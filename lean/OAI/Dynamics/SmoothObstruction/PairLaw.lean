import Mathlib

namespace OAI

section

open scoped Classical
open Finset

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset
open scoped ENNReal
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable abbrev cell (μ : Measure X) (P : X → α) (a : α) : Measure X :=
  μ.restrict (P ⁻¹' {a})

/-- The manuscript's original, unnormalized-on-retained-pairs law. All
zero-mass cells contribute zero; no conditional renormalization is used. -/
noncomputable def law (μ : Measure X) (P : X → α) : Measure (X × X) :=
  ∑ a, (μ (P ⁻¹' {a}))⁻¹ • (cell μ P a).prod (cell μ P a)

lemma sum_cells (μ : Measure X) (P : X → α) (hP : Measurable P) :
    ∑ a,cell μ P a=μ := by
  have hd : Pairwise (fun a b => Disjoint (P ⁻¹' {a}) (P ⁻¹' {b})) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    exact hab ((Set.mem_singleton_iff.mp hxa).symm.trans (Set.mem_singleton_iff.mp hxb))
  have hu : (⋃ a,P ⁻¹' {a})=univ := by ext x; simp
  have hh := Measure.restrict_iUnion (μ:=μ) hd (fun a => hP (measurableSet_singleton a))
  rw [hu,Measure.restrict_univ,Measure.sum_fintype] at hh
  exact hh.symm

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma normalized_cell (μ : Measure X) [IsFiniteMeasure μ] (P : X → α) (a : α) :
    ((μ (P ⁻¹' {a}))⁻¹ * (cell μ P a) univ) • cell μ P a=cell μ P a := by
  rw [cell,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  by_cases hz : μ (P ⁻¹' {a})=0
  · rw [Measure.restrict_eq_zero.mpr hz,smul_zero]
  · rw [ENNReal.inv_mul_cancel hz (measure_ne_top _ _),one_smul]

lemma first_marginal (μ : Measure X) [IsFiniteMeasure μ] (P : X → α) (hP : Measurable P) :
    (law μ P).map Prod.fst=μ := by
  rw [law,←Measure.mapₗ_apply_of_measurable measurable_fst,map_sum]
  simp only [Measure.mapₗ_apply_of_measurable measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_fst_prod,smul_smul,normalized_cell]
  exact sum_cells μ P hP

lemma second_marginal (μ : Measure X) [IsFiniteMeasure μ] (P : X → α) (hP : Measurable P) :
    (law μ P).map Prod.snd=μ := by
  rw [law,←Measure.mapₗ_apply_of_measurable measurable_snd,map_sum]
  simp only [Measure.mapₗ_apply_of_measurable measurable_snd,
    Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_snd_prod,smul_smul,normalized_cell]
  exact sum_cells μ P hP

theorem law_probability (μ : Measure X) [IsProbabilityMeasure μ] (P : X → α)
    (hP : Measurable P) : IsProbabilityMeasure (law μ P) := by
  apply isProbabilityMeasure_iff.mpr
  have hh := congrArg (fun ν : Measure X => ν univ) (first_marginal μ P hP)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using hh

lemma bad_pair_bound (μ : Measure X) [IsProbabilityMeasure μ] (P : X → α) (hP : Measurable P)
    (R : Set X) (hR : MeasurableSet R) :
    law μ P (R ×ˢ R)ᶜ ≤ 2*μ Rᶜ := by
  have he : (R ×ˢ R)ᶜ=(Prod.fst ⁻¹' Rᶜ)∪(Prod.snd ⁻¹' Rᶜ) := by
    ext z; simp only [mem_compl_iff,mem_prod,mem_union,Set.mem_preimage]; tauto
  rw [he]
  have hf := congrArg (fun ν : Measure X => ν Rᶜ) (first_marginal μ P hP)
  have hs := congrArg (fun ν : Measure X => ν Rᶜ) (second_marginal μ P hP)
  rw [Measure.map_apply measurable_fst hR.compl] at hf
  rw [Measure.map_apply measurable_snd hR.compl] at hs
  exact (measure_union_le _ _).trans (by rw [hf,hs,two_mul])

end SmoothObstruction.PairLaw

end

section

namespace SmoothObstruction
open MeasureTheory Filter Topology Set
open scoped ENNReal
/-- A finite original cell-weighted pair law and its measurable switch.
The carrier is not normalized and no sigma-algebra on the retained subtype
is silently substituted for the ambient original pair law. -/
structure SwitchData {M : Type} [MeasurableSpace M] (μ : Measure M) where
  J : Type
  fin : Fintype J
  meas : MeasurableSpace J
  singletons : MeasurableSingletonClass J
  label : M → J
  carrier : Set (M×M)
  point : M×M → M
  label_measurable : Measurable label
  carrier_measurable : MeasurableSet carrier
  point_measurable : Measurable point
attribute [instance] SwitchData.fin SwitchData.meas SwitchData.singletons
namespace SwitchData
variable {M : Type} [MeasurableSpace M] {μ : Measure M}
noncomputable def law (D : SwitchData μ) : Measure (M×M) := PairLaw.law μ D.label
noncomputable def retained (D : SwitchData μ) : Measure (M×M) := D.law.restrict D.carrier
def Good (D : SwitchData μ) (η C B : ℝ) (n : ℕ) : Prop :=
  (Fintype.card D.J : ℝ)≤Real.exp (C*B*n) ∧ 1-η≤D.law.real D.carrier ∧
    D.retained.map D.point≤(2:ℝ≥0∞) • μ
end SwitchData
/-- The literal quantitative smooth switching property, with one fixed
sequence of original finite cell laws, summable sixteenth powers, and
uniform two-sided shadowing over the full dyadic windows. -/
def SmoothSwitching {M : Type} [MetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (S Sinv : M → M) : Prop :=
  ∀ η : ℝ,0<η → ∃ (B : ℕ → ℝ) (C : ℝ) (D : ℕ → SwitchData μ),
    (∀ k,0<B k) ∧ Summable (fun k => (B k)^16) ∧
    (∀ᶠ k in atTop,(D k).Good η C (B k) (2^k)) ∧
    ∀ ε : ℝ,0<ε → ∀ᶠ k in atTop,∀ u∈(D k).carrier,∀ t v : Fin (2^k+1),
      dist (S^[t.val] ((D k).point u)) (S^[t.val] u.1)+
      dist (Sinv^[v.val] ((D k).point u)) (Sinv^[v.val] u.2)<ε
end SmoothObstruction

end

end OAI
