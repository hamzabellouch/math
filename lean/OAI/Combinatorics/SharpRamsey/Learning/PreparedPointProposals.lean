import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestRowSize
import OAI.Combinatorics.SharpRamsey.Learning.PreparedProposals
import OAI.Combinatorics.SharpRamsey.Learning.PoissonSupport

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
noncomputable section
variable {A : Type*} [Fintype A]
local instance flat_JoinedPreparedPointProposals_1 (R : ℕ) : DecidableEq (Fin R×A) := Classical.decEq _

omit [Fintype A] in

theorem total_cutoff_intersection (S : Finset A) (R M : ℕ) (γ : ℝ≥0)
    (P : Set (Schedule S R)) (hM : 2*((R:ℝ)*S.card*γ)≤M) :
    (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real P-
      Real.exp (-((R:ℝ)*S.card*γ)/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real
        {ω | (∑ i,ω i)≤M ∧ ω∈P} := by
  let μ := PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)
  have ht := PoissonTail.total_tail (fun _ : Fin R×S => γ)
  rw [constant_mean S R γ] at ht
  have hbad : μ.real {ω | M<∑ i,ω i}≤Real.exp (-((R:ℝ)*S.card*γ)/3) := by
    apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) ht
    intro ω hω
    exact hM.trans (by exact_mod_cast hω.le)
  have hs : P⊆{ω | (∑ i,ω i)≤M ∧ ω∈P}∪{ω | M<∑ i,ω i} := by
    intro ω hω
    by_cases hc : (∑ i,ω i)≤M
    · exact Or.inl ⟨hc,hω⟩
    · exact Or.inr (Nat.lt_of_not_ge hc)
  have hu := (measureReal_mono (μ:=μ) (h₂:=measure_ne_top _ _) hs).trans
    (measureReal_union_le _ _)
  linarith

def ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) : Fin R×A → ℕ :=
  fun rx => extend S ω rx.1 rx.2

def coordinateSupport (S : Finset A) (R : ℕ) : Finset (Fin R×A) := univ ×ˢ S

def ambientRate (S : Finset A) (R : ℕ) (γ : ℝ≥0) (rx : Fin R×A) : ℝ≥0 :=
  if rx.2∈S then γ else 0

omit [Fintype A] in
lemma ambientCounts_restrict (S : Finset A) {R : ℕ} (z : Fin R×A → ℕ)
    (hz : ∀ rx,rx.2∉S → z rx=0) :
    ambientCounts S (fun rx : Fin R×S => z (rx.1,rx.2))=z := by
  funext rx
  by_cases hx : rx.2∈S
  · simp [ambientCounts,extend,hx]
  · simp [ambientCounts,extend,hx,hz rx hx]

omit [Fintype A] in
lemma restrict_ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    (fun rx : Fin R×S => ambientCounts S ω (rx.1,rx.2))=ω := by
  funext rx
  simp [ambientCounts,extend,rx.2.2]

theorem ambientCounts_hasLaw (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    HasLaw (ambientCounts S) (PoissonSchedules.scheduleLaw (ambientRate S R γ))
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton z)]
  by_cases hz : ∀ rx,rx.2∉S → z rx=0
  · have he : ambientCounts S ⁻¹' {z}={fun rx : Fin R×S => z (rx.1,rx.2)} := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      constructor
      · intro h
        calc
          ω = fun rx : Fin R×S => ambientCounts S ω (rx.1,rx.2) := (restrict_ambientCounts S ω).symm
          _ = _ := by rw [h]
      · rintro rfl
        exact ambientCounts_restrict S z hz
    rw [he,PoissonSchedules.scheduleLaw,PoissonSchedules.scheduleLaw,
      Measure.pi_singleton,Measure.pi_singleton,Fintype.prod_prod_type,Fintype.prod_prod_type]
    apply prod_congr rfl
    intro r _
    calc
      _ = ∏ x∈S,poissonMeasure γ {z (r,x)} := prod_coe_sort S _
      _ = ∏ x∈S,poissonMeasure (ambientRate S R γ (r,x)) {z (r,x)} := by
        apply prod_congr rfl
        intro x hx
        rw [ambientRate,ite_eq_left hx]
      _ = _ := prod_subset (subset_univ S) (fun x _ hx => by
        simp only [ambientRate,ite_eq_right hx,hz (r,x) hx,poissonMeasure_singleton]
        norm_num)
  · obtain ⟨rx,hx,hn⟩ := not_forall.mp hz |>.imp (fun rx h => by simpa using h)
    have he : ambientCounts S ⁻¹' {z}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hh := congrFun (Set.mem_singleton_iff.mp hω) rx
      exact hn (by simpa [ambientCounts,extend,hx] using hh.symm)
    rw [he,measure_empty,PoissonSchedules.scheduleLaw,Measure.pi_singleton]
    symm
    apply prod_eq_zero (mem_univ rx)
    simp [ambientRate,hx,poissonMeasure_singleton,hn]

lemma sum_ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    (∑ rx,ambientCounts S ω rx)=∑ rx,ω rx := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  change (∑ x,PoissonSupport.extend S (fun x => ω (r,x)) x)=_
  exact PoissonSupport.sum_extend S _

omit [Fintype A] in
lemma ambient_rate_uniform (S : Finset A) (hS : S.Nonempty) (R : ℕ) (hR : 0<R)
    (γ : ℝ≥0) :
    PoissonLikelihood.uniformRate (coordinateSupport S R) ((R:ℝ≥0)*S.card*γ)=
      ambientRate S R γ := by
  funext rx
  simp only [PoissonLikelihood.uniformRate,coordinateSupport,mem_product,mem_univ,true_and,
    card_product,card_univ,Fintype.card_fin,ambientRate]
  by_cases hx : rx.2∈S
  · simp only [ite_eq_left hx,Nat.cast_mul]
    have hr : (R:ℝ≥0)≠0 := by exact_mod_cast hR.ne'
    have hs : (S.card:ℝ≥0)≠0 := by exact_mod_cast (card_pos.mpr hS).ne'
    field_simp
  · simp only [ite_eq_right hx]

theorem ambient_proposal_success (S U : Finset A) (hS : S.Nonempty) (hSU : S⊆U)
    (R M : ℕ) (hR : 0<R) (γ : ℝ≥0) (P : (Fin R×A→ℕ)→Prop) :
    ((S.card:ℝ)/(U.card:ℝ))^M *
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real
        {ω | (∑ i,ω i)≤M ∧ P (ambientCounts S ω)} ≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*γ) M)
        (PreparedProposals.accepts (coordinateSupport S R) M P) := by
  have hu : U.Nonempty := hS.mono hSU
  have hcS : (coordinateSupport S R).Nonempty := by
    exact Finset.Nonempty.product (by exact ⟨⟨0,hR⟩,mem_univ _⟩) hS
  have hcU : (coordinateSupport U R).Nonempty := hcS.mono (product_subset_product_right hSU)
  have hcSU : coordinateSupport S R⊆coordinateSupport U R := product_subset_product_right hSU
  have hh := PreparedProposals.proposal_success (coordinateSupport S R) (coordinateSupport U R)
    ((R:ℝ≥0)*S.card*γ) M hcS hcU hcSU P
  rw [PreparedProposals.true_success_probability,ambient_rate_uniform S hS R hR γ] at hh
  have he : ((coordinateSupport S R).card:ℝ)/((coordinateSupport U R).card:ℝ)=
      (S.card:ℝ)/(U.card:ℝ) := by
    simp only [coordinateSupport,card_product,card_univ,Fintype.card_fin,Nat.cast_mul]
    have hr : (R:ℝ)≠0 := by exact_mod_cast hR.ne'
    field_simp
  rw [he] at hh
  have hlaw := ambientCounts_hasLaw S R γ
  have hm := congrArg (fun μ : Measure (Fin R×A→ℕ) =>
    μ.real {z | FiniteSchedules.total z≤M ∧ P z}) hlaw.map_eq
  rw [map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)] at hm
  have hp : ambientCounts S ⁻¹' {z | FiniteSchedules.total z≤M ∧ P z}=
      {ω | (∑ i,ω i)≤M ∧ P (ambientCounts S ω)} := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,FiniteSchedules.total,sum_ambientCounts]
  rw [hp] at hm
  exact hm.symm ▸ hh

end
end SharpLogRamsey.PreparedRow

end

end OAI
