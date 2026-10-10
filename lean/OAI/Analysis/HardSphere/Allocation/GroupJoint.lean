import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
attribute [local instance] Classical.propDecidable

lemma certified_allocated_joint {W Z V : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    [Fintype V] [DecidableEq V] (μ : Measure W) [SFinite μ] (κ : Kernel W Z) [IsSFiniteKernel κ]
    (cert : V→W→Prop) (bad : V→W×Z→Prop)
    (hcert : ∀v,MeasurableSet {w | cert v w}) (hbad : ∀v,MeasurableSet {p | bad v p})
    (p q : ℝ≥0∞)
    (hjoint : ∀S : Finset V,μ {w | ∀v∈S,¬cert v w}≤p^S.card)
    (hcond : ∀w,∀T : Finset V,(∀v∈T,cert v w)→κ w {z | ∀v∈T,bad v (w,z)}≤q^T.card)
    (A : Finset V) :
    μ.compProd κ {wz | ∀v∈A,¬cert v wz.1 ∨ bad v wz}≤(p+q)^A.card := by
  let F : Finset V→Set (W×Z) := fun S ↦ {wz | (∀v∈S,¬cert v wz.1) ∧
    ∀v∈A\S,cert v wz.1 ∧ bad v wz}
  have hF (S : Finset V) : MeasurableSet (F S) := by
    have h₁ : MeasurableSet {p : W×Z | ∀v∈S,¬cert v p.1} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun v ↦ MeasurableSet.iInter (fun _ ↦ (hcert v).compl.preimage measurable_fst))
    have h₂ : MeasurableSet {p : W×Z | ∀v∈A\S,cert v p.1 ∧ bad v p} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun v ↦ MeasurableSet.iInter (fun _ ↦ ((hcert v).preimage measurable_fst).inter (hbad v)))
    exact h₁.inter h₂
  have hsub : {wz : W×Z | ∀v∈A,¬cert v wz.1 ∨ bad v wz}⊆⋃S∈A.powerset,F S := by
    intro wz hwz
    let S := A.filter (fun v ↦ ¬cert v wz.1)
    refine mem_iUnion.mpr ⟨S,mem_iUnion.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),?_⟩⟩
    constructor
    · exact fun v hv ↦ (Finset.mem_filter.mp hv).2
    · intro v hv
      obtain ⟨hvA,hvS⟩ := Finset.mem_sdiff.mp hv
      have hc : cert v wz.1 := by
        by_contra hn
        exact hvS (Finset.mem_filter.mpr ⟨hvA,hn⟩)
      exact ⟨hc,(hwz v hvA).resolve_left (not_not.mpr hc)⟩
  have hbound (S : Finset V) : μ.compProd κ (F S)≤p^S.card*q^(A\S).card := by
    rw [Measure.compProd_apply (hF S)]
    let C : Set W := {w | ∀v∈S,¬cert v w}
    have hC : MeasurableSet C := by
      simp only [C,ofPred_forall]
      exact MeasurableSet.iInter (fun v ↦ MeasurableSet.iInter (fun _ ↦ (hcert v).compl))
    calc
      _ ≤ ∫⁻w,C.indicator (fun _ ↦ q^(A\S).card) w ∂μ := by
        apply lintegral_mono
        intro w
        change κ w {z | (w,z)∈F S} ≤ _
        by_cases hc : w∈C
        · rw [Set.indicator_of_mem hc]
          by_cases hT : ∀v∈A\S,cert v w
          · apply (measure_mono (show {z | (w,z)∈F S}⊆{z | ∀v∈A\S,bad v (w,z)} from fun z hz v hv ↦ (hz.2 v hv).2)).trans
            exact hcond w (A\S) hT
          · have he : {z | (w,z)∈F S}=∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro z hz
              exact hT (fun v hv ↦ (hz.2 v hv).1)
            rw [he,measure_empty]
            exact bot_le
        · rw [Set.indicator_of_notMem hc]
          have he : {z | (w,z)∈F S}=∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            exact hc hz.1
          rw [he,measure_empty]
      _ = q^(A\S).card*μ C := by rw [lintegral_indicator hC]; simp
      _ ≤ q^(A\S).card*p^S.card := mul_le_mul_right (hjoint S) _
      _ = _ := mul_comm _ _
  calc
    _ ≤ μ.compProd κ (⋃S∈A.powerset,F S) := measure_mono hsub
    _ ≤ ∑S∈A.powerset,μ.compProd κ (F S) := measure_biUnion_finset_le _ _
    _ ≤ ∑S∈A.powerset,p^S.card*q^(A\S).card := Finset.sum_le_sum (fun S _ ↦ hbound S)
    _ = _ := by
      calc
        _ = ∑S∈A.powerset,p^S.card*q^(A.card-S.card) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hS)]
        _ = _ := Finset.sum_pow_mul_eq_add_pow p q A

end HardSphere.Groups

end

noncomputable section
open scoped BigOperators
namespace HardSphere.Groups

def groupCount (ell D : ℝ) (M : ℕ) : ℕ := ⌊ell*D/(4*(M:ℝ))⌋₊

lemma groupCount_allocation {ell D : ℝ} {M m : ℕ}
    (hell : 0≤ell) (hD : 0≤D) (hM : 0<M) (hm : ell*D/2 ≤ (m:ℝ)) :
    M*groupCount ell D M ≤ m := by
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hfloor := Nat.floor_le (show 0≤ell*D/(4*(M:ℝ)) by positivity)
  have hh : (M:ℝ)*(groupCount ell D M:ℝ) ≤ ell*D/4 := by
    unfold groupCount
    calc
      _ ≤ (M:ℝ)*(ell*D/(4*(M:ℝ))) := mul_le_mul_of_nonneg_left hfloor hMp.le
      _ = ell*D/4 := by field_simp
  have hm' : ell*D/4≤(m:ℝ) := by nlinarith [mul_nonneg hell hD]
  have h := hh.trans hm'
  exact_mod_cast h

lemma groupCount_ratio {ell D : ℝ} {M : ℕ}
    (hell : 0<ell) (hD : 0<D) (hM : 0<M)
    (hlarge : 2≤ell*D/(4*(M:ℝ))) :
    ell/(8*(M:ℝ)) ≤ (groupCount ell D M:ℝ)/D := by
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hfloor : ell*D/(4*(M:ℝ)) < (⌊ell*D/(4*(M:ℝ))⌋₊:ℝ)+1 := by
    have hnonneg := div_nonneg (mul_nonneg hell.le hD.le)
      (mul_nonneg (by norm_num : (0:ℝ)≤4) hMp.le)
    exact_mod_cast (Nat.floor_lt hnonneg).mp (Nat.lt_succ_self _)
  have hh : ell*D/(8*(M:ℝ)) ≤ (groupCount ell D M:ℝ) := by
    unfold groupCount
    have he : ell*D/(4*(M:ℝ))=2*(ell*D/(8*(M:ℝ))) := by ring
    rw [he] at hlarge hfloor

    have he' : ⌊2*(ell*D/(8*(M:ℝ)))⌋₊=⌊ell*D/(4*(M:ℝ))⌋₊ := by rw [←he]
    rw [he'] at hfloor
    linarith
  apply (le_div_iff₀ hD).mpr
  have he : (ell/(8*(M:ℝ)))*D=ell*D/(8*(M:ℝ)) := by ring
  rw [he]
  exact hh

end HardSphere.Groups

end

end OAI
