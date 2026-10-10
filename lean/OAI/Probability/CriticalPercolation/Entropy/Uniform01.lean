import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.Priority

noncomputable def uniform01 : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure uniform01 := by
  constructor
  simp [uniform01, Real.volume_Icc]

variable {I : Type*} [Fintype I]

noncomputable def law : Measure (I → ℝ) := Measure.pi fun _ => uniform01

instance : IsProbabilityMeasure (law (I := I)) := by
  unfold law
  infer_instance

noncomputable def split (i : I) : (I → ℝ) ≃ᵐ (ℝ × ({j : I // j ≠ i} → ℝ)) where
  toEquiv := Equiv.funSplitAt i ℝ
  measurable_toFun := (measurable_pi_apply i).prodMk
    (Measurable.of_eval (fun coordinate => measurable_pi_apply coordinate.val))
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    by_cases h : j = i
    · subst j
      simpa [Equiv.funSplitAt, Equiv.piSplitAt] using measurable_fst
    · simpa [Equiv.funSplitAt, Equiv.piSplitAt, h, Function.comp_def] using
        (measurable_pi_apply (⟨j,h⟩ : {j : I // j ≠ i})).comp measurable_snd

omit [Fintype I] in
lemma split_apply (i : I) (u : I → ℝ) : split i u = (u i, fun j : {j : I // j ≠ i} => u j.val) := rfl

omit [Fintype I] in
lemma split_symm_apply (i j : I) (u : ℝ × ({j : I // j ≠ i} → ℝ)) :
    (split i).symm u j = if h : j = i then u.1 else u.2 ⟨j,h⟩ := by
  simp only [split, MeasurableEquiv.symm_mk, Equiv.funSplitAt, Equiv.piSplitAt,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk]
  split_ifs with h
  · subst j; rfl
  · rfl

lemma split_preserving (i : I) : MeasurePreserving (split i) law
    (uniform01.prod (law (I := {j : I // j ≠ i}))) := by
  apply MeasurePreserving.symm (split i).symm
  refine ⟨(split i).symm.measurable, ?_⟩
  unfold law
  refine (Measure.pi_eq fun s _ => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have he : (split i).symm ⁻¹' (Set.univ.pi s) =
      s i ×ˢ (Set.univ.pi fun j : {j : I // j ≠ i} => s j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h
      constructor
      · simpa [split_symm_apply] using h i
      · intro j; simpa [split_symm_apply, j.property] using h j
    · rintro ⟨h₁,h₂⟩ j
      by_cases h : j = i
      · subst j; simpa [split_symm_apply] using h₁
      · simpa [split_symm_apply, h] using h₂ ⟨j,h⟩
  rw [he, Measure.prod_prod, Measure.pi_pi]
  have hprod := Fintype.prod_subtype_mul_prod_subtype (fun j : I => j = i)
    (fun j => uniform01 (s j))
  simpa only [Fintype.prod_unique, (default : {j : I // j = i}).property] using hprod

lemma uniform01_Ioi {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    uniform01 (Ioi t) = ENNReal.ofReal (1-t) := by
  rw [uniform01, Measure.restrict_apply measurableSet_Ioi]
  have he : Ioi t ∩ Icc (0:ℝ) 1 = Ioc t 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · intro h; exact ⟨h.1,h.2.2⟩
    · intro h; exact ⟨h.1, ht.1.trans h.1.le, h.2⟩
  rw [he, Real.volume_Ioc]

lemma integral_survival (S : Finset I) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (∫ u : I → ℝ, if ∀ j ∈ S, t < u j then (1:ℝ) else 0 ∂law) = (1-t)^S.card := by
  have he : {u : I → ℝ | ∀ j ∈ S, t < u j} =
      Set.univ.pi (fun j => if j ∈ S then Ioi t else Set.univ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h j; split_ifs with hj
      · exact h j hj
      · trivial
    · intro h j hj; simpa [hj] using h j
  have hf : (fun u : I → ℝ => if ∀ j ∈ S, t < u j then (1:ℝ) else 0) =
      ({u : I → ℝ | ∀ j ∈ S, t < u j}).indicator (fun _ => (1:ℝ)) := by
    funext u
    simp [Set.indicator]
  rw [hf]
  rw [integral_indicator]
  · rw [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
      he, law, Measure.pi_pi]
    simp only [apply_ite, uniform01_Ioi ht, measure_univ, ENNReal.toReal_prod,
      apply_ite, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2), ENNReal.toReal_one]
    rw [Finset.prod_ite_mem Finset.univ S (fun _ => 1-t)]
    simp
  · rw [he]
    exact MeasurableSet.univ_pi fun j => by split_ifs <;> measurability

end CriticalPercolation.Priority
open Set MeasureTheory Real
open scoped Interval

end
end

end OAI
