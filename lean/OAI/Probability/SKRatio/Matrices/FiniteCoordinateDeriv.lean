import Mathlib
import OAI.Probability.SKRatio.Matrices.CoordinateDeriv

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKRatioGaussian
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def finiteCoordinateDeriv (i : κ) (f : (κ → ℝ) → ℝ) (x : κ → ℝ) : ℝ :=
  deriv (fun z => f (Function.update x i z)) (x i)

lemma lipschitz_coordinate_update (i : κ) (x : κ → ℝ) :
    LipschitzWith 1 (fun z : ℝ => Function.update x i z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).2
  intro k
  by_cases h : k = i
  · subst k; simp
  · simp only [Function.update_of_ne h,dist_self]; exact dist_nonneg

lemma measurable_finiteCoordinateDeriv (i : κ) {f : (κ → ℝ) → ℝ}
    (hf : Continuous f) : Measurable (finiteCoordinateDeriv i f) := by
  have h := measurable_deriv_with_param (f := fun x z => f (Function.update x i z))
    (hf.comp (continuous_update i))
  exact h.comp ((continuous_id.prodMk (continuous_apply i)).measurable)

lemma norm_finiteCoordinateDeriv_le (i : κ) {f : (κ → ℝ) → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (x : κ → ℝ) :
    ‖finiteCoordinateDeriv i f x‖ ≤ L := by
  simpa only [finiteCoordinateDeriv,Function.comp_def,mul_one] using
    norm_deriv_le_of_lipschitz (hf.comp (lipschitz_coordinate_update i x)) (x₀ := x i)

lemma gaussianFinite_lipschitz_IBP_equiv {n : ℕ} (e : Fin (n+1) ≃ κ) (i : κ)
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ x, finiteCoordinateDeriv i f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  have he (x : Fin (n+1) → ℝ) (k : κ) : E x k = x (e.symm k) := by
    simp [E,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have hl : LipschitzWith 1 E := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul]
    apply (dist_pi_le_iff dist_nonneg).2
    intro k
    simpa only [he] using dist_le_pi_dist x y (e.symm k)
  have hp := measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e
  have hh := gaussianProduct_lipschitz_IBP (e.symm i)
    (by simpa only [mul_one,Function.comp_def] using hf.comp hl) (fun x => hC (E x))
  have hu (x : Fin (n+1) → ℝ) (z : ℝ) :
      E ((e.symm i).insertNth z ((e.symm i).removeNth x)) =
        Function.update (E x) i z := by
    rw [Fin.insertNth_removeNth]
    ext k
    simp only [he]
    by_cases h : k = i
    · subst k; simp
    · simp [he,Function.update_of_ne h,show e.symm k ≠ e.symm i from fun h' => h (e.symm.injective h')]
  have hd (x : Fin (n+1) → ℝ) :
      coordinateDeriv (e.symm i) (f ∘ E) x = finiteCoordinateDeriv i f (E x) := by
    simp only [coordinateDeriv,finiteCoordinateDeriv,Function.comp_def,hu,he]
  rw [← hp.integral_comp' (fun x => x i*f x),
    ← hp.integral_comp' (finiteCoordinateDeriv i f)]
  change (∫ x, E x i*f (E x) ∂standardGaussianProduct (n+1)) =
    ∫ x, finiteCoordinateDeriv i f (E x) ∂standardGaussianProduct (n+1)
  simpa only [← hd,he,Function.comp_def] using hh

theorem gaussianFinite_lipschitz_IBP (i : κ)
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ x, finiteCoordinateDeriv i f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  have hn : Fintype.card κ ≠ 0 := by
    let : Nonempty κ := ⟨i⟩
    exact Fintype.card_ne_zero
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let e : κ ≃ Fin (n+1) := (Fintype.equivFin κ).trans (Equiv.cast (congrArg Fin hn))
  exact gaussianFinite_lipschitz_IBP_equiv e.symm i hf hC

end SKRatioGaussian

end
end
end

end OAI
