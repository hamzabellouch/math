import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds
import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

/-! The normalized target and error in successive primitive mean steps.
The target is defined from the actual old mean metric; its next defect is
exactly the rescaled error of the constructed increment. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open WeightedEstimates PhaseMean

def normalizedMeanDefect (δ : ℝ) (γ P : SmallModes.Base → Tensor) :
    SmallModes.Base → Tensor := fun x => (δ^2)⁻¹ • (γ x-P x)-γ x

def primitiveMeanTarget (δ δ' : ℝ) (γ P : SmallModes.Base → Tensor) :
    SmallModes.Base → Tensor := fun x => (δ^2)⁻¹ • (γ x-P x-δ'^2 • γ x)

lemma primitiveMeanTarget_eq (δ δ' : ℝ) (γ P : SmallModes.Base → Tensor) :
    primitiveMeanTarget δ δ' γ P = fun x =>
      γ x + normalizedMeanDefect δ γ P x - (δ'^2 / δ^2) • γ x := by
  ext x k
  simp only [primitiveMeanTarget,normalizedMeanDefect,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul]
  ring

lemma primitiveMeanTarget_smooth {δ δ' : ℝ} {γ P : SmallModes.Base → Tensor}
    (hγ : ContDiff ℝ ∞ γ) (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (primitiveMeanTarget δ δ' γ P) :=
  ((hγ.sub hP).sub (hγ.const_smul (δ'^2))).const_smul _

lemma normalizedMeanDefect_smooth {δ : ℝ} {γ P : SmallModes.Base → Tensor}
    (hγ : ContDiff ℝ ∞ γ) (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (normalizedMeanDefect δ γ P) :=
  ((hγ.sub hP).const_smul _).sub hγ

lemma primitiveMeanTarget_identity {δ δ' : ℝ} (hδ : δ ≠ 0)
    (γ P : SmallModes.Base → Tensor) :
    (δ^2 : ℝ) • primitiveMeanTarget δ δ' γ P = γ-P-(δ'^2 : ℝ) • γ := by
  ext x k
  simp only [primitiveMeanTarget,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  field_simp

lemma primitiveMeanTarget_distance {δ δ' : ℝ} {γ P : SmallModes.Base → Tensor}
    {x : SmallModes.Base} {a b : ℝ}
    (hD : ‖normalizedMeanDefect δ γ P x‖ ≤ a) (hγ : ‖γ x‖ ≤ b) :
    ‖primitiveMeanTarget δ δ' γ P x - γ x‖ ≤ a + (δ'^2 / δ^2) * b := by
  have hid : primitiveMeanTarget δ δ' γ P x - γ x =
      normalizedMeanDefect δ γ P x - (δ'^2 / δ^2) • γ x := by
    rw [primitiveMeanTarget_eq]
    ext k
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hid]
  calc
    _ ≤ ‖normalizedMeanDefect δ γ P x‖ + ‖(δ'^2 / δ^2) • γ x‖ := norm_sub_le _ _
    _ = ‖normalizedMeanDefect δ γ P x‖ + (δ'^2 / δ^2) * ‖γ x‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg δ') (sq_nonneg δ))]
    _ ≤ _ := add_le_add hD (mul_le_mul_of_nonneg_left hγ
      (div_nonneg (sq_nonneg δ') (sq_nonneg δ)))

lemma primitiveMeanTarget_bound {U : Set SmallModes.Base} (hU : IsOpen U)
    {γ P : SmallModes.Base → Tensor} (hγ : ContDiff ℝ ∞ γ) (hP : ContDiff ℝ ∞ P)
    {δ δ' s A B : ℝ} {m : ℕ} (hδ : 0 < δ) (hδ' : 0 ≤ δ') (hδδ : δ' ≤ δ)
    (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hγb : WeightedBound U s m A γ)
    (hDb : WeightedBound U s m B (normalizedMeanDefect δ γ P)) :
    WeightedBound U s m (2*A+B) (primitiveMeanTarget δ δ' γ P) := by
  have hr : 0 ≤ δ'^2 / δ^2 := div_nonneg (sq_nonneg δ') (sq_nonneg δ)
  have hr1 : δ'^2 / δ^2 ≤ 1 := (div_le_one (sq_pos_of_pos hδ)).2 (by nlinarith)
  have hscaled := hγb.const_smul hU.uniqueDiffOn hγ.contDiffOn (δ'^2 / δ^2)
  have hscaled' : WeightedBound U s m A (fun x => (δ'^2 / δ^2) • γ x) := by
    apply hscaled.mono_const
    rw [abs_of_nonneg hr]
    exact mul_le_of_le_one_left hA hr1
  have hD := normalizedMeanDefect_smooth (δ := δ) hγ hP
  have hb := (hγb.add hU.uniqueDiffOn hs hγ.contDiffOn hD.contDiffOn hDb).sub
    hU.uniqueDiffOn hs (hγ.add hD).contDiffOn (hγ.const_smul _).contDiffOn hscaled'
  have he : A+B+A = 2*A+B := by ring
  rw [he] at hb
  exact hb.congr (fun x _ => congrFun (primitiveMeanTarget_eq δ δ' γ P) x)

lemma normalizedMeanDefect_after_step {U : Set SmallModes.Base} (hU : IsOpen U)
    {γ P Q : SmallModes.Base → Tensor} (hγ : ContDiff ℝ ∞ γ)
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    {δ δ' s C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    (hb : WeightedBound U s m C (Q-P-(δ^2 : ℝ) • primitiveMeanTarget δ δ' γ P)) :
    WeightedBound U s m (C / δ'^2) (normalizedMeanDefect δ' γ Q) := by
  have hT := primitiveMeanTarget_smooth (δ := δ) (δ' := δ') hγ hP
  have hsmooth : ContDiff ℝ ∞ (Q-P-(δ^2 : ℝ) • primitiveMeanTarget δ δ' γ P) :=
    (hQ.sub hP).sub (by
      change ContDiff ℝ ∞ (fun x => (δ^2 : ℝ) • primitiveMeanTarget δ δ' γ P x)
      exact hT.const_smul _)
  have hh := hb.const_smul hU.uniqueDiffOn hsmooth.contDiffOn (-(δ'^2)⁻¹)
  have hc : |-(δ'^2)⁻¹| * C = C/δ'^2 := by
    rw [abs_neg,abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hδ'))]
    ring
  rw [hc] at hh
  apply hh.congr
  intro x _
  ext k
  simp only [normalizedMeanDefect,primitiveMeanTarget,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  field_simp
  ring

/-- A cutoff extension of the target gives the same next defect wherever
it agrees with the actual primitive mean target. -/
lemma normalizedMeanDefect_after_local_step {U : Set SmallModes.Base} (hU : IsOpen U)
    {γ P Q H : SmallModes.Base → Tensor} (hγ : ContDiff ℝ ∞ γ)
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    {δ δ' s C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    (hH : ∀ x ∈ U, H x = primitiveMeanTarget δ δ' γ P x)
    (hb : WeightedBound U s m C (Q-P-(δ^2 : ℝ) • H)) :
    WeightedBound U s m (C / δ'^2) (normalizedMeanDefect δ' γ Q) := by
  apply normalizedMeanDefect_after_step hU hγ hP hQ hδ hδ'
  exact hb.congr (fun x hx => by simp only [Pi.sub_apply,Pi.smul_apply,hH x hx])

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
