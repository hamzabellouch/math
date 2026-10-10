import OAI.Geometry.Arnold.Sphere

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample
namespace ThreePoints

open scoped Matrix

def ambientHessian : Pair →L[ℝ] Pair →L[ℝ] ℝ :=
  (secondCoord 0).smulRight (firstCoord 0) +
  (secondCoord 1).smulRight (firstCoord 1) +
  (secondCoord 2).smulRight (firstCoord 2) +
  (firstCoord 0).smulRight (secondCoord 0) +
  (firstCoord 1).smulRight (secondCoord 1) +
  (firstCoord 2).smulRight (secondCoord 2)

lemma ambientHessian_apply (r s : Pair) : ambientHessian r s =
    r.2 ⬝ᵥ s.1 + r.1 ⬝ᵥ s.2 := by
  simp [ambientHessian, firstCoord, secondCoord, dotProduct, Fin.sum_univ_succ]
  ring

lemma df_eq_affine : df = fun q ↦ (firstCoord 0 - secondCoord 2) + ambientHessian q := by
  funext q
  apply ContinuousLinearMap.ext
  intro r
  simp [df, ambientHessian, firstCoord, secondCoord]
  ring

lemma df_hasFDerivAt (q : Pair) : HasFDerivAt df ambientHessian q := by
  rw [df_eq_affine]
  convert! (hasFDerivAt_const (firstCoord 0 - secondCoord 2) q).add
    ambientHessian.hasFDerivAt using 1
  simp only [zero_add]

lemma f_secondFDeriv (q : Pair) :
    fderiv ℝ (fderiv ℝ f) q = ambientHessian := by
  have hf : fderiv ℝ f = df := funext fun x ↦ (f_hasFDerivAt x).fderiv
  rw [hf]
  exact (df_hasFDerivAt q).fderiv

lemma df_qzero : df qzero = 0 := by
  apply ContinuousLinearMap.ext
  intro r
  simp [df, qzero, pole, east, Matrix.cons_val_two]

/-- The full tangent in the two ambient factors. -/
def IsTangent (q r : Pair) : Prop := q.1 ⬝ᵥ r.1 = 0 ∧ q.2 ⬝ᵥ r.2 = 0

lemma tangent_qzero_iff (r : Pair) : IsTangent qzero r ↔ r.1 2 = 0 ∧ r.2 0 = 0 := by
  simp [IsTangent, qzero, pole, east, dotProduct, Fin.sum_univ_succ]

lemma ambientHessian_at_qzero_on_tangent (r s : Pair)
    (hr : IsTangent qzero r) (hs : IsTangent qzero s) :
    fderiv ℝ (fderiv ℝ f) qzero r s = r.1 1 * s.2 1 + r.2 1 * s.1 1 := by
  obtain ⟨hr₂, hr₀⟩ := (tangent_qzero_iff r).mp hr
  obtain ⟨hs₂, hs₀⟩ := (tangent_qzero_iff s).mp hs
  rw [f_secondFDeriv, ambientHessian_apply]
  simp [dotProduct, Fin.sum_univ_succ, hr₂, hr₀, hs₂, hs₀, add_comm]

/-- There is a genuine nonzero tangent in the kernel of the Hessian at q0. -/
theorem qzero_degenerate_hessian :
    ∃ r : Pair, r ≠ 0 ∧ IsTangent qzero r ∧
      ∀ s : Pair, IsTangent qzero s → fderiv ℝ (fderiv ℝ f) qzero r s = 0 := by
  let r : Pair := (east, 0)
  have hr : IsTangent qzero r := by
    rw [tangent_qzero_iff]
    simp [r, east, Matrix.cons_val_two]
  refine ⟨r, ?_, hr, ?_⟩
  · intro he
    have hh := congrArg (fun q : Pair ↦ q.1 0) he
    norm_num [r, east] at hh
  · intro s hs
    rw [ambientHessian_at_qzero_on_tangent r s hr hs]
    simp [r, east]

/-- In coordinates (u,v,a,b) on the tangent the Hessian is va'+av'. -/
def tangentCoordinates (w : Fin 4 → ℝ) : Pair :=
  (![w 0, w 1, 0], ![0, w 2, w 3])

lemma tangentCoordinates_mem (w : Fin 4 → ℝ) : IsTangent qzero (tangentCoordinates w) := by
  rw [tangent_qzero_iff]
  simp [tangentCoordinates, Matrix.cons_val_two]

lemma hessian_tangentCoordinates (w z : Fin 4 → ℝ) :
    fderiv ℝ (fderiv ℝ f) qzero (tangentCoordinates w) (tangentCoordinates z) =
      w 1 * z 2 + w 2 * z 1 := by
  rw [ambientHessian_at_qzero_on_tangent _ _ (tangentCoordinates_mem w)
    (tangentCoordinates_mem z)]
  rfl

lemma tangent_hessian_kernel (w : Fin 4 → ℝ) :
    (∀ z : Fin 4 → ℝ,
      fderiv ℝ (fderiv ℝ f) qzero (tangentCoordinates w) (tangentCoordinates z) = 0) ↔
      w 1 = 0 ∧ w 2 = 0 := by
  simp only [hessian_tangentCoordinates]
  constructor
  · intro h
    have h₁ := h ![0, 0, 1, 0]
    have h₂ := h ![0, 1, 0, 0]
    simpa [Matrix.cons_val_two] using And.intro h₁ h₂
  · rintro ⟨hw₁, hw₂⟩ z
    simp [hw₁, hw₂]

end ThreePoints
end ArnoldCounterexample

end

end OAI
