import OAI.MeasureTheory.Falconer.Slicing.GaussianControlledIncidence
import OAI.MeasureTheory.Falconer.Geometry.FrameEmbedding

namespace OAI

/-! # A uniformly transverse row frame for each fixed spherical chart -/

namespace Falconer
variable {n h : ℕ}

theorem exists_transverse_row_frame (hhn : h ≤ n) {w : Space (n+1)} (hw : ‖w‖ = 1) :
    ∃ e : Space h →ₗᵢ[ℝ] Space (n+1),
      ∀ i, inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0 := by
  let u := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let R : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have hR : R u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let f : Fin h → Fin (n+1) := fun i => ⟨i.val+1,by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp [f] at he
    omega
  let v : Fin h → Space (n+1) := fun i => R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))
  have hv : Orthonormal ℝ v := by
    exact ((EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.comp f hf).comp_linearIsometryEquiv R
  obtain ⟨e,he⟩ := orthonormal_frame_embedding hv
  refine ⟨e,fun i => ?_⟩
  rw [he,← hR]
  change inner ℝ (R u) (R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))) = 0
  rw [R.inner_map_map]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.2 (by
    intro heq
    have hz := congrArg Fin.val heq
    dsimp [f] at hz
    omega)

theorem transverse_frame_chart_bound (e : Space h →ₗᵢ[ℝ] Space (n+1))
    (w₀ : Space (n+1))
    (he : ∀ i, inner ℝ w₀ (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    {w : Space (n+1)} {ρ : ℝ} (hw : dist w w₀ ≤ ρ) (i : Fin h) :
    |inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i))| ≤ ρ := by
  let b := e (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hi : inner ℝ w b = inner ℝ (w-w₀) b := by rw [inner_sub_left,he i,sub_zero]
  rw [hi]
  calc
    _ ≤ ‖w-w₀‖*‖b‖ := abs_real_inner_le_norm _ _
    _ = dist w w₀ := by
      rw [show ‖b‖ = 1 from (e.norm_map _).trans
        ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i),mul_one,dist_eq_norm]
    _ ≤ _ := hw

end Falconer

end OAI
