import OAI.Analysis.KadisonKastler.PublishedCommonPosition
import OAI.Analysis.KadisonKastler.FaithfulRepresentation

namespace OAI

/-! # Returning a common-position isomorphism to the original space -/

namespace KadisonKastler

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N R : VonNeumannAlgebra H} {hRM : R ≤ M} {hRN : R ≤ N} {g : ℝ}

namespace CommonTracialPositionData

variable (d : CommonTracialPositionData M N R hRM hRN g K)

/-- Transport through the two faithful representations. -/
def transportEquiv (θ : Algebra d.left ≃⋆ₐ[ℂ] Algebra d.right) :
    Algebra M ≃⋆ₐ[ℂ] Algebra N :=
  (d.leftEquiv.trans θ).trans d.rightEquiv.symm

@[simp]
theorem rightEquiv_transportEquiv (θ : Algebra d.left ≃⋆ₐ[ℂ] Algebra d.right)
    (x : Algebra M) : d.rightEquiv (d.transportEquiv θ x) = θ (d.leftEquiv x) :=
  d.rightEquiv.apply_symm_apply _

/-- The comparison of original contractions in the published theorem is
exactly what transfers the perturbation estimate back to the original
Hilbert space. -/
theorem transportEquiv_unitBall_bound
    (θ : Algebra d.left ≃⋆ₐ[ℂ] Algebra d.right) {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x : Algebra d.left,
      ‖(θ x : K →L[ℂ] K) - (x : K →L[ℂ] K)‖ ≤ C * ‖x‖)
    (hgap : kkDistance M N < g) (x : Algebra M) (hx : ‖x‖ ≤ 1) :
    ‖(d.transportEquiv θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤
      C + d.tolerance + 2 * g := by
  obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx ⟨x.property, hx⟩ hgap
  let b : Algebra N := ⟨y, hy.1⟩
  have hnorm : ‖d.leftEquiv x‖ = ‖x‖ :=
    injective_starAlgHom_norm d.leftEquiv.toStarAlgHom d.leftEquiv.injective x
  have hclose : ‖(θ (d.leftEquiv x) : K →L[ℂ] K) -
      (d.leftEquiv x : K →L[ℂ] K)‖ ≤ C := by
    have hh := hθ (d.leftEquiv x)
    rw [hnorm] at hh
    exact hh.trans (by nlinarith)
  have hcomparison := d.comparison x b hx hy.2
  have hfaithful : ‖(d.transportEquiv θ x : H →L[ℂ] H) - y‖ =
      ‖(θ (d.leftEquiv x) : K →L[ℂ] K) - (d.rightEquiv b : K →L[ℂ] K)‖ := by
    change ‖d.transportEquiv θ x - b‖ = ‖θ (d.leftEquiv x) - d.rightEquiv b‖
    have hh := injective_starAlgHom_norm d.rightEquiv.toStarAlgHom
      d.rightEquiv.injective (d.transportEquiv θ x - b)
    change ‖d.rightEquiv (d.transportEquiv θ x - b)‖ = _ at hh
    rw [map_sub, d.rightEquiv_transportEquiv] at hh
    exact hh.symm
  have hfirst : ‖(d.transportEquiv θ x : H →L[ℂ] H) - y‖ ≤
      C + (d.tolerance + ‖(x : H →L[ℂ] H) - y‖) := by
    rw [hfaithful]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (d.leftEquiv x : K →L[ℂ] K) _).trans
      (add_le_add hclose hcomparison)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (d.transportEquiv θ x : H →L[ℂ] H) y (x : H →L[ℂ] H)
  rw [norm_sub_rev y] at ht
  linarith

/-- The transferred estimate holds on every algebra element, with no
loss in its constant. -/
theorem transportEquiv_bound
    (θ : Algebra d.left ≃⋆ₐ[ℂ] Algebra d.right) {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x : Algebra d.left,
      ‖(θ x : K →L[ℂ] K) - (x : K →L[ℂ] K)‖ ≤ C * ‖x‖)
    (hgap : kkDistance M N < g) (x : Algebra M) :
    ‖(d.transportEquiv θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤
      (C + d.tolerance + 2 * g) * ‖x‖ := by
  let F : Algebra M →L[ℂ] (H →L[ℂ] H) :=
    starAlgHomToContinuousLinearMap
      (N.toStarSubalgebra.subtype.comp (d.transportEquiv θ).toStarAlgHom) -
        starAlgHomToContinuousLinearMap M.toStarSubalgebra.subtype
  have hg : 0 ≤ g := (kkDistance_nonneg M N).trans hgap.le
  have hF : ‖F‖ ≤ C + d.tolerance + 2 * g :=
    ContinuousLinearMap.opNorm_le_of_unit_norm
      (add_nonneg (add_nonneg hC d.tolerance_nonneg) (mul_nonneg (by norm_num) hg))
      (fun x hx =>
      d.transportEquiv_unitBall_bound θ hC hθ hgap x hx.le)
  exact (F.le_opNorm x).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg x))

end CommonTracialPositionData

end

end KadisonKastler

end OAI
