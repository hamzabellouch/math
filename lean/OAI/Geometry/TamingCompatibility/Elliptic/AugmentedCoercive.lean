import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.VariationalResolvent

namespace OAI


noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma projected_energy_coercive (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (K : Submodule ℝ H) [CompleteSpace K] (G : H →L[ℝ] V)
    (hgraph : ∀ u, ‖u‖^2 = ‖i u‖^2 + ‖D u‖^2)
    (hweak : ∀ f v, ⟪D (G f),D v⟫ = ⟪f-K.starProjection f,i v⟫) :
    IsCoercive (energy (K.starProjection ∘L i) D) := by
  let q := ‖D‖ * ‖G‖
  have hq : 0 ≤ q := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let C := 2+q^2
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C⁻¹,inv_pos.mpr hC,fun u => ?_⟩
  have hp : ⟪K.starProjection (i u),i u⟫ = ‖K.starProjection (i u)‖^2 := by
    simpa only [RCLike.re_to_real,real_inner_self_eq_norm_sq,Submodule.starProjection_apply,Submodule.norm_coe] using K.re_inner_starProjection_eq_normSq (i u)
  have hw := hweak (i u) u
  rw [inner_sub_left,real_inner_self_eq_norm_sq,hp] at hw
  have hb : ‖i u‖^2-‖K.starProjection (i u)‖^2 ≤ q*‖i u‖*‖D u‖ := by
    rw [← hw]
    apply (real_inner_le_norm _ _).trans
    have hh : ‖D (G (i u))‖ ≤ q*‖i u‖ := calc
      _ ≤ ‖D‖*‖G (i u)‖ := D.le_opNorm _
      _ ≤ ‖D‖*(‖G‖*‖i u‖) := mul_le_mul_of_nonneg_left (G.le_opNorm _) (norm_nonneg _)
      _ = _ := mul_assoc _ _ _ |>.symm
    exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  have hu : ‖u‖^2 ≤ C*(‖K.starProjection (i u)‖^2+‖D u‖^2) := by
    rw [hgraph]
    dsimp only [C]
    nlinarith [sq_nonneg (‖i u‖-q*‖D u‖),sq_nonneg ‖D u‖,
      mul_nonneg (sq_nonneg q) (sq_nonneg ‖K.starProjection (i u)‖)]
  simp only [energy_apply,ContinuousLinearMap.comp_apply,real_inner_self_eq_norm_sq]
  have hh := (mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hC.le))
  rw [← mul_assoc,inv_mul_cancel₀ hC.ne',one_mul] at hh
  nlinarith
end TamingCompatibility.Variational

end

end OAI
