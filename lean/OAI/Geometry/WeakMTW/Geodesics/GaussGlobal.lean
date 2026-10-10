import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.FiberSmooth
import OAI.Geometry.WeakMTW.Geodesics.GlobalFirstVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace GaussCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 theorem norm_sq_line_hasDerivAt (v w : E) :
    HasDerivAt (fun s : ℝ => ‖v+s•w‖^2) (2 * inner ℝ v w) 0 := by
  have hd : HasDerivAt (fun s : ℝ => v+s•w) w 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  simpa only [zero_smul,add_zero] using hd.norm_sq
end GaussCalculus

namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem vertical_fan_momentum (x : M) (v w : TangentSpace (model n) x) (t : ℝ) :
    fanMomentum (fun s : ℝ => (⟨x,v+s•w⟩ : TangentBundle (model n) M)) t =
      t * inner ℝ v w := by
  let P : ℝ → TangentBundle (model n) M := fun s => ⟨x,v+s•w⟩
  have hzero : fanMomentum P 0 = 0 := by
    unfold fanMomentum
    have he : (fun s => geodesic (P s) 0) = fun _ : ℝ => x := by
      funext s
      exact geodesic_zero _
    have hderiv : mfderiv 𝓘(ℝ, ℝ) (model n) (fun s => geodesic (P s) 0) 0 = 0 := by
      rw [he, mfderiv_const]
      rfl
    rw [hderiv]
    exact inner_zero_right _
  have hde := GaussCalculus.norm_sq_line_hasDerivAt v w
  have hh := fanMomentum_affine (vertical_fan_smooth x v w) t
  rw [hzero] at hh
  change fanMomentum P t = 0 + t * (deriv (fun s : ℝ => ‖v+s•w‖^2) 0 / 2) at hh
  rw [hde.deriv] at hh
  simpa only [zero_add,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
