import Mathlib
import OAI.Analysis.AffineBernstein.JetCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Strict curvature of the actual level hypersurface forces strict concavity
of its support value in the base variables. -/
theorem support_base_hessian_neg {F : S × E → ℝ} {Y : S → E} {s : S} {e : E} {lam : ℝ}
    (hF : ContDiffAt ℝ ∞ F (s,Y s)) (hY : ContDiffAt ℝ ∞ Y s)
    (hlevel : (fun r => F (r,Y r)) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)))
    (hlam : 0 < lam)
    (hconormal : ∀ z : E, fderiv ℝ F (s,Y s) (0,z) = lam * inner ℝ e z)
    (hcurv : ∀ z : S × E, z ≠ 0 → fderiv ℝ F (s,Y s) z = 0 →
      0 < fderiv ℝ (fderiv ℝ F) (s,Y s) z z)
    {v : S} (hv : v ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun r => inner ℝ e (Y r))) s v v < 0 := by
  let X : S → S × E := fun r => (r,Y r)
  have hX : ContDiffAt ℝ ∞ X s := contDiffAt_id.prodMk hY
  let z : S × E := (v, fderiv ℝ Y s v)
  have hz : z ≠ 0 := fun hc => hv (congrArg Prod.fst hc)
  have hD : fderiv ℝ F (s,Y s) z = 0 := by
    have he := hlevel.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (F ∘ X) s = _ at he
    rw [fderiv_comp s (hF.differentiableAt (by simp)) (hX.differentiableAt (by simp))] at he
    have hh := congrArg (fun L : S →L[ℝ] ℝ => L v) he
    simpa only [ContinuousLinearMap.comp_apply, fderiv_const_apply, zero_apply,
      graphMap_fderiv (hY.differentiableAt (by simp)), X, z] using hh
  have hD2 := (hlevel.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have he := congrArg (fun L : S →L[ℝ] (S →L[ℝ] ℝ) => L v v) hD2
  have hchain := second_fderiv_comp (g := X) (x := s) hF hX v v
  change fderiv ℝ (fderiv ℝ (fun r => F (r,Y r))) s v v = _ at hchain
  rw [hchain, graphMap_fderiv (hY.differentiableAt (by simp)),
    graphMap_second hY, hconormal] at he
  have hs := second_fderiv_clm_comp (InnerProductSpace.toDual ℝ E e) hY v v
  change fderiv ℝ (fderiv ℝ (fun r => inner ℝ e (Y r))) s v v =
    inner ℝ e (fderiv ℝ (fderiv ℝ Y) s v v) at hs
  have hc := hcurv z hz hD
  have hzero : fderiv ℝ (fun _ : S => (0 : ℝ)) = (fun _ => 0) :=
    funext (fun _ => fderiv_const_apply 0)
  rw [hzero, fderiv_const_apply] at he
  simp only [zero_apply] at he
  change 0 < fderiv ℝ (fderiv ℝ F) (X s) (v, fderiv ℝ Y s v) (v, fderiv ℝ Y s v) at hc
  rw [hs]
  nlinarith

end AffineBernstein
end

end OAI
