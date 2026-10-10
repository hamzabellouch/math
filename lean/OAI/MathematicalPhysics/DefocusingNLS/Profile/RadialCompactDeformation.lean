import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactEvaluation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorVelocity

namespace OAI

/-! The actual deformation eigenvalues converge on every fixed exterior annulus. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_converging_exterior_deformation
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (nhds z₀)) (r : ℕ → ℝ) (r₀ : ℝ)
    (hr : Tendsto r atTop (nhds r₀)) (hr₀ : innerBoundaryRadius ≤ r₀)
    (hrmem : ∀ i, innerBoundaryRadius < r i)
    (hX : ∀ i, HasRadialExterior
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i))
      (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0) :
    let ν₀ := -2*radialShootingQ z₀
    let J₀ := radialFreeSlowJet (radialShootingQ z₀) (radialShootingM z₀) (Real.log r₀)
    let ξ₀ := J₀.2/J₀.1
    let w := fun i => radialVelocity (6-2*radialShootingA (s i))
      (fun t => ‖radialMatchedProfile (s i) (z i) t‖)
    Tendsto (fun i => w i (r i)/r i) atTop
      (nhds (1/2+2/r₀^2*(ν₀.im+ξ₀.im))) ∧
    Tendsto (fun i => deriv (w i) (r i)) atTop
      (nhds (1/2-ξ₀.re-2/r₀^2*(ν₀.im+ξ₀.im)*(11+2*ν₀.re+2*ξ₀.re))) := by
  intro ν₀ J₀ ξ₀ w
  let N := fun i => s i+radialInnerShootingThreshold
  have hN : StrictMono N := fun i j hij => Nat.add_lt_add_right (hs hij) _
  let ν := fun i => radialShootingNu (N i) (z i)
  let Z := fun i => radialExteriorCanonical (ν i) (N i) (radialShootingM (z i))
    (Real.log innerBoundaryRadius)
  let ξ := fun i => (Z i (Real.log (r i))).2/(Z i (Real.log (r i))).1
  have hjet := radialShooting_converging_radius N hN z z₀ hz r r₀ hr hr₀
    (Eventually.of_forall (fun i => (hrmem i).le))
  obtain ⟨δ,ρ,hδ,_hδm,_hsmall,_hρ,_hupper,hlower⟩ := radialShooting_free_annulus z₀
  have hn : J₀.1 ≠ 0 := norm_pos_iff.mp (hδ.trans (hlower (Real.log r₀)
    (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr₀)))
  have hξ : Tendsto ξ atTop (nhds ξ₀) := by
    simpa only [Pi.div_apply,ξ,Z,ν,ξ₀,J₀] using!
      hjet.snd_nhds.div hjet.fst_nhds hn
  have hν := radialShootingNu_subsequence_tendsto N hN z z₀ hz
  have hrpos : 0 < r₀ := lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) hr₀
  have hscale : Tendsto (fun i => 2/(r i)^2) atTop (nhds (2/r₀^2)) := by
    simpa only [Pi.div_apply] using!
      (tendsto_const_nhds (x := (2 : ℝ))).div (hr.pow 2) (pow_ne_zero 2 hrpos.ne')
  have hνr := (Complex.continuous_re.tendsto ν₀).comp hν
  have hνi := (Complex.continuous_im.tendsto ν₀).comp hν
  have hξr := (Complex.continuous_re.tendsto ξ₀).comp hξ
  have hξi := (Complex.continuous_im.tendsto ξ₀).comp hξ
  have htan : Tendsto (fun i => 1/2+2/(r i)^2*((ν i).im+(ξ i).im))
      atTop (nhds (1/2+2/r₀^2*(ν₀.im+ξ₀.im))) := by
    simpa only [Function.comp_def,ν] using!
      (tendsto_const_nhds (x := (1/2 : ℝ))).add (hscale.mul (hνi.add hξi))
  have hrad : Tendsto (fun i => 1/2-(ξ i).re-
      2/(r i)^2*((ν i).im+(ξ i).im)*(11+2*(ν i).re+2*(ξ i).re)) atTop
      (nhds (1/2-ξ₀.re-2/r₀^2*(ν₀.im+ξ₀.im)*(11+2*ν₀.re+2*ξ₀.re))) := by
    simpa only [Function.comp_def,ν] using!
      ((tendsto_const_nhds (x := (1/2 : ℝ))).sub hξr).sub
        ((hscale.mul (hνi.add hξi)).mul
          (((tendsto_const_nhds (x := (11 : ℝ))).add (hνr.const_mul 2)).add
            (hξr.const_mul 2)))
  constructor
  · apply htan.congr'
    exact Eventually.of_forall (fun i =>
      (radialMatchedVelocity_logarithmic (s i) (z i) (hX i) (hmatch i) (r i) (hrmem i)).symm)
  · apply hrad.congr'
    exact Eventually.of_forall (fun i =>
      (radialMatchedDeformation_logarithmic (s i) (z i) (hX i) (hmatch i) (r i) (hrmem i)).symm)

end DefocusingNLS

end OAI
