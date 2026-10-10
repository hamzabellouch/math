import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactEvaluation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBoundary
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

namespace OAI

/-! Uniform convergence of the actual exterior profile on each fixed annulus. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialShootingFreeExterior (z : ProfileMatchingBall) (r : ℝ) : ℂ :=
  Complex.exp ((-2*radialShootingQ z)*(Real.log r : ℂ))*
    (radialFreeSlowJet (radialShootingQ z) (radialShootingM z) (Real.log r)).1

theorem radialShootingExterior_uniform_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (R : ℝ) :
    TendstoUniformlyOn (fun i => radialShootingExteriorProfile (s i) (z i))
      (radialShootingFreeExterior z₀) atTop (Icc innerBoundaryRadius R) := by
  let N := fun i => s i+radialInnerShootingThreshold
  have hN : StrictMono N := fun i j hij => Nat.add_lt_add_right (hs hij) _
  let ν := fun i => radialShootingNu (N i) (z i)
  let ν₀ := -2*radialShootingQ z₀
  have hν : Tendsto ν atTop (𝓝 ν₀) :=
    radialShootingNu_subsequence_tendsto N hN z z₀ hz
  obtain ⟨δ,ρ,hδ,hδm,hsmall,hρ,hupper,hlower⟩ := radialShooting_free_annulus z₀
  have hq : -1 < (radialShootingQ z₀).re := by simp [radialShootingQ]
  have hH := (radialExteriorCanonical_H_limit_subsequence N hN ν
    (fun i => radialShootingM (z i)) (radialShootingQ z₀) (radialShootingM z₀)
    hq hν (continuous_radialShootingM.continuousAt.tendsto.comp hz) δ ρ
    (Real.log innerBoundaryRadius) hδ hδm hsmall hρ hupper hlower).2
  have hlog : ContinuousOn Real.log (Icc innerBoundaryRadius R) := by
    apply Real.continuousOn_log.mono
    intro r hr
    exact ne_of_gt (lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) hr.1)
  have hH' := (uniformContinuous_fst.comp_tendstoUniformlyOn hH).comp Real.log
  have hHann : TendstoUniformlyOn
      (fun i r => (radialExteriorCanonical (ν i) (N i) (radialShootingM (z i))
        (Real.log innerBoundaryRadius) (Real.log r)).1)
      (fun r => (radialFreeSlowJet (radialShootingQ z₀) (radialShootingM z₀)
        (Real.log r)).1) atTop (Icc innerBoundaryRadius R) := by
    apply hH'.mono
    intro r hr
    exact Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr.1
  let : CompactSpace (Icc innerBoundaryRadius R) := isCompact_iff_compactSpace.mp isCompact_Icc
  let E : ℂ → Icc innerBoundaryRadius R → ℂ :=
    fun v r => Complex.exp (v*(Real.log r.val : ℂ))
  have hE : Continuous ↿E := by
    apply Complex.continuous_exp.comp
    exact continuous_fst.mul (Complex.continuous_ofReal.comp
      (hlog.domRestrict.comp continuous_snd))
  have hEu : TendstoUniformly (fun i => E (ν i)) (E ν₀) atTop :=
    fun u hu => hν.eventually ((Continuous.tendstoUniformly E hE ν₀) u hu)
  have hEann : TendstoUniformlyOn (fun i r => Complex.exp (ν i*(Real.log r : ℂ)))
      (fun r => Complex.exp (ν₀*(Real.log r : ℂ))) atTop (Icc innerBoundaryRadius R) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    exact hEu
  have hcJ : Continuous (radialFreeSlowJet (radialShootingQ z₀) (radialShootingM z₀)) :=
    continuous_iff_continuousAt.mpr (fun t => (radialFreeSlowJet_hasDerivAt _ _ hq t).continuousAt)
  have hcH : ContinuousOn (fun r => (radialFreeSlowJet (radialShootingQ z₀)
      (radialShootingM z₀) (Real.log r)).1) (Icc innerBoundaryRadius R) :=
    hcJ.fst.comp_continuousOn hlog
  have hcE : ContinuousOn (fun r => Complex.exp (ν₀*(Real.log r : ℂ)))
      (Icc innerBoundaryRadius R) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hlog))
  have hp := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    (hEann.tendstoLocallyUniformlyOn.mul₀ hHann.tendstoLocallyUniformlyOn hcE hcH)
  convert hp using 1 <;> ext <;> rfl

end DefocusingNLS

end OAI
