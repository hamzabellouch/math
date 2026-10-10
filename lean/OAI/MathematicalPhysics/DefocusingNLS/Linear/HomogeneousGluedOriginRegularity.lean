import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedOriginBasis
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularCompleteness

namespace OAI

/-! Integer angular modes have all regular-origin derivatives; no expansion is assumed. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousGlued_origin_regularity (ell m : ℕ) (νp νm : ℂ)
    (R : ℝ) (hR : 0 < R) (Q : ℝ → ℂ) (hQ : Continuous Q)
    (hQs : ContDiffOn ℝ ∞ Q (Icc 0 R)) (U : ℝ → E₄)
    (hUc : ContDiff ℝ 2 (fun r => (U r).1.1) ∧
      ContDiff ℝ 2 (fun r => (U r).2.1))
    (hU : ∀ r ∈ Ioc 0 R, HasDerivAt U
      (spectralPhysicalCircularField νp νm ((ell * (ell + 10) : ℕ) : ℂ) m
        (Q r) r (U r)) r) :
    ContDiffOn ℝ ∞ (fun r => (U r).1.1) (Icc 0 R) ∧
      ContDiffOn ℝ ∞ (fun r => (U r).2.1) (Icc 0 R) := by
  obtain ⟨Rp, Rm, hp, hm, hrank, hpc, hmc, hps, hms⟩ :=
    homogeneousGlued_exists_origin_basis ell m νp νm R hR Q hQ hQs
  obtain ⟨c, hc⟩ := homogeneousRegular_basis_complete νp νm
    ((ell * (ell + 10) : ℕ) : ℝ) (Nat.cast_nonneg _) m Q hQ R hR U Rp Rm
    hUc hpc hmc (by simpa only [Complex.ofReal_natCast] using hU)
    (by simpa only [Complex.ofReal_natCast] using hp)
    (by simpa only [Complex.ofReal_natCast] using hm) hrank
  have he (r : ℝ) (hr : r ∈ Ioc 0 R) : U r = c.1 • Rp r + c.2 • Rm r :=
    homogeneousPhysicalOutgoingPlane_backward νp νm ((ell * (ell + 10) : ℕ) : ℂ) m Q
      U Rp Rm r R hr.1 hr.2 hQ.continuousOn
      (fun t ht => hU t ⟨hr.1.trans_le ht.1, ht.2⟩)
      (fun t ht => hp t ⟨hr.1.trans_le ht.1, ht.2⟩)
      (fun t ht => hm t ⟨hr.1.trans_le ht.1, ht.2⟩) c hc
  have hep : EqOn (fun r => (U r).1.1)
      (fun r => c.1 * (Rp r).1.1 + c.2 * (Rm r).1.1) (Ioc 0 R) := by
    intro r hr
    exact congrArg (fun V : E₄ => V.1.1) (he r hr)
  have hem : EqOn (fun r => (U r).2.1)
      (fun r => c.1 * (Rp r).2.1 + c.2 * (Rm r).2.1) (Ioc 0 R) := by
    intro r hr
    exact congrArg (fun V : E₄ => V.2.1) (he r hr)
  have hep' : EqOn (fun r => (U r).1.1)
      (fun r => c.1 * (Rp r).1.1 + c.2 * (Rm r).1.1) (Icc 0 R) := by
    have hh := hep.closure hUc.1.continuous
      ((hpc.1.continuous.const_mul c.1).add (hmc.1.continuous.const_mul c.2))
    simpa only [closure_Ioc hR.ne] using hh
  have hem' : EqOn (fun r => (U r).2.1)
      (fun r => c.1 * (Rp r).2.1 + c.2 * (Rm r).2.1) (Icc 0 R) := by
    have hh := hem.closure hUc.2.continuous
      ((hpc.2.continuous.const_mul c.1).add (hmc.2.continuous.const_mul c.2))
    simpa only [closure_Ioc hR.ne] using hh
  exact ⟨((contDiffOn_const.mul hps.1).add (contDiffOn_const.mul hms.1)).congr hep',
    ((contDiffOn_const.mul hps.2).add (contDiffOn_const.mul hms.2)).congr hem'⟩

end DefocusingNLS

end OAI
