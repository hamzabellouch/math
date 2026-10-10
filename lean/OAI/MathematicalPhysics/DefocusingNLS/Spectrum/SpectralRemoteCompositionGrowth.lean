import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolBilinear
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! A finite composition estimate for the coarse derivative growth of the
exterior profile. The outer polynomial degree does not enter the bound. -/

open Set
open scoped ContDiff
namespace DefocusingNLS

theorem spectralRemote_composition_growth
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : ℝ → A) (g : A → B) (L t C D K : ℝ) (k : ℕ)
    (hf : ContDiffOn ℝ ∞ f (Ioi L)) (hg : ContDiff ℝ ∞ g)
    (ht : L < t) (ht0 : 0 ≤ t) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (houter : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i g (f t)‖ ≤ K)
    (hinner : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedDeriv i f t‖ ≤ D*Real.exp (C*t)) :
    ‖iteratedDeriv k (fun s => g (f s)) t‖ ≤
      ((k.factorial : ℝ)*K*D^k)*Real.exp ((k : ℝ)*C*t) := by
  have hbase : 1 ≤ D*Real.exp (C*t) :=
    one_le_mul_of_one_le_of_one_le hD (Real.one_le_exp_iff.mpr (mul_nonneg hC ht0))
  have hb := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hf (by simp : (k : ℕ∞ω) ≤ ∞)
    uniqueDiffOn_univ isOpen_Ioi.uniqueDiffOn (mapsTo_univ _ _) ht
    (by simpa only [iteratedFDerivWithin_univ] using houter)
    (fun i hi hik => by
      rw [HasUniformLogJetBound.norm_jet_within f hf ht i]
      exact (hinner i hi hik).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hbase hi))
  rw [HasUniformLogJetBound.norm_jet_within _ (hg.comp_contDiffOn hf) ht k] at hb
  apply hb.trans_eq
  rw [mul_pow,← Real.exp_nat_mul]
  rw [show (k : ℝ)*(C*t) = (k : ℝ)*C*t by ring]
  ring

end DefocusingNLS

end OAI
