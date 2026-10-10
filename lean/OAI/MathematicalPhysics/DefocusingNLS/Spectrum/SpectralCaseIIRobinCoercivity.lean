import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellInnerRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinNormBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnComparison

namespace OAI

/-! The two mixed Case II Robin slopes control local values by local
first derivatives when the actual Green error is sufficiently small. -/

open Set
namespace DefocusingNLS

theorem spectralNoTurn_ratio_norm_lower (alpha : ℂ) (F nu : ℝ)
    (hnu : 0 < nu) (hF : nu^2/2 ≤ F)
    (hclose : ‖alpha/(Real.sqrt F : ℂ)+Complex.I‖ ≤ 1/2) : nu/4 ≤ ‖alpha‖ := by
  have hFp : 0 < F := (by positivity : 0 < nu^2/2).trans_le hF
  have hs := Real.sqrt_pos.mpr hFp
  have hs2 := Real.sq_sqrt hFp.le
  have hslo : nu/2 ≤ Real.sqrt F := by nlinarith
  have ht := norm_sub_le (alpha/(Real.sqrt F : ℂ)+Complex.I) (alpha/(Real.sqrt F : ℂ))
  have hn : ‖Complex.I‖ ≤ ‖alpha/(Real.sqrt F : ℂ)+Complex.I‖+‖alpha/(Real.sqrt F : ℂ)‖ := by
    convert ht using 1
    congr 1
    ring
  rw [Complex.norm_I,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs] at hn
  have hd : 1/2 ≤ ‖alpha‖/Real.sqrt F := by linarith
  have hh := (le_div_iff₀ hs).mp hd
  linarith

theorem spectralCaseII_robin_coercivity {R E A : ℝ}
    (Sp Sm : SpectralScalarBoundarySystem R E A) (hRE : R ≤ E)
    (J b eta omega gamma d eps nu C delta : ℝ)
    (hp : SpectralTurningComparison Sp J 1 b eta omega gamma d)
    (hm : SpectralNoTurnComparison Sm J eps b eta omega (-gamma))
    (hnu : 0 < nu) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (heps : eps ≤ 1/2) (hsmall : 48*C*delta ≤ 1/4)
    (hkp : nu/2 ≤ (Sp.k R)^2) (hkp' : (Sp.k R)^2 ≤ C*nu)
    (hkm' : (Sm.k R)^2 ≤ C*nu)
    (hF : nu^2/2 ≤ homogeneousSpectralLocalizationFrequency (-1) b eta omega R)
    (q : (ℂ × ℂ) × (ℂ × ℂ))
    (herr : spectralShellPairNorm (Sp.k R) (Sm.k R)
      (q-(Sp.extension q.1.1 R,Sm.extension q.2.1 R)) ≤
      delta*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) :
    (nu/48)*(‖q.1.1‖+‖q.2.1‖) ≤ 2*(‖q.1.2‖+‖q.2.2‖) := by
  let ap := (Sp.U R).2/(Sp.U R).1
  let am := (Sm.U R).2/(Sm.U R).1
  have hap : nu/48 ≤ ‖ap‖ := by
    have hr := hp.2.2.2.2.1
    have hn := Complex.abs_re_le_norm ap
    have ha := neg_le_abs ap.re
    dsimp only [ap] at *
    linarith
  have ham : nu/48 ≤ ‖am‖ := by
    have hh := spectralNoTurn_ratio_norm_lower am
      (homogeneousSpectralLocalizationFrequency (-1) b eta omega R) nu hnu hF
      (hm.2.2.2.2.trans heps)
    linarith
  have he := spectralCoupled_inner_robin_scaled Sp Sm hRE q delta (C*nu) hdelta hkp' hkm' herr
  apply spectralCoupled_robin_coercivity q.1.1 q.2.1 q.1.2 q.2.2 ap am (nu/48) (48*C*delta)
    (by positivity) (by positivity) hsmall hap ham
  · convert he.1 using 1
    ring
  · convert he.2 using 1
    ring

end DefocusingNLS

end OAI
