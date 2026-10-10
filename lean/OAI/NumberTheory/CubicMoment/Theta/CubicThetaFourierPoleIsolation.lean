import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexRadialTest
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticPoleIsolation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrincipalPart

namespace OAI

/-! The continued arithmetic Fourier coefficient has no artificial poles
from the initial fixed radial test. Its only possible pole in Re(s)>1
is the actual arithmetic pole at 4/3. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_analytic_germ {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) (hne : s≠4/3) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q s ∧
      cubicThetaFrequencyContinuation h=ᶠ[𝓝[≠] s] q := by
  obtain ⟨W,_,hW⟩ := cubicThetaComplexRadialTest_nonzero hh hs
  obtain ⟨g,hg,he⟩ := cubicThetaForcedEnergy_analytic_germ hs hne
  let L : cubicThetaGlobalEnergySpace →L[ℂ] ℂ :=
    (innerSL ℂ (cubicThetaCuspFourierTest h W)).comp cubicThetaCuspRestriction
  let R := cubicThetaFourierRadialTest h W
  have hR : AnalyticAt ℂ R s := (cubicThetaFourierRadialTest_entire hh W).analyticAt s
  have hRn : R s≠0 := hW
  have hG := cubicThetaGamma_analytic_right (s:=s) (by linarith)
  have hGn := Complex.Gamma_ne_zero_of_re_pos (show 0<s.re by linarith)
  have hπ : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hL : AnalyticAt ℂ (fun z => L (g z)) s :=
    (L.analyticAt (g s)).comp (f:=g) (x:=s) hg
  refine ⟨fun z => Complex.Gamma z/((Real.pi:ℂ)*R z)*L (g z),
    (hG.div (analyticAt_const.mul hR) (mul_ne_zero hπ hRn)).mul hL,?_⟩
  have hr : ∀ᶠ z in 𝓝 s, R z≠0 := hR.continuousAt.eventually_ne hRn
  have hγ : ∀ᶠ z in 𝓝 s, Complex.Gamma z≠0 := hG.continuousAt.eventually_ne hGn
  filter_upwards [cubicThetaCuspFourierObservable_continued hh W hs,he,
    nhdsWithin_le_nhds hr,nhdsWithin_le_nhds hγ] with z hz heg hrz hgz
  change inner ℂ (cubicThetaCuspFourierTest h W)
    (cubicThetaCuspRestriction (cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter z) (cubicThetaForcingL2 z)))=_ at hz
  rw [heg] at hz
  change L (g z)=((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*R z at hz
  rw [hz]
  field_simp

theorem cubicThetaFrequencyContinuation_principal_part {h : Eisenstein} (hh : h≠0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (4/3:ℂ) ∧
      (fun s => cubicThetaFrequencyContinuation h s-
        (s-4/3)⁻¹*cubicThetaArithmeticFourierResidue h (4/3))=ᶠ[𝓝[≠] (4/3:ℂ)] q := by
  apply cubicThetaPrincipalPart_removable (cubicThetaFrequencyContinuation_meromorphic hh (by norm_num))
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,smul_eq_mul] using
    cubicThetaFrequencyContinuation_residue hh (σ:=4/3) (by norm_num) (by norm_num)

end CubicFirstMoment

end

end OAI
