import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxSystem
import Mathlib.Analysis.ODE.PicardLindelof

namespace OAI

/-! Smooth coefficient regularity propagates to the classical flux state on an annulus. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFluxField_contDiffOn (ell : ℕ) (μ A : ℝ → ℝ) (c ζ : ℂ) (s : Set ℝ)
    (hμ : ContDiffOn ℝ ∞ μ s) (hA : ContDiffOn ℝ ∞ A s)
    (hμ0 : ∀ r ∈ s, μ r ≠ 0) (hr0 : ∀ r ∈ s, r ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => spectralFluxField ell (μ p.1) (A p.1) c ζ p.1 p.2)
      (s ×ˢ univ) := by
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => (μ p.1 : ℂ)) (s ×ˢ univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hμ.comp contDiff_fst.contDiffOn (fun _ hp => hp.1))
  have ha : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => (A p.1 : ℂ)) (s ×ˢ univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hA.comp contDiff_fst.contDiffOn (fun _ hp => hp.1))
  have hr : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => (p.1 : ℂ)) (s ×ˢ univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiff_fst.contDiffOn
  have hm0 (p : ℝ × E₄) (hp : p ∈ s ×ˢ univ) : (μ p.1 : ℂ) ≠ 0 :=
    by exact_mod_cast hμ0 p.1 hp.1
  have hr11 (p : ℝ × E₄) (hp : p ∈ s ×ˢ univ) : (p.1 : ℂ)^11 ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hr0 p.1 hp.1)
  have h11 := hr.pow 11
  have h9 := hr.pow 9
  have h00 : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.1.1) (s ×ˢ univ) := by fun_prop
  have h01 : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.1.2) (s ×ˢ univ) := by fun_prop
  have h10 : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.2.1) (s ×ˢ univ) := by fun_prop
  have h11' : ContDiffOn ℝ ∞ (fun p : ℝ × E₄ => p.2.2.2) (s ×ˢ univ) := by fun_prop
  exact (((h10.mul (h11.inv hr11)).add (ha.mul h01)).mul (hm.inv hm0)).prodMk
    (((h11'.mul (h11.inv hr11)).sub (ha.mul h00)).mul (hm.inv hm0)) |>.prodMk
      (((((contDiffOn_const.mul h9).mul hm).mul h00).sub
        (((contDiffOn_const.mul h11).mul hm).mul h01)).prodMk
       ((((contDiffOn_const.mul h9).mul hm).mul h01).add
        (((contDiffOn_const.mul h11).mul hm).mul h00)))

theorem spectralFluxState_contDiffOn_annulus (ell : ℕ) (R l α β : ℝ)
    (hR : 0 < R) (hl : 0 < l) (hlα : l < α) (hβR : β < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (hws : ContDiffOn ℝ ∞ w.density (Icc α β))
    (has : ContDiffOn ℝ ∞ a.density (Icc α β))
    (he : ∀ v : spectralHarmonicCoreSubspace ell R l,
      spectralHarmonicPairComplexForm ell R w u v=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) v) :
    ContDiffOn ℝ ∞ (spectralFluxState ell R hR w a u) (Icc α β) := by
  have hs : Icc α β ⊆ Ioo l R := fun x hx => ⟨hlα.trans_le hx.1,hx.2.trans_lt hβR⟩
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
    (f := fun x U => spectralFluxField ell (w.density x) (a.density x) c ζ x U)
    (u := (univ : Set E₄))
  · exact spectralFluxField_contDiffOn ell w.density a.density c ζ (Icc α β) hws has
      (fun x hx => (hpos x ⟨hl.trans (hs hx).1,(hs hx).2⟩).ne')
      (fun x hx => (hl.trans (hs hx).1).ne')
  · intro x hx
    exact (spectralFluxState_hasDerivAt ell R l hR hl w a u c ζ B hw ha hpos he x (hs hx)).hasDerivWithinAt
  · exact fun _ _ => mem_univ _

end DefocusingNLS

end OAI
