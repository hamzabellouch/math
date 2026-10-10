import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondClassicalFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEulerRegularBranch
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreLocality

namespace OAI

/-! A limiting weak kernel is a regular harmonic power inside the constrained core. -/

open Set MeasureTheory Filter Topology
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralHarmonicCore_representative_zero (ell : ℕ) (R l : ℝ) (hR : 0 < R)
    (hlR : l ≤ R) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R l) (x : ℝ) (hx : x ∈ Ioc 0 l) :
    spectralHarmonicRepresentative ell R hR u.fst x=0 := by
  rw [spectralHarmonicCore_mem] at hu
  change spectralRadialRepresentative R hR (spectralHarmonicRadialForget ell R u.fst) x=0
  rw [spectralRadialRepresentative,dite_eq_left hx.1]
  exact spectralRadialCore_point_zero_of_le R l x hR hx.1 hx.2 hlR _ hu

theorem spectralSecond_core_power (ell : ℕ) (R l : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hlR : l < R)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R l)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R))
    (hpos : ∀ x ∈ Ioo 0 R, 0 < w.density x)
    (hcore : ∀ x ∈ Ioc 0 l, w.density x=1)
    (he : ∀ f : 𝓢(ℝ,ℂ),
      spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR
        (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) c ζ B
        (spectralHarmonicObservation ell R hR u)) (spectralSecondTest ell R f)) :
    ∃ C : ℂ, (∀ x ∈ Ioc 0 l, spectralHarmonicRepresentative ell R hR u.snd x=C*(x : ℂ)^ell) ∧
      deriv (spectralHarmonicRepresentative ell R hR u.snd) l=
        (ell : ℂ)*spectralHarmonicRepresentative ell R hR u.snd l/(l : ℂ) := by
  let g := spectralHarmonicRepresentative ell R hR u.snd
  let P := spectralSecondClassicalFlux ell R hR w a u
  obtain ⟨hg,hgc,hP⟩ := spectralSecond_classical ell R hR w a u c ζ B hw ha hpos he
  have hsub : Ioc 0 l ⊆ Ioo 0 R := fun x hx => ⟨hx.1,hx.2.trans_lt hlR⟩
  have hz (x : ℝ) (hx : x ∈ Ioc 0 l) :=
    spectralHarmonicCore_representative_zero ell R l hR hlR.le u hu x hx
  have hflux (x : ℝ) (hx : x ∈ Ioc 0 l) : P x=(x : ℂ)^11*deriv g x := by
    dsimp only [P,spectralSecondClassicalFlux,g]
    rw [hcore x hx,hz x hx]
    simp
  have hdg (x : ℝ) (hx : x ∈ Ioo 0 l) : HasDerivAt g (P x/(x : ℂ)^11) x := by
    have hd := (hg x (hsub (Ioo_subset_Ioc_self hx))).differentiableAt
      (Ioo_mem_nhds hx.1 (hx.2.trans hlR))
    have hxn : (x : ℂ)^11 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hx.1.ne')
    rw [hflux x (Ioo_subset_Ioc_self hx),mul_div_cancel_left₀ _ hxn]
    exact hd.hasDerivAt
  have hdP (x : ℝ) (hx : x ∈ Ioo 0 l) :
      HasDerivAt P ((ell : ℂ)*((ell : ℂ)+10)*(x : ℂ)^9*g x) x := by
    have hp := hP x (hsub (Ioo_subset_Ioc_self hx))
    simpa only [spectralSecondContinuousSource,hcore x (Ioo_subset_Ioc_self hx),
      hz x (Ioo_subset_Ioc_self hx),one_smul,smul_zero,mul_zero,add_zero,
      Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_ofNat] using hp
  obtain ⟨C,hC⟩ := spectralEuler_regular_branch ell l hl g P hdg hdP
    (spectralRadialRepresentative_origin_decay R hR (spectralHarmonicRadialForget ell R u.snd) ell)
  have hclosed : Ioc (0 : ℝ) l ⊆ closure (Ioo 0 l) := by
    rw [closure_Ioo hl.ne]
    exact Ioc_subset_Icc_self
  have hCE : EqOn g (fun x : ℝ => C*(x : ℂ)^ell) (Ioo 0 l) := hC
  have hCfull : EqOn g (fun x : ℝ => C*(x : ℂ)^ell) (Ioc 0 l) :=
    hCE.of_subset_closure ((spectralHarmonicRepresentative_continuousOn ell R hR u.snd).mono hsub)
      (by fun_prop) Ioo_subset_Ioc_self hclosed
  refine ⟨C,hCfull,?_⟩
  have hderiv : EqOn (deriv g) (fun x : ℝ => (ell : ℂ)*g x/(x : ℂ)) (Ioo 0 l) := by
    intro x hx
    have heq : g =ᶠ[𝓝 x] fun y : ℝ => C*(y : ℂ)^ell := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hC y hy
    have hd := ((spectralRadialPower_hasDerivAt ell x hx.1.ne').const_mul C).congr_of_eventuallyEq heq
    rw [hd.deriv]
    change C*((ell : ℂ)*(x : ℂ)^ell/(x : ℂ))=(ell : ℂ)*g x/(x : ℂ)
    rw [hC x hx]
    ring
  have hfcont : ContinuousOn (fun x : ℝ => (ell : ℂ)*g x/(x : ℂ)) (Ioc 0 l) :=
    (continuousOn_const.mul ((spectralHarmonicRepresentative_continuousOn ell R hR u.snd).mono hsub)).div
      Complex.continuous_ofReal.continuousOn (fun x hx => by exact_mod_cast hx.1.ne')
  exact (hderiv.of_subset_closure (hgc.mono hsub) hfcont Ioo_subset_Ioc_self hclosed) ⟨hl,le_rfl⟩

end DefocusingNLS

end OAI
