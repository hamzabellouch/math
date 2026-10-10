import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAiryRiccati
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAiryMass
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRiccatiLimit

namespace OAI

/-! The real logarithmic slope of every nonzero-flux forbidden-side Airy
solution tends to the growing slope. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralAirySlope_tendsto_one
    (q : ℝ → ℂ × ℂ) (T : ℝ) (hT : 1≤T)
    (hq : ContinuousOn q (Ici T))
    (hD : ∀ t, T≤t → HasDerivAt q (spectralScalarField (-(t : ℂ)) (q t)) t)
    (hJ : spectralScalarFlux (q T)≠0) :
    Tendsto (spectralAirySlope q) atTop (𝓝 1) := by
  obtain ⟨S,hTS,hm,hbound⟩ := spectralAiry_eventual_mass_bound q T hT hq hD hJ
  let Q := fun t => spectralScalarMass (q t)
  let P := fun t => spectralScalarMomentum (q t)
  let J := spectralScalarFlux (q T)
  let e := fun t => J^2/(Real.sqrt t*(Q t)^2)
  let D := fun t => Real.sqrt t*(1-(spectralAirySlope q t)^2)-spectralAirySlope q t/(2*t)+e t
  have hS : 1≤S := hT.trans hTS
  have hmass (t : ℝ) (ht : S≤t) : 0<Q t := hm.trans_le (hbound t ht).2
  have hsqrt (t : ℝ) (ht : S≤t) : 0<Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  have hflux (t : ℝ) (ht : S≤t) : spectralScalarFlux (q t)=J :=
    spectralScalarFlux_const T t q (fun x => -x) (hq.mono (fun _ hx => hx.1))
      (fun x hx => by simpa only [Complex.ofReal_neg] using hD x hx.1.le) t ⟨hTS.trans ht,le_rfl⟩
  have hqS : ContinuousOn q (Ici S) := hq.mono (Ici_subset_Ici.mpr hTS)
  have hQc : ContinuousOn Q (Ici S) := by
    have hh := hqS.fst.norm.pow 2
    change ContinuousOn (fun t => ‖(q t).1‖^2) (Ici S) at hh
    simpa only [Q,spectralScalarMass,Complex.normSq_eq_norm_sq] using hh
  have hPc : ContinuousOn P (Ici S) := Complex.continuous_re.comp_continuousOn (hqS.fst.star.mul hqS.snd)
  have hsc : ContinuousOn (spectralAirySlope q) (Ici S) :=
    hPc.div (Real.continuous_sqrt.continuousOn.mul hQc)
      (fun t ht => mul_ne_zero (hsqrt t ht).ne' (hmass t ht).ne')
  have hd (t : ℝ) (ht : S≤t) : HasDerivAt (spectralAirySlope q) (D t) t := by
    have hh := spectralAirySlope_hasDerivAt q t (by linarith) (hD t (hTS.trans ht)) (hmass t ht).ne'
    simpa only [hflux t ht] using hh
  have he0 (t : ℝ) (ht : S≤t) : 0≤e t := by
    dsimp only [e]
    exact div_nonneg (sq_nonneg J) (mul_nonneg (hsqrt t ht).le (sq_nonneg _))
  have heC (t : ℝ) (ht : S≤t) : e t≤(J^2/(Q S)^2)/Real.sqrt t := by
    have hs0 := hsqrt t ht
    have hQt := hmass t ht
    have hQs : 0<Q S := hm
    have hQQ : (Q S)^2≤(Q t)^2 := pow_le_pow_left₀ hQs.le (hbound t ht).2 2
    calc
      e t ≤ J^2/(Real.sqrt t*(Q S)^2) := by
        dsimp only [e]
        exact div_le_div_of_nonneg_left (sq_nonneg J) (by positivity) (mul_le_mul_of_nonneg_left hQQ hs0.le)
      _ = _ := by ring
  exact spectralRiccati_tendsto_one (spectralAirySlope q) D e S (J^2/(Q S)^2) hS hsc hd
    (fun t ht => div_nonneg (hbound t ht).1.le (mul_nonneg (hsqrt t ht).le (hmass t ht).le))
    he0 heC (fun _ _ => rfl)

end DefocusingNLS

end OAI
