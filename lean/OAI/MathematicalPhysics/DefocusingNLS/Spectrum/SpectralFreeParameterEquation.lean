import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeParameterLocal
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSecondParameterLocal

namespace OAI

/-! Differentiated equations for the actual H columns, identified from their
local holomorphic weighted-resolvent construction. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralFreeFirst_parameter_equation (ell : ℕ) (νp νm z : ℂ)
    (hq : -1 < (((ell : ℂ)-νp)/2+z).re) :
    (∀ t, max 0 (Real.log 4/2) ≤ t →
      AnalyticAt ℂ (fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam) t) z) ∧
    ∀ t, max 0 (Real.log 4/2) < t →
      HasDerivAt (fun s => deriv (fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam) s) z)
        (circularLeadingField t (deriv (fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam) t) z) +
          circularBoundedField (νp-2*z) (νm-2*z) ((ell*(ell+10) : ℕ) : ℂ) 1 0
            (deriv (fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam) t) z) +
          circularPointSlopeCLM νp νm z (spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+z) t)) t := by
  obtain ⟨Y,hnear,hYa,hYd⟩ := spectralFreeFirst_local_differentiated ell νp νm z hq
  have he (s : ℝ) (hs : max 0 (Real.log 4/2) ≤ s) :
      (fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam) s) =ᶠ[𝓝 z] (fun lam => Y lam s) :=
    hnear.mono (fun _ h => (h s hs).symm)
  have hd (s : ℝ) (hs : max 0 (Real.log 4/2) ≤ s) := (he s hs).deriv_eq
  constructor
  · intro t ht
    exact (hYa t).congr (he t ht).symm
  · intro t ht
    have htime : (fun s => deriv (fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam) s) z) =ᶠ[𝓝 t]
        (fun s => deriv (fun lam => Y lam s) z) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact hd s hs.le
    have h := (hYd t ((le_max_left 0 _).trans ht.le)).congr_of_eventuallyEq htime
    apply h.congr_deriv
    rw [hd t ht.le,(he t ht.le).eq_of_nhds]

theorem spectralFreeSecond_parameter_equation (ell : ℕ) (νp νm z : ℂ)
    (hq : -1 < (((ell : ℂ)-νm)/2+z).re) :
    (∀ t, max 0 (Real.log 4/2) ≤ t →
      AnalyticAt ℂ (fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam) t) z) ∧
    ∀ t, max 0 (Real.log 4/2) < t →
      HasDerivAt (fun s => deriv (fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam) s) z)
        (circularLeadingField t (deriv (fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam) t) z) +
          circularBoundedField (νp-2*z) (νm-2*z) ((ell*(ell+10) : ℕ) : ℂ) 1 0
            (deriv (fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam) t) z) +
          circularPointSlopeCLM νp νm z (spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+z) t)) t := by
  obtain ⟨Y,hnear,hYa,hYd⟩ := spectralFreeSecond_local_differentiated ell νp νm z hq
  have he (s : ℝ) (hs : max 0 (Real.log 4/2) ≤ s) :
      (fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam) s) =ᶠ[𝓝 z] (fun lam => Y lam s) :=
    hnear.mono (fun _ h => (h s hs).symm)
  have hd (s : ℝ) (hs : max 0 (Real.log 4/2) ≤ s) := (he s hs).deriv_eq
  constructor
  · intro t ht
    exact (hYa t).congr (he t ht).symm
  · intro t ht
    have htime : (fun s => deriv (fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam) s) z) =ᶠ[𝓝 t]
        (fun s => deriv (fun lam => Y lam s) z) := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact hd s hs.le
    have h := (hYd t ((le_max_left 0 _).trans ht.le)).congr_of_eventuallyEq htime
    apply h.congr_deriv
    rw [hd t ht.le,(he t ht.le).eq_of_nhds]

end DefocusingNLS

end OAI
