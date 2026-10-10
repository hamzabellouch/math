import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalParameterEquation

namespace OAI

/-! Canonical physical outgoing columns satisfy the differentiated equation
used in matching generalized eigenvectors. -/

open Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_physical_parameter_equation (ν η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ)
    (r : ℝ) (hr : 1 < r)
    (hscale : (Complex.exp (ν * (Real.log r : ℂ)) *
      star (Complex.exp (ν * (Real.log r : ℂ)))) ^ n = 1 / (r : ℂ) ^ 2) :
    let V := fun lam => spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Y lam)
    HasDerivAt (fun s => deriv (fun lam => V lam s) z)
      (spectralPhysicalCircularField (ν - 2 * z) (star ν - 2 * z) η n
        (Complex.exp (ν * (Real.log r : ℂ)) * (radialExteriorCanonical ν n b L (Real.log r)).1) r
        (deriv (fun lam => V lam r) z) +
        ((0, -Complex.I * (V z r).1.1), (0, Complex.I * (V z r).2.1))) r := by
  let V := fun lam => spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Y lam)
  let D := fun t => deriv (fun lam => Y lam t) z
  let W := spectralPhysicalPair (ν - 2 * z) (star ν - 2 * z)
    (fun t => circularParameterShear t (Y z t) (D t))
  have he (s : ℝ) (hs : 1 < s) : deriv (fun lam => V lam s) z = W s := by
    have hp := spectralPhysicalPair_hasParameterDerivAt ν (star ν) z Y D s
      (hY.2.2.1 z (Real.log s) (Real.log_pos hs).le).differentiableAt.hasDerivAt
    exact hp.deriv
  have hd := spectralPhysicalShear_hasDerivAt ν z η n hn
    (fun t => (radialExteriorCanonical ν n b L t).1) (Y z) D r
    (lt_trans zero_lt_one hr) hscale (hY.1 z (Real.log r) (Real.log_pos hr).le)
    (canonical_circular_parameter_equation ν η b n hn L hX hb c Y hY z
      (Real.log r) (Real.log_pos hr))
  have htime : (fun s => deriv (fun lam => V lam s) z) =ᶠ[𝓝 r] W := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact he s hs
  have hnew := hd.congr_of_eventuallyEq htime
  change HasDerivAt (fun s => deriv (fun lam => V lam s) z)
    (spectralPhysicalCircularField (ν - 2 * z) (star ν - 2 * z) η n
      (Complex.exp (ν * (Real.log r : ℂ)) * (radialExteriorCanonical ν n b L (Real.log r)).1) r
      (deriv (fun lam => V lam r) z) +
      ((0, -Complex.I * (V z r).1.1), (0, Complex.I * (V z r).2.1))) r
  rw [he r hr]
  exact hnew

end DefocusingNLS

end OAI
