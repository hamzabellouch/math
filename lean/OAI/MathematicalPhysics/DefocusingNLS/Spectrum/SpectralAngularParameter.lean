import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularSource
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularParameterEquation

namespace OAI

/-! The differentiated regular physical columns, with the angular factor
restored, satisfy the same source system as a radial Jordan chain. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralAngularPair_hasParameterDerivAt (ell : ℕ)
    (Y : ℂ → ℝ → E₄) (D : ℝ → E₄) (z : ℂ) (r : ℝ)
    (hY : HasDerivAt (fun lam => Y lam r) (D r) z) :
    HasDerivAt (fun lam => spectralAngularPair ell (Y lam) r)
      (spectralAngularPair ell D r) z := by
  have hp := (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt z hY
  have hm := (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt z hY
  have hp0 := (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z hp
  have hp1 := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z hp
  have hm0 := (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z hm
  have hm1 := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z hm
  have h0 := hp0.const_mul ((r : ℂ) ^ ell)
  have h1 := ((hp0.const_mul ((ell : ℂ) / (r : ℂ))).add hp1).const_mul ((r : ℂ) ^ ell)
  have h2 := hm0.const_mul ((r : ℂ) ^ ell)
  have h3 := ((hm0.const_mul ((ell : ℂ) / (r : ℂ))).add hm1).const_mul ((r : ℂ) ^ ell)
  convert! (h0.prodMk h1).prodMk (h2.prodMk h3) using 1

theorem spectralRegularParameterPhysical_hasDerivAt (ell m : ℕ) (νp νm Q : ℂ)
    (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ)
    (c : ℂ × ℂ) (z : ℂ)
    (hgap : spectralRegularSourceBound A B
      (-Complex.I * νp / 2 + Complex.I * (ell : ℂ) / 2 + Complex.I * z)
      (Complex.I * νm / 2 - Complex.I * (ell : ℂ) / 2 - Complex.I * z) < 2 * α)
    (r : ℝ) (hr : r ∈ Ioc 0 R)
    (hA : A r = spectralDiagonalCoefficient m Q)
    (hB : B r = spectralCrossCoefficient m Q) :
    let s := spectralRegularSolutionSource (2 * ell + 11) R α hR hα A B
      (-Complex.I * νp / 2 + Complex.I * (ell : ℂ) / 2)
      (Complex.I * νm / 2 - Complex.I * (ell : ℂ) / 2) c
    let W := spectralRegularState (2 * ell + 11) α c (s z)
    let V := spectralRegularState (2 * ell + 11) α 0 (deriv s z)
    HasDerivAt (spectralAngularPair ell V)
      (spectralPhysicalCircularField (νp - 2 * z) (νm - 2 * z)
        ((ell * (ell + 10) : ℕ) : ℂ) m Q r (spectralAngularPair ell V r) +
        ((0, -Complex.I * (spectralAngularPair ell W r).1.1),
         (0, Complex.I * (spectralAngularPair ell W r).2.1))) r := by
  let cp := -Complex.I * νp / 2 + Complex.I * (ell : ℂ) / 2
  let cm := Complex.I * νm / 2 - Complex.I * (ell : ℂ) / 2
  let s := spectralRegularSolutionSource (2 * ell + 11) R α hR hα A B cp cm c
  let W := spectralRegularState (2 * ell + 11) α c (s z)
  let V := spectralRegularState (2 * ell + 11) α 0 (deriv s z)
  change HasDerivAt (spectralAngularPair ell V)
    (spectralPhysicalCircularField (νp - 2 * z) (νm - 2 * z)
      ((ell * (ell + 10) : ℕ) : ℂ) m Q r (spectralAngularPair ell V r) +
      ((0, -Complex.I * (spectralAngularPair ell W r).1.1),
       (0, Complex.I * (spectralAngularPair ell W r).2.1))) r
  have hv := spectralRegularParameterState_hasDerivAt (2 * ell + 11) R α hR hα A B
    cp cm c z hgap r hr
  have hp : cp + Complex.I * z = -Complex.I * (νp - 2 * z) / 2 +
      Complex.I * (ell : ℂ) / 2 := by dsimp only [cp]; ring
  have hm : cm - Complex.I * z = Complex.I * (νm - 2 * z) / 2 -
      Complex.I * (ell : ℂ) / 2 := by dsimp only [cm]; ring
  dsimp only at hv
  rw [hp, hm, hA, hB] at hv
  have hh := spectralRegularPhysical_source_hasDerivAt ell m (νp - 2 * z) (νm - 2 * z)
    Q (-Complex.I * (W r).1.1) (Complex.I * (W r).2.1) V r hr.1 hv
  apply hh.congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · rfl
  · dsimp only [spectralAngularPair, spectralAngularJet, Prod.fst_add, Prod.snd_add]
    ring
  · rfl
  · dsimp only [spectralAngularPair, spectralAngularJet, Prod.fst_add, Prod.snd_add]
    ring

end DefocusingNLS

end OAI
