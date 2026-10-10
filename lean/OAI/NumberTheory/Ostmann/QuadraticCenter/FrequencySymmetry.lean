import OAI.NumberTheory.Ostmann.QuadraticCenter.CenterCorrection
import OAI.NumberTheory.Ostmann.QuadraticCenter.CenteredQuadraticSum
import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped FourierTransform ComplexConjugate

theorem cutoffFourier_neg (x : ℝ) : cutoffFourier (-x) = conj (cutoffFourier x) := by
  have hf : (fun t : ℝ => ((SchwartzCutoff.psi t).re : ℂ)) = SchwartzCutoff.psi := by
    funext t
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im, SchwartzCutoff.psi_im]
  have hh := SchwartzCutoff.fourier_real_conj (fun t => (SchwartzCutoff.psi t).re) x
  rw [hf] at hh
  simpa only [cutoffFourier, SchwartzMap.fourier_coe] using hh.symm

theorem weylPhase_neg (x : ℝ) : weylPhase (-x) = conj (weylPhase x) := by
  simp only [weylPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem unitaryDFT_neg_of_real {d : ℕ} [NeZero d]
    (G : ZMod d → ℂ) (hG : ∀ x, conj (G x) = G x) (v : ZMod d) :
    Supply.unitaryDFT G (-v) = conj (Supply.unitaryDFT G v) := by
  simp only [Supply.unitaryDFT, map_div₀, Complex.conj_ofReal, Supply.conj_dft]
  have he : (fun x => conj (G x)) = G := funext hG
  rw [he]

theorem centeredProduct_real {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (x : ZMod (∏ i, p i)) :
    conj (centeredProduct p hcop S x) = centeredProduct p hcop S x := by
  simp only [centeredProduct, map_prod, Complex.conj_ofReal]

def quadraticFourierFrequency (q d : ℕ) [NeZero d] (G : ZMod d → ℂ)
    (mInv : ZMod d) (a R : ℝ) (u : ℤ) : ℂ :=
  (jacobiSym u q : ℂ) * Supply.unitaryDFT G (-(u : ZMod d) * mInv) *
    weylPhase (a * u / d) * cutoffFourier ((u : ℝ) / (R * d))

theorem quadraticFourierFrequency_neg (q d : ℕ) [NeZero d]
    (G : ZMod d → ℂ) (hG : ∀ x, conj (G x) = G x)
    (mInv : ZMod d) (a R : ℝ) (u : ℤ) :
    quadraticFourierFrequency q d G mInv a R (-u) =
      (jacobiSym (-1) q : ℂ) * conj (quadraticFourierFrequency q d G mInv a R u) := by
  have hJ : jacobiSym (-u) q = jacobiSym (-1) q * jacobiSym u q := by
    simpa only [neg_one_mul] using jacobiSym.mul_left (-1) u q
  have hg : -((-u : ℤ) : ZMod d) * mInv = -(-(u : ZMod d) * mInv) := by
    simp only [Int.cast_neg, neg_neg, neg_mul]
  have hp : a * ((-u : ℤ) : ℝ) / d = -(a * (u : ℝ) / d) := by push_cast; ring
  have hc : (((-u : ℤ) : ℝ) / (R * d)) = -((u : ℝ) / (R * d)) := by push_cast; ring
  simp only [quadraticFourierFrequency, hJ, Int.cast_mul, hg,
    unitaryDFT_neg_of_real G hG, hp, weylPhase_neg, hc, cutoffFourier_neg,
    map_mul, map_intCast]
  ring

end Ostmann.QuadraticCenter

end

end OAI
