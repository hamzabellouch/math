import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationCounting
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationModes

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def quadraticCorrelationConstant : ℝ := 8 * cutoffFourierBound^2

theorem quadraticCorrelationConstant_pos : 0 < quadraticCorrelationConstant := by
  have hC := cutoffFourierBound_pos
  unfold quadraticCorrelationConstant
  positivity

theorem centeredQuadraticSum_dyadic_correlation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
    [NeZero (∏ i, p i)] [NeZero (∏ j, r j)]
    (hp : ∀ i, (p i).Prime) (hr : ∀ j, (r j).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
    (A : ∀ i, Finset (ZMod (p i))) (B : ∀ j, Finset (ZMod (r j)))
    (mInv : ZMod (∏ i, p i)) (mInv' : ZMod (∏ j, r j))
    {S v : ℕ} (hS : 0 < S) (hv : 0 < v) {R : ℝ} (hR : 0 < R) (h θ : ℝ)
    (hperiod : (Nat.lcm (∏ i, p i) (∏ j, r j) : ℝ) *
      (harmonic (Nat.lcm (∏ i, p i) (∏ j, r j)) : ℝ) ≤ S) :
    ‖∑ s ∈ Finset.Ico S (2*S),
      centeredQuadraticSum p hcop A mInv s v 1 R h θ *
        conj (centeredQuadraticSum r hcor B mInv' s v 1 R h θ) / (s : ℂ)‖ ≤
      quadraticCorrelationConstant *
        ((Nat.gcd (∏ i, p i) (∏ j, r j) : ℝ) /
          (Real.sqrt ((∏ i, p i : ℕ) : ℝ) * Real.sqrt ((∏ j, r j : ℕ) : ℝ))) := by
  let d : ℕ := ∏ i, p i
  let e : ℕ := ∏ j, r j
  let G : ℝ := (Nat.gcd d e : ℝ)/(Real.sqrt d*Real.sqrt e)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  rw [Finset.sum_Ico_eq_sum_range, show 2*S-S = S by omega]
  change ‖∑ n ∈ Finset.range S,
    positiveQuadraticSum d (centeredQuadraticAmplitude p hcop A mInv (S+n) v)
      (S+n) v R (h+θ) *
    conj (positiveQuadraticSum e (centeredQuadraticAmplitude r hcor B mInv' (S+n) v)
      (S+n) v R (h+θ)) / ((S+n : ℕ) : ℂ)‖ ≤ quadraticCorrelationConstant*G
  apply positiveQuadraticSum_dyadic_bound
    (d := d) (e := e) (S := S) (v := v)
    (fun s => centeredQuadraticAmplitude p hcop A mInv s v)
    (fun s => centeredQuadraticAmplitude r hcor B mInv' s v)
    (h+θ) hS hv hR (mul_nonneg quadraticCorrelationConstant_pos.le hG)
  exact centeredQuadraticMode_dyadic_bound p r hp hr hcop hcor A B mInv mInv' hR h θ hperiod

end Ostmann.QuadraticCenter

end

end OAI
