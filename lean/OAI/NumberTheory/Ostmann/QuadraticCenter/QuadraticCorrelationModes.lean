import OAI.NumberTheory.Ostmann.QuadraticCenter.CenteredQuadraticSum
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelation
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationExpansion

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem centeredQuadraticAmplitude_eq_scalar {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i)) (s v w : ℕ) :
    centeredQuadraticAmplitude p hcop S mInv s v w =
      centeredProductTransform p hcop S
        ((-((v*w^2 : ℕ) : ZMod (∏ i, p i))*mInv)*(s : ZMod (∏ i, p i))) := by
  unfold centeredQuadraticAmplitude
  congr 1
  push_cast
  ring

theorem centeredQuadraticMode_dyadic_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
    [NeZero (∏ i, p i)] [NeZero (∏ j, r j)]
    (hp : ∀ i, (p i).Prime) (hr : ∀ j, (r j).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
    (A : ∀ i, Finset (ZMod (p i))) (B : ∀ j, Finset (ZMod (r j)))
    (mInv : ZMod (∏ i, p i)) (mInv' : ZMod (∏ j, r j))
    {S v : ℕ} {R : ℝ} (hR : 0 < R) (h θ : ℝ)
    (hperiod : (Nat.lcm (∏ i, p i) (∏ j, r j) : ℝ) *
      (harmonic (Nat.lcm (∏ i, p i) (∏ j, r j)) : ℝ) ≤ S) (w w' : ℕ) :
    ‖∑ n ∈ Finset.range S,
      quadraticCrossMode (∏ i, p i) (∏ j, r j)
        (centeredQuadraticAmplitude p hcop A mInv (S+n) v)
        (centeredQuadraticAmplitude r hcor B mInv' (S+n) v)
        (S+n) v w w' R (h+θ)‖ ≤
      (8*cutoffFourierBound^2)*
        ((Nat.gcd (∏ i, p i) (∏ j, r j) : ℝ) /
          (Real.sqrt ((∏ i, p i : ℕ) : ℝ) * Real.sqrt ((∏ j, r j : ℕ) : ℝ))) * S := by
  let d : ℕ := ∏ i, p i
  let e : ℕ := ∏ j, r j
  let G : ℝ := (Nat.gcd d e : ℝ)/(Real.sqrt d*Real.sqrt e)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let c : ZMod d := -((v*w^2 : ℕ) : ZMod d)*mInv
  let c' : ZMod e := -((v*w'^2 : ℕ) : ZMod e)*mInv'
  let α : ℝ := (h+θ)*v*((w:ℝ)^2/d-(w':ℝ)^2/e)
  have hlocal := centered_correlation_smoothed_bound p r hp hr hcop hcor A B c c'
    α (S : ℤ) S hR v w w' (H := (S : ℝ)) le_rfl (by simp)
  have heq : (∑ n ∈ Finset.range S,
      quadraticCrossMode d e (centeredQuadraticAmplitude p hcop A mInv (S+n) v)
        (centeredQuadraticAmplitude r hcor B mInv' (S+n) v) (S+n) v w w' R (h+θ)) =
      ∑ n ∈ Finset.range S,
        (centeredCorrelation p r hcop hcor A B c c'
          (((S : ℤ)+(n : ℤ) : ℤ) : ZMod (Nat.lcm d e)) *
          weylPhase (((S : ℝ)+n)*α)) *
        quadraticCutoffWeight R d e v w w' ((S : ℝ)+n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [quadraticCrossMode, centeredQuadraticAmplitude_eq_scalar,
      centeredCorrelation, Int.cast_add, Int.cast_natCast, Nat.cast_add, map_add, map_natCast]
    rfl
  rw [heq]
  calc
    _ ≤ 2*cutoffFourierBound^2*G*(2*S+2*Nat.lcm d e*(harmonic (Nat.lcm d e) : ℝ)) := hlocal
    _ ≤ 2*cutoffFourierBound^2*G*(4*S) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hperiod]
    _ = (8*cutoffFourierBound^2)*G*S := by ring

end Ostmann.QuadraticCenter

end

end OAI
