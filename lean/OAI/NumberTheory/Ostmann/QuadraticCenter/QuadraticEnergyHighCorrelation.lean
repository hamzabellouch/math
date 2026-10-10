import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyHighModes

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology ComplexConjugate
open Filter

theorem centeredQuadraticSum_high_correlation_eventually :
    ∀ᶠ T : ℝ in atTop,
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
      [NeZero (∏ i, p i)] [NeZero (∏ j, r j)],
      (∀ i, (p i).Prime) → (∀ j, (r j).Prime) →
      ∀ (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
      (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
      (A : ∀ i, Finset (ZMod (p i))) (B : ∀ j, Finset (ZMod (r j)))
      (mInv : ZMod (∏ i, p i)) (mInv' : ZMod (∏ j, r j))
      (S L : ℕ) [NeZero L], (∏ i, p i) ∣ L → (∏ j, r j) ∣ L → ∀ (u K : ℝ),
      2 * L ^ 2 ≤ S → (S : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      ∀ (v : ℕ), 0 < v → ∀ (R h θ : ℝ), 0 < R →
      ‖∑ s ∈ quadraticHighWeightIndices S L u K, ((u ^ s.primeFactors.card : ℝ) : ℂ) *
        (centeredQuadraticSum p hcop A mInv s v 1 R h θ *
          conj (centeredQuadraticSum r hcor B mInv' s v 1 R h θ) / (s : ℂ))‖ ≤
        cutoffFourierBound ^ 2 * Real.exp (-10 * K) := by
  filter_upwards [high_weight_quadratic_mode_eventually] with T hT
  intro ι κ instι instκ p r instp instr instD instE hp hr hcop hcor A B mInv mInv'
    S L instL hd he u K hS hSupper hu huupper hK v hv R h θ hR
  have hSpos : 0 < S := (Nat.mul_pos (by decide : 0 < 2)
    (pow_pos (Nat.pos_of_neZero L) 2)).trans_le hS
  let W := quadraticHighWeightIndices S L u K
  let weight : ℕ → ℂ := fun s => if s ∈ W then ((u ^ s.primeFactors.card : ℝ) : ℂ) else 0
  have heq (f : ℕ → ℂ) :
      (∑ n ∈ Finset.range S, weight (S+n) * f (S+n)) =
        ∑ s ∈ W, ((u ^ s.primeFactors.card : ℝ) : ℂ) * f s := by
    simp only [weight, ite_mul, zero_mul]
    exact sum_range_dyadic_indicator (A := ℂ) S W (Finset.filter_subset _ _)
      (fun s => ((u ^ s.primeFactors.card : ℝ) : ℂ) * f s)
  have hc := positiveQuadraticSum_weighted_dyadic_bound
    (d := ∏ i, p i) (e := ∏ j, r j) (S := S) (v := v)
    (fun s => centeredQuadraticAmplitude p hcop A mInv s v)
    (fun s => centeredQuadraticAmplitude r hcor B mInv' s v)
    weight (R := R) (B := cutoffFourierBound ^ 2 * Real.exp (-10*K)) (h+θ)
    hSpos hv hR (by positivity) (fun w w' => ?_)
  · rw [heq (fun s => positiveQuadraticSum (∏ i, p i)
        (centeredQuadraticAmplitude p hcop A mInv s v) s v R (h+θ) *
        conj (positiveQuadraticSum (∏ j, r j)
          (centeredQuadraticAmplitude r hcor B mInv' s v) s v R (h+θ)) / (s : ℂ))] at hc
    exact hc
  · rw [heq (fun s => quadraticCrossMode (∏ i, p i) (∏ j, r j)
        (centeredQuadraticAmplitude p hcop A mInv s v)
        (centeredQuadraticAmplitude r hcor B mInv' s v) s v w w' R (h+θ))]
    have hm := hT p r hp hr hcop hcor A B mInv mInv' S L hd he u K
      hS hSupper hu huupper hK v w w' R (h+θ)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm

end Ostmann.QuadraticCenter

end

end OAI
