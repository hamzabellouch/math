import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationModes
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyCounting
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyHighMass

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology ComplexConjugate
open Filter

theorem quadraticCutoffWeight_norm_le (R : ℝ) (d e v w w' : ℕ) (s : ℝ) :
    ‖quadraticCutoffWeight R d e v w w' s‖ ≤ cutoffFourierBound ^ 2 := by
  unfold quadraticCutoffWeight
  rw [norm_mul, Complex.norm_conj]
  calc
    _ ≤ cutoffFourierBound * cutoffFourierBound :=
      mul_le_mul (norm_cutoff_fourier_le _) (norm_cutoff_fourier_le _)
        (norm_nonneg _) cutoffFourierBound_pos.le
    _ = _ := (pow_two _).symm

theorem quadraticCrossMode_norm_le (d e : ℕ) (a b : ℕ → ℂ)
    (s v w w' : ℕ) (R α : ℝ) :
    ‖quadraticCrossMode d e a b s v w w' R α‖ ≤
      ‖a w * conj (b w')‖ * cutoffFourierBound ^ 2 := by
  unfold quadraticCrossMode
  rw [norm_mul, norm_mul, weylPhase_norm, mul_one]
  exact mul_le_mul_of_nonneg_left (quadraticCutoffWeight_norm_le R d e v w w' s) (norm_nonneg _)

theorem high_weight_quadratic_mode_eventually :
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
      ∀ (v w w' : ℕ) (R α : ℝ),
      ‖∑ s ∈ quadraticHighWeightIndices S L u K, ((u ^ s.primeFactors.card : ℝ) : ℂ) *
        quadraticCrossMode (∏ i, p i) (∏ j, r j)
          (centeredQuadraticAmplitude p hcop A mInv s v)
          (centeredQuadraticAmplitude r hcor B mInv' s v) s v w w' R α‖ ≤
        cutoffFourierBound ^ 2 * (S : ℝ) * Real.exp (-10 * K) := by
  filter_upwards [high_weight_transform_product_eventually] with T hT
  intro ι κ instι instκ p r instp instr instD instE hp hr hcop hcor A B mInv mInv'
    S L instL hd he u K hS hSupper hu huupper hK v w w' R α
  have hu0 : 0 ≤ u := (by linarith : 0 < u).le
  let c : ZMod (∏ i, p i) := -((v*w^2 : ℕ) : ZMod (∏ i, p i))*mInv
  let c' : ZMod (∏ j, r j) := -((v*w'^2 : ℕ) : ZMod (∏ j, r j))*mInv'
  have hmass := hT p r hp hr hcop hcor A B c c' S L hd he u K hS hSupper hu huupper hK
  calc
    _ ≤ ∑ s ∈ quadraticHighWeightIndices S L u K,
        ‖((u ^ s.primeFactors.card : ℝ) : ℂ) *
          quadraticCrossMode (∏ i, p i) (∏ j, r j)
            (centeredQuadraticAmplitude p hcop A mInv s v)
            (centeredQuadraticAmplitude r hcor B mInv' s v) s v w w' R α‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ quadraticHighWeightIndices S L u K,
        cutoffFourierBound ^ 2 * (u ^ s.primeFactors.card *
          ‖centeredProductTransform p hcop A (c * (s : ZMod (∏ i, p i))) *
            conj (centeredProductTransform r hcor B (c' * (s : ZMod (∏ j, r j))))‖) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 _)]
      have hh := mul_le_mul_of_nonneg_left
        (quadraticCrossMode_norm_le (∏ i, p i) (∏ j, r j)
          (centeredQuadraticAmplitude p hcop A mInv s v)
          (centeredQuadraticAmplitude r hcor B mInv' s v) s v w w' R α)
        (pow_nonneg hu0 s.primeFactors.card)
      simpa only [centeredQuadraticAmplitude_eq_scalar, c, c', mul_left_comm, mul_comm, mul_assoc] using hh
    _ ≤ cutoffFourierBound ^ 2 * ((S : ℝ) * Real.exp (-10*K)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ = _ := by ring

end Ostmann.QuadraticCenter

end

end OAI
