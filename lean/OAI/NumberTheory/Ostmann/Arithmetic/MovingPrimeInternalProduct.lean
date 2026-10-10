import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeProbabilityError
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeIndexedProbability
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSquareError

namespace OAI

/-! # Relative square error under the original two-prime law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingInternalPrimeLineProbability {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] : ℝ :=
  internalLineProbability false
    (fun j => MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).a)
    (fun j => MovingSlotReversal.naturalReduction p value
      (movingPrimeOccurrenceLine value T p j).b)

theorem movingInternalPrimeLineProbability_nonneg {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) [Fact p.Prime] :
    0 ≤ movingInternalPrimeLineProbability value T p := internalLineProbability_nonneg _ _ _

theorem movingInternalPrimeLineProbability_le_scalar {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (base : MovingPrimeOccurrences value T p) :
    movingInternalPrimeLineProbability value T p ≤ internalLineScalar false p := by
  unfold movingInternalPrimeLineProbability
  rw [movingInternalPrimeProbability_eq_flags tier value hprime hdisjoint T hlevels p hf base]
  exact internalLineFlagWeight_le_scalar _ _ _

theorem movingPrimeRepresentativeProduct_error {σ C : Type*} [Fintype C]
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hlevels : ∀ b, (T b).Levels tier)
    (rep : C → σ) (base : ∀ c, MovingPairRepresentativeOccurrences T (rep c))
    (hf : ∀ c b, (T b).Frequencies (fun s => (s : ZMod (value (rep c))) ≠ 0))
    (V : ℝ) (hsize : ∀ c, Real.exp V ≤ value (rep c)) :
    letI : ∀ c, Fact (value (rep c)).Prime := fun _ => ⟨hprime _⟩
    ‖(∏ c, movingInternalPrimeAverage value T (value (rep c))) -
      ∏ c, (movingInternalPrimeLineProbability value T (value (rep c)) : ℂ)‖ ≤
        ((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) *
          ∏ c, internalLineScalar false (value (rep c)) := by
  let _ : ∀ c, Fact (value (rep c)).Prime := fun _ => ⟨hprime _⟩
  have hprob (c) : 0 ≤ movingInternalPrimeLineProbability value T (value (rep c)) :=
    movingInternalPrimeLineProbability_nonneg value T _
  have hline (c) : movingInternalPrimeLineProbability value T (value (rep c)) ≤
      internalLineScalar false (value (rep c)) := by
    let j : MovingPrimeOccurrences value T (value (rep c)) :=
      ⟨(base c).1, ⟨(base c).2.val, ⟨rep c, (base c).2.property, rfl⟩⟩⟩
    exact movingInternalPrimeLineProbability_le_scalar tier value hprime hdisjoint T hlevels _ (hf c) j
  have hs : (∑ c, (value (rep c) : ℝ)⁻¹) ≤ (Fintype.card C : ℝ) * Real.exp (-V) := by
    calc
      _ ≤ ∑ _c : C, Real.exp (-V) := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos V) (hsize c)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h := finite_relative_product_error (Finset.univ : Finset C)
    (fun c => movingInternalPrimeAverage value T (value (rep c)))
    (fun c => (movingInternalPrimeLineProbability value T (value (rep c)) : ℂ))
    (fun c => movingInternalPrimeLineProbability value T (value (rep c)))
    (fun c => 2 * (2 ^ n - 1 : ℕ) / (value (rep c) : ℝ))
    (fun c _ => hprob c) (fun c _ => by positivity)
    (fun c _ => movingInternalPrimeAverage_probability_norm_le value T _)
    (fun c _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hprob c)])
    (fun c _ => movingInternalPrimeAverage_probability_error tier value hprime hdisjoint T hlevels _ (hf c))
  have hp : (∏ c, movingInternalPrimeLineProbability value T (value (rep c))) ≤
      ∏ c, internalLineScalar false (value (rep c)) :=
    Finset.prod_le_prod₀ (fun c _ => hprob c) (fun c _ => hline c)
  have hk : (∑ c, 2 * (2 ^ n - 1 : ℕ) / (value (rep c) : ℝ)) ≤
      (2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V) := by
    simp only [div_eq_mul_inv, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
  exact h.trans (mul_le_mul hk hp (Finset.prod_nonneg (fun c _ => hprob c)) (by positivity))

end Ostmann

end OAI
