import OAI.NumberTheory.TwoPointCorrelations.MRTFrequencyCover
import OAI.NumberTheory.TwoPointCorrelations.MRTRealPrimeBins

namespace OAI

/-! The coarse energy on a later MRT class, summed over actual large
preceding-bin witnesses. The Ramaré error is deliberately absent here:
it is charged once, before this finite cover is used. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_witnessed_cofactor_energy {κ β : Type*}
    (K : Finset κ) (Q : κ → ℝ → ℂ) (A lower : κ → ℝ)
    (P : Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N : ℕ} (hN : 0 < N) (hlower : ∀ k ∈ K, 1 ≤ lower k)
    (B : Finset β) (Pprev : β → Finset ℕ) (Y : β → ℝ)
    (hY : ∀ b ∈ B, 1 < Y b)
    (hPprev : ∀ b ∈ B, ∀ p ∈ Pprev b, p.Prime)
    (hprevbin : ∀ b ∈ B, ∀ p ∈ Pprev b, Y b ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y b)
    (a : β → ℕ → ℂ) (ha : ∀ b ∈ B, ∀ p ∈ Pprev b, ‖a b p‖ ≤ 1)
    (V : β → ℝ) (hV : ∀ b ∈ B, 0 < V b)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : MeasurableSet S)
    (hST : S ⊆ Set.Ioc (-T) T) (hQ : ∀ k ∈ K, Continuous (Q k))
    (hsmall : ∀ k ∈ K, ∀ t ∈ S, ‖Q k t‖ ≤ A k)
    (hcover : ∀ t ∈ S, ∃ b ∈ B, V b ≤
      ‖mrtExponentialPolynomial (Pprev b) (fun p => a b p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in S, ‖∑ k ∈ K, Q k t * mrtCofactorPolynomial P F N (lower k) t‖ ^ 2) ≤
      ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
        ((16 * Real.exp 10 *
          (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y b⌉₊ (lower k) + 1) * ⌈Y b⌉₊) *
            ((mrtAmplificationOrder ⌈Y b⌉₊ (lower k)).factorial : ℝ) ^ 2) /
          (V b) ^ (2 * mrtAmplificationOrder ⌈Y b⌉₊ (lower k))) := by
  let R : κ → ℝ → ℂ := fun k => mrtCofactorPolynomial P F N (lower k)
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * R k t
  let E : β → Set ℝ := fun b => {t | V b ≤
    ‖mrtExponentialPolynomial (Pprev b) (fun p => a b p / (p : ℂ))
      (fun p => -Real.log (p : ℝ)) t‖}
  have hR (k : κ) (hk : k ∈ K) : Continuous (R k) := by
    have he : R k = mrtExponentialPolynomial
        (Ioc ⌊(N : ℝ) / lower k⌋₊ ⌊(2 * N : ℝ) / lower k⌋₊)
        (fun n => (F n / ((finitePrimeDivisorCount P n + 1 : ℕ) : ℂ)) / (n : ℂ))
        (fun n => -Real.log (n : ℝ)) :=
      funext (mrt_cofactor_exponential_polynomial P F N (hlower k hk))
    rw [he]
    exact mrtExponentialPolynomial_continuous _ _ _
  have hG : Continuous G := continuous_finsetSum K (fun k hk => (hQ k hk).mul (hR k hk))
  have hE (b : β) : MeasurableSet (E b) :=
    (isClosed_le continuous_const
      (mrtExponentialPolynomial_continuous _ _ _).norm).measurableSet
  have hiG : IntegrableOn (fun t => ‖G t‖ ^ 2) S :=
    mrt_continuous_square_integrable hG hT.le hST
  change (∫ t in S, ‖G t‖ ^ 2) ≤ _
  apply (mrt_nonnegative_integral_cover B E (fun b _ => hE b) hS
    (fun t => ‖G t‖ ^ 2) hiG (fun _ _ => sq_nonneg _) hcover).trans
  apply sum_le_sum
  intro b hb
  change (∫ t in S ∩ E b, ‖∑ k ∈ K, Q k t * R k t‖ ^ 2) ≤ _
  have hsub : S ∩ E b ⊆ Set.Ioc (-T) T := Set.inter_subset_left.trans hST
  apply (mrt_restricted_product_sum_energy_local K Q R hR A hT.le hsub
    (fun k hk t ht => hsmall k hk t ht.1)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact mrt_real_short_class_cofactor_energy (Pprev b) P (hPprev b hb) (hY b hb)
    (hprevbin b hb) hN (a b) (ha b hb) F hF (hlower k hk) hT (hV b hb)
    hsub (fun t ht => ht.2)

end TwoPointCorrelations

end OAI
