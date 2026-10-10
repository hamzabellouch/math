import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalCostData
import OAI.NumberTheory.Ostmann.Construction.ScheduledFullMatchingGraph

namespace OAI

/-! # Actual matched pair counts at the linear constituent-size scale -/
namespace Ostmann
open scoped Classical

theorem constituent_retained_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n S : ℕ)
    (hsize : ∀ i, size i ≤ S) :
    Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) ≤
        3 ^ n * Fintype.card I * S := by
  have hcard : Fintype.card (Σ i, Fin (size i)) ≤ Fintype.card I * S := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (f := size) (g := fun _ => S)
        (fun i _ => hsize i))
  apply (Fintype.card_le_of_injective _
    (scheduledRetainedEmbedding (fun i : Σ a, Fin (size a) => role i.1) n).injective).trans
  apply (copyScheduleAtoms_card_le _ n).trans
  simpa only [mul_assoc] using Nat.mul_le_mul_left (3 ^ n) hcard

theorem constituent_retained_word_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n S A : ℕ)
    (hsize : ∀ i, size i ≤ S) :
    Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n) + 1 ≤
      2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by
  have hc := constituent_retained_card_le role size n S hsize
  rw [Fintype.card_sum] at hc
  have he : 2 * 3 ^ n * Fintype.card I * S = 2 * (3 ^ n * Fintype.card I * S) := by ring
  rw [he]
  omega

theorem constituent_matched_top_count {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let W := insertedConstituentWord role size n
    let W' := fun v => List.map (insertedConstituentPerm role size n e) (W v)
    (constituentPrimePairChecks (CopyScheduleH ρ n ⊕ CopyScheduleY ρ n) ++
      atomPairChecks W ++ atomPairChecks W').length ≤ 3 * (3 ^ n * Fintype.card I * S) ^ 2 := by
  intro ρ W W'
  have hcard : Fintype.card (Σ i, Fin (size i)) ≤ Fintype.card I * S := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (f := size) (g := fun _ => S)
        (fun i _ => hsize i))
  have hK : Fintype.card (CopyScheduleH ρ n ⊕ CopyScheduleY ρ n) ≤
      3 ^ n * Fintype.card I * S := by
    apply (Fintype.card_le_of_injective _ (scheduledRetainedEmbedding ρ n).injective).trans
    apply (copyScheduleAtoms_card_le ρ n).trans
    simpa only [mul_assoc] using Nat.mul_le_mul_left (3 ^ n) hcard
  have hc := constituent_pair_top_count role size n e S hS hsize
  have hp := Nat.pow_le_pow_left hK 2
  dsimp only [ρ] at hp
  exact hc.trans (by omega)

theorem constituent_matched_linear_counts {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (S : ℕ) (s m : ℝ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hs : 0 ≤ s) (hm : 0 ≤ m) (hSm : (S : ℝ) ≤ s * (1 + m)) :
    let W := insertedConstituentWord role size n
    let W' := fun v => List.map (insertedConstituentPerm role size n e) (W v)
    let a := constituentFinalCountRate (Fintype.card I) n s
    (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
        a * (1 + m) ∧
    ((constituentPrimePairChecks (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤ a * (1 + m) ^ 2 := by
  intro W W' a
  have hp := constituent_pair_prime_count role size n e S hS hsize
  have hc := constituent_matched_top_count role size n e S hS hsize
  have hrealp : (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
      2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S * (2 ^ n - 1 : ℕ) := by
    calc
      _ ≤ 2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ)) := by
        exact_mod_cast hp
      _ = _ := by ring
  have hrealc : ((constituentPrimePairChecks (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
      CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
      3 * ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S) ^ 2 := by
    exact_mod_cast hc
  have ha1 : 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) ≤ a := by
    dsimp [a, constituentFinalCountRate]
    linarith [sq_nonneg ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * s)]
  have ha2 : 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2 ≤ a := by
    dsimp [a, constituentFinalCountRate]
    have hh : 0 ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) := by positivity
    linarith
  constructor
  · calc
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ) := hrealp
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m)) * (2 ^ n - 1 : ℕ) := by gcongr
      _ = (2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ)) * (1 + m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha1 (by linarith)
  · calc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S) ^ 2 := hrealc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m))) ^ 2 := by gcongr
      _ = (3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2) * (1 + m) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)

end Ostmann

end OAI
