import OAI.NumberTheory.TwoPoint.Bounds.CenteredTupleProfiles
import OAI.NumberTheory.TwoPoint.Walks.TupleSliceSupport

namespace OAI

/-! Exact finite summation of partial-centering errors. Each removed
supply subset costs its retained reciprocal mass, never its number of primes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma positivePrefix_sum_finite {α : Type*} (S : Finset α) (F : α → ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun n => ∑ a ∈ S, F a n) X =
      ∑ a ∈ S, positivePrefix (F a) X := by
  unfold positivePrefix
  exact sum_comm

lemma tupleCenteredProfile_nonraw_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (q : ℕ) (hcop : ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h X : ℕ) :
    (positivePrefix (tupleCenteredProfile P q eligible l b h) X -
      positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X) / (X : ℂ) =
      ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
        (-1 : ℂ) ^ I.card *
          (positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ)) := by
  have hp : positivePrefix (fun n => tupleCenteredProfile P q eligible l b h n -
      tuplePartialProfile P ∅ q eligible l b h n) X =
      positivePrefix (tupleCenteredProfile P q eligible l b h) X -
        positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X := by
    simp only [positivePrefix, sum_sub_distrib]
  rw [← hp]
  simp_rw [tupleCenteredProfile_nonraw P hprime hdisjoint q hcop eligible l b h]
  rw [positivePrefix_sum_finite, sum_div]
  apply sum_congr rfl
  intro I _
  rw [positivePrefix_const_mul]
  ring

lemma complement_product_le {J : ℕ} (V : Fin J → ℝ) (hV : ∀ j, 1 ≤ V j)
    (I : Finset (Fin J)) : (∏ j : {j // j ∉ I}, V j) ≤ ∏ j, V j := by
  rw [← prod_subtype (p := fun j : Fin J => j ∉ I) (F := inferInstance) (univ \ I) (by simp) V]
  exact prod_le_prod_of_subset_of_one_le₀ (subset_univ _)
    (fun j _ => zero_le_one.trans (hV j)) (fun j _ _ => hV j)

lemma partial_centering_sum_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hmass : ∀ j, 1 ≤ primeHarmonicMass (P j))
    (Q : Finset ℕ) (weight : ℕ → ℝ) (hweight : ∀ q ∈ Q, 0 ≤ weight q)
    (hcop : ∀ q ∈ Q, ∀ j, ∀ p ∈ P j, q.Coprime p)
    (eligible : ℕ → ℕ → Prop) (l : ℕ) [NeZero l] (b : ZMod l) (h X : ℕ)
    (E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ q ∈ Q, ∀ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
      ‖positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ)‖ ≤
        E * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j))) :
    ‖∑ q ∈ Q, (weight q : ℂ) *
      ((positivePrefix (tupleCenteredProfile P q eligible l b h) X -
        positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X) / (X : ℂ))‖ ≤
      E * (2 : ℝ) ^ J * (∑ q ∈ Q, weight q / (q : ℝ)) *
        ∏ j, primeHarmonicMass (P j) := by
  let V := ∏ j, primeHarmonicMass (P j)
  have hV : 0 ≤ V := prod_nonneg fun j _ => zero_le_one.trans (hmass j)
  have hc : (((univ : Finset (Fin J)).powerset.filter Finset.Nonempty).card : ℝ) ≤
      (2 : ℝ) ^ J := by
    have hn := card_le_card (filter_subset (s := (univ : Finset (Fin J)).powerset)
      (p := Finset.Nonempty))
    simpa only [card_powerset, card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
      (show (((univ : Finset (Fin J)).powerset.filter Finset.Nonempty).card : ℝ) ≤
        ((univ : Finset (Fin J)).powerset.card : ℝ) by exact_mod_cast hn)
  calc
    _ ≤ ∑ q ∈ Q, ‖(weight q : ℂ) *
        ((positivePrefix (tupleCenteredProfile P q eligible l b h) X -
          positivePrefix (tuplePartialProfile P ∅ q eligible l b h) X) / (X : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, weight q * ((2 : ℝ) ^ J * (E * (1 / (q : ℝ)) * V)) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight q hq),
        tupleCenteredProfile_nonraw_prefix P hprime hdisjoint q (hcop q hq)]
      apply mul_le_mul_of_nonneg_left _ (hweight q hq)
      calc
        _ ≤ ∑ I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            ‖(-1 : ℂ) ^ I.card *
              (positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _I ∈ (univ : Finset (Fin J)).powerset.filter Finset.Nonempty,
            E * (1 / (q : ℝ)) * V := by
          apply sum_le_sum
          intro I hI
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          apply (hbound q hq I hI).trans
          have hv := complement_product_le (fun j => primeHarmonicMass (P j)) hmass I
          dsimp only [V]
          calc
            _ = (E * (1 / (q : ℝ))) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
        _ ≤ (2 : ℝ) ^ J * (E * (1 / (q : ℝ)) * V) := by
          simp only [sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro q _
      dsimp only [V]
      ring

end TwoPointCorrelations

end OAI
