import OAI.NumberTheory.TwoPoint.Walks.PartialTupleProfiles
import OAI.NumberTheory.TwoPoint.Walks.TupleSliceSupport

namespace OAI

/-! A partial-centering bin saves L^(-21/20) with exactly the reciprocal
mass of the retained supply products. The scale exponent is absolute. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma indexed_rescaled_prefix_bound {α : Type*} [Fintype α]
    (u : α → ℕ) (F : α → ℕ → ℂ) (X : ℕ) (E : ℝ)
    (hX : 0 < X) (hE : 0 ≤ E) (hu : ∀ a, 0 < u a)
    (hF : ∀ a, ‖positivePrefix (F a) (X / u a) / ((X / u a : ℕ) : ℂ)‖ ≤ E) :
    ‖(∑ a, positivePrefix (F a) (X / u a)) / (X : ℂ)‖ ≤
      E * ∑ a, 1 / (u a : ℝ) := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  rw [sum_div]
  calc
    _ ≤ ∑ a, ‖positivePrefix (F a) (X / u a) / (X : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ a, E * (1 / (u a : ℝ)) := by
      apply sum_le_sum
      intro a _
      have hup : (0 : ℝ) < u a := by exact_mod_cast hu a
      have hb := prefix_norm_of_average_bound (F a) (X / u a) E (hF a)
      have hratio : ((X / u a : ℕ) : ℝ) ≤ (X : ℝ) / u a := Nat.cast_div_le
      have hp := hb.trans (mul_le_mul_of_nonneg_right hratio hE)
      rw [norm_div, Complex.norm_natCast]
      calc
        _ ≤ (((X : ℝ) / u a) * E) / X := div_le_div_of_nonneg_right hp hXp.le
        _ = _ := by field_simp
    _ = _ := by rw [mul_sum]

lemma retained_tuple_reciprocal_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (I : Finset (Fin J)) (q : ℕ) :
    (∑ y : (j : {j // j ∉ I}) → P j,
      1 / ((q : ℝ) * ∏ j, ((y j).val : ℝ))) =
      (1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j) := by
  calc
    _ = (1 / (q : ℝ)) *
        ∑ y : (j : {j // j ∉ I}) → P j, ∏ j, ((y j).val : ℝ)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      simp only [one_div, mul_inv_rev, prod_inv_distrib]
      ring
    _ = _ := by
      congr 1
      exact (Fintype.prod_sum (fun j : {j // j ∉ I} =>
        fun p : P j => (p.val : ℝ)⁻¹)).symm

theorem quantitative_partial_tuple_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (J : ℕ) (P : Fin J → Finset ℕ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j k, k ≠ j → Disjoint (P j) (P k)) →
      ∀ (I : Finset (Fin J)) (q X l : ℕ) [NeZero l],
      0 < q → 0 < X →
      ∀ (eligible : ℕ → ℕ → Prop) (b : ZMod l) (M : ℝ) (τ : ℝ),
      0 < τ → τ < 2 →
      (∀ y : (j : {j // j ∉ I}) → P j,
        IsUnit ((q * ∏ j, (y j).val : ℕ) : ZMod l)) →
      (∀ y : (j : {j // j ∉ I}) → P j,
        Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤
          ((X / (q * ∏ j, (y j).val) : ℕ) : ℝ)) →
      (∀ y : (j : {j // j ∉ I}) → P j, ∀ z ∈ primeTupleSlice P I,
        eligible ((∏ j, (y j).val) * z) q →
          M / (q * ∏ j, ((y j).val : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ τ * (M / (q * ∏ j, ((y j).val : ℝ))) ∧
          Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧
          (z : ℝ) ≤ Real.exp (2 * L) ∧
          avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖positivePrefix (tuplePartialProfile P I q eligible l b h) X / (X : ℂ)‖ ≤
        ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) *
          ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j)) := by
  obtain ⟨C, hC, hb⟩ := quantitative_residue_bin hM hMRT h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro J P hp hd I q X l _ hq hX eligible b M τ hτ hτtwo hunit hY hZ
  rw [tuplePartialProfile_prefix P hp hd I q hq eligible l b h X hunit]
  have hu (y : (j : {j // j ∉ I}) → P j) : 0 < q * ∏ j, (y j).val :=
    Nat.mul_pos hq (prod_pos fun j _ => (hp j _ (y j).property).pos)
  have he := indexed_rescaled_prefix_bound
    (fun y : (j : {j // j ∉ I}) → P j => q * ∏ j, (y j).val)
    (fun y => residueScaledRoughProfile l b
      ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
    X ((l : ℝ) * C * L ^ (-21 / 20 : ℝ)) hX (by positivity) hu
    (fun y => hb _ l (hY y) b (M / (q * ∏ j, ((y j).val : ℝ))) τ hτ hτtwo _
      (fun z hz => hZ y z (mem_filter.mp hz).1 (mem_filter.mp hz).2))
  simpa only [Nat.cast_mul, Nat.cast_prod, retained_tuple_reciprocal_sum] using he

end TwoPointCorrelations

end OAI
