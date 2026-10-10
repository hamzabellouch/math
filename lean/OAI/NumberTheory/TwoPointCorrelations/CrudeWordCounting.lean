import OAI.NumberTheory.TwoPointCorrelations.ColumnRepresentatives
import OAI.NumberTheory.TwoPointCorrelations.FiniteProbability
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Finite descriptions used by the reciprocal crude count. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- A partition is recorded by a representative slot for each slot. -/
noncomputable def slotPartitionCode (N : ℕ) (s : Setoid (Fin N)) : Fin N → Fin N :=
  columnRepresentative (fun i => @Quotient.mk _ s i) ∅

lemma slotPartitionCode_eq_iff (N : ℕ) (s : Setoid (Fin N)) (i j : Fin N) :
    slotPartitionCode N s i = slotPartitionCode N s j ↔ s.r i j := by
  exact (columnRepresentative_eq_iff (fun i => @Quotient.mk _ s i) ∅ i j).trans Quotient.eq

lemma slotPartitionCode_injective (N : ℕ) : Function.Injective (slotPartitionCode N) := by
  intro s t h
  apply Setoid.ext
  intro i j
  rw [← slotPartitionCode_eq_iff N s, ← slotPartitionCode_eq_iff N t, h]

/-- The elementary Bell-number bound used in `q:crude-count`. -/
theorem card_slotPartitions_le (N : ℕ) : Nat.card (Setoid (Fin N)) ≤ N ^ N := by
  have h := Nat.card_le_card_of_injective (slotPartitionCode N) (slotPartitionCode_injective N)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h

/-- Signs, a partition code, bounded records per slot, and lit designations. -/
abbrev CrudeWordCode (R N D : ℕ) :=
  (Fin R → Bool) × (Fin N → Fin N) × (Fin N → Fin D) × (Fin N → Bool)

theorem card_crudeWordCode (R N D : ℕ) :
    Fintype.card (CrudeWordCode R N D) = 2 ^ R * (N ^ N * (D ^ N * 2 ^ N)) := by
  simp only [CrudeWordCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]

/-- A column and an ordered list of candidate lit pairs have at most this
many descriptions. Repeated or invalid descriptions only enlarge the bound. -/
abbrev RankPairChoices (J R r : ℕ) := Fin J × (Fin r → Fin R × Fin R)

theorem card_rankPairChoices (J R r : ℕ) :
    Fintype.card (RankPairChoices J R r) = J * R ^ (2 * r) := by
  simp only [RankPairChoices, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  congr 1
  rw [← pow_two, ← pow_mul]

/-- A finite union bound for arbitrary events under the concrete finite law. -/
theorem FiniteLaw.probability_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (μ : FiniteLaw A) (E : I → A → Prop) :
    μ.probability (fun x => ∃ i, E i x) ≤ ∑ i, μ.probability (E i) := by
  classical
  unfold FiniteLaw.probability
  rw [← μ.average_sum]
  apply μ.average_mono
  intro x
  by_cases hx : ∃ i, E i x
  · obtain ⟨i, hi⟩ := hx
    simp only [ite_eq_left (show ∃ j, E j x from ⟨i, hi⟩)]
    apply (le_trans ?_ (single_le_sum (f := fun i => if E i x then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)))
    simp [hi]
  · simp only [ite_eq_right hx]
    exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)

/-- Uniform bounds may be summed over the explicit column/pair records. -/
theorem rank_pair_union_bound {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (J R r : ℕ) (E : RankPairChoices J R r → A → Prop)
    (B : ℝ) (hB : ∀ c, μ.probability (E c) ≤ B) :
    μ.probability (fun x => ∃ c, E c x) ≤ (J * R ^ (2 * r) : ℕ) * B := by
  apply (μ.probability_exists_le E).trans
  calc
    _ ≤ ∑ _c : RankPairChoices J R r, B := sum_le_sum (fun c _ => hB c)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, card_rankPairChoices]

lemma card_crudeWordCode_exp (R N D : ℕ) :
    (Fintype.card (CrudeWordCode R N D) : ℝ) ≤
      Real.exp (R * Real.log 2 + N * Real.log (N + 1) +
        N * Real.log (D + 1) + N * Real.log 2) := by
  have hp (n k : ℕ) : (n : ℝ) ^ k ≤ Real.exp ((k : ℝ) * Real.log (n + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < n + 1)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k
  have htwo (k : ℕ) : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [card_crudeWordCode]
  push_cast
  calc
    _ ≤ (2 : ℝ) ^ R * (Real.exp ((N : ℝ) * Real.log (N + 1)) *
        (Real.exp ((N : ℝ) * Real.log (D + 1)) * 2 ^ N)) := by
      gcongr
      · exact hp N N
      · exact hp D N
    _ = _ := by rw [htwo, htwo, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The slot bound `N ≤ C R log L` and polynomial record alphabets yield
the manuscript's `exp (O(R log² L))` count with an explicit coefficient. -/
theorem crudeWordCode_bound (R N D d : ℕ) (L C : ℝ)
    (hL : 1 ≤ Real.log L) (hRN : R ≤ N)
    (hslots : (N : ℝ) ≤ C * R * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hD : (D : ℝ) + 1 ≤ L ^ d) :
    (Fintype.card (CrudeWordCode R N D) : ℝ) ≤
      Real.exp (((d : ℝ) + 4) * C * R * (Real.log L) ^ 2) := by
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2 : Real.log 2 ≤ Real.log L := htwo.trans hL
  have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < N + 1) hN
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogD : Real.log ((D : ℝ) + 1) ≤ (d : ℝ) * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < D + 1) hD
    simpa only [Real.log_pow] using h
  have h1 : (R : ℝ) * Real.log 2 ≤ N * Real.log L :=
    mul_le_mul (by exact_mod_cast hRN) hlog2 (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hlogN (show (0 : ℝ) ≤ N by positivity)
  have h3 := mul_le_mul_of_nonneg_left hlogD (show (0 : ℝ) ≤ N by positivity)
  have h4 := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ N by positivity)
  have h5 := mul_le_mul_of_nonneg_right hslots (show 0 ≤ Real.log L by linarith)
  apply (card_crudeWordCode_exp R N D).trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) + 4 by positivity)
    (sub_nonneg.mpr h5)]

end TwoPointCorrelations

end OAI
