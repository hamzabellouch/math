import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped BigOperators

variable {ι α : Type*} [instDecidableEqι : DecidableEq ι] [DecidableEq α]

private theorem sum_membership_indicator
    (A U : Finset α) (hAU : A ⊆ U) :
    (∑ x ∈ U, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
  have hfilter : U.filter (fun x => x ∈ A) = A := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨hAU hx, hx⟩⟩
  rw [Finset.sum_boole, hfilter]

private theorem sum_overlap_multiplicity
    (I : Finset ι) (T : ι → Finset α) (U : Finset α)
    (hTU : ∀ i ∈ I, T i ⊆ U) :
    (∑ x ∈ U, ∑ i ∈ I, if x ∈ T i then (1 : ℝ) else 0) =
      ∑ i ∈ I, ((T i).card : ℝ) := let _ := instDecidableEqι; by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_membership_indicator (T i) U (hTU i hi)

private theorem sum_sq_overlap_multiplicity
    (I : Finset ι) (T : ι → Finset α) (U : Finset α)
    (hTU : ∀ i ∈ I, T i ⊆ U) :
    (∑ x ∈ U, (∑ i ∈ I, if x ∈ T i then (1 : ℝ) else 0) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, ((T i ∩ T j).card : ℝ) := let _ := instDecidableEqι; by
  calc
    (∑ x ∈ U, (∑ i ∈ I, if x ∈ T i then (1 : ℝ) else 0) ^ 2) =
        ∑ x ∈ U, ∑ i ∈ I, ∑ j ∈ I,
          (if x ∈ T i then (1 : ℝ) else 0) *
          (if x ∈ T j then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ U,
          (if x ∈ T i then (1 : ℝ) else 0) *
          (if x ∈ T j then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ i ∈ I, ∑ j ∈ I, ((T i ∩ T j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ x ∈ U,
            (if x ∈ T i then (1 : ℝ) else 0) *
            (if x ∈ T j then (1 : ℝ) else 0)) =
            ∑ x ∈ U, if x ∈ T i ∩ T j then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxi : x ∈ T i <;> by_cases hxj : x ∈ T j <;>
            simp [Finset.mem_inter, hxi, hxj]
        _ = ((T i ∩ T j).card : ℝ) := by
          apply sum_membership_indicator
          intro x hx
          exact hTU i hi (Finset.mem_inter.mp hx).1

private theorem overlap_energy_lower {β : Type*} (U : Finset β)
    (r : β → ℝ) (s K R : ℝ) (hs : 0 < s) (hK : 0 < K)
    (hmass : (∑ x ∈ U, r x) = s ^ 2)
    (henergy : (∑ x ∈ U, r x ^ 2) = R)
    (hU : (U.card : ℝ) ≤ K * s) : s ^ 3 / K ≤ R := by
  have hR : 0 ≤ R := by
    rw [← henergy]
    exact Finset.sum_nonneg (fun x _ => sq_nonneg (r x))
  have hcs : (s ^ 2) ^ 2 ≤ (U.card : ℝ) * R := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) r
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
      mul_one, hmass, henergy] using h
  have hscaled : (s ^ 2) ^ 2 ≤ (K * s) * R :=
    hcs.trans (mul_le_mul_of_nonneg_right hU hR)
  apply (div_le_iff₀ hK).2
  refine le_of_mul_le_mul_left (a := s) ?_ hs
  calc
    s * s ^ 3 = (s ^ 2) ^ 2 := by ring
    _ ≤ (K * s) * R := hscaled
    _ = s * (R * K) := by ring

private theorem popular_card_lower (I : Finset ι) (f : ι → ℝ)
    (n a : ℝ) (hn : 0 < n) (ha : 0 ≤ a)
    (hcard : (I.card : ℝ) = n)
    (hupper : ∀ i ∈ I, f i ≤ n)
    (hsum : 2 * n * a ≤ ∑ i ∈ I, f i) :
    a ≤ ((I.filter fun i => a ≤ f i).card : ℝ) := let _ := instDecidableEqι; by
  classical
  have hbound : (∑ i ∈ I, f i) ≤
      ((I.filter fun i => a ≤ f i).card : ℝ) * n + n * a := by
    calc
      (∑ i ∈ I, f i) ≤ ∑ i ∈ I, ((if a ≤ f i then n else 0) + a) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : a ≤ f i
        · rw [ite_eq_left h]
          exact (hupper i hi).trans (le_add_of_nonneg_right ha)
        · rw [ite_eq_right h, zero_add]
          exact (lt_of_not_ge h).le
      _ = ((I.filter fun i => a ≤ f i).card : ℝ) * n + n * a := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_filter,
          Finset.sum_const, nsmul_eq_mul, hcard]
  refine le_of_mul_le_mul_left (a := n) ?_ hn
  nlinarith only [hsum, hbound]

theorem exists_popular_intersections
    (I : Finset ι) (T : ι → Finset α) (U : Finset α) (s : ℕ) (K : ℝ)
    (hI : I.card = s) (hne : I.Nonempty)
    (hT : ∀ i ∈ I, (T i).card = s)
    (hTU : ∀ i ∈ I, T i ⊆ U)
    (hU : (U.card : ℝ) ≤ K * s) (hK : 2 ≤ K) :
    ∃ b ∈ I, ∃ A : Finset ι, A ⊆ I ∧ (s : ℝ) / (2 * K) ≤ A.card ∧
      ∀ a ∈ A, (s : ℝ) / (2 * K) ≤ (T a ∩ T b).card := by
  classical
  have hsNat : 0 < s := by simpa only [hI] using Finset.card_pos.mpr hne
  have hs : (0 : ℝ) < s := Nat.cast_pos.mpr hsNat
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_two hK
  let r (x : α) : ℝ := ∑ i ∈ I, if x ∈ T i then 1 else 0
  let R : ℝ := ∑ i ∈ I, ∑ j ∈ I, ((T i ∩ T j).card : ℝ)
  let row (b : ι) : ℝ := ∑ a ∈ I, ((T a ∩ T b).card : ℝ)
  have hmass : (∑ x ∈ U, r x) = (s : ℝ) ^ 2 := by
    calc
      (∑ x ∈ U, r x) = ∑ i ∈ I, ((T i).card : ℝ) :=
        sum_overlap_multiplicity I T U hTU
      _ = ∑ _i ∈ I, (s : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun n : ℕ => (n : ℝ)) (hT i hi)
      _ = (s : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, hI, pow_two]
  have henergy : (∑ x ∈ U, r x ^ 2) = R :=
    sum_sq_overlap_multiplicity I T U hTU
  have hlower : (s : ℝ) ^ 3 / K ≤ R :=
    overlap_energy_lower U r s K R hs hKpos hmass henergy hU
  have hrows : (∑ b ∈ I, row b) = R := by
    dsimp only [row, R]
    exact Finset.sum_comm
  have hmean : (∑ _b ∈ I, (s : ℝ) ^ 2 / K) ≤ ∑ b ∈ I, row b := by
    calc
      (∑ _b ∈ I, (s : ℝ) ^ 2 / K) = (s : ℝ) ^ 3 / K := by
        rw [Finset.sum_const, nsmul_eq_mul, hI]
        ring
      _ ≤ R := hlower
      _ = ∑ b ∈ I, row b := hrows.symm
  obtain ⟨b, hb, hrow⟩ := Finset.exists_le_of_sum_le
    (s := I) (f := fun _ => (s : ℝ) ^ 2 / K) (g := row) hne hmean
  let A := I.filter (fun a => (s : ℝ) / (2 * K) ≤ (T a ∩ T b).card)
  refine ⟨b, hb, A, ?_, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).1
  · apply popular_card_lower I (fun a => ((T a ∩ T b).card : ℝ))
      (s : ℝ) ((s : ℝ) / (2 * K)) hs
    · exact div_nonneg hs.le (mul_nonneg zero_le_two hKpos.le)
    · exact congrArg (fun n : ℕ => (n : ℝ)) hI
    · intro a ha
      apply Nat.cast_le.mpr
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (hT a ha)
    · calc
        2 * (s : ℝ) * ((s : ℝ) / (2 * K)) = (s : ℝ) ^ 2 / K := by
          field_simp [ne_of_gt hKpos]
        _ ≤ ∑ a ∈ I, ((T a ∩ T b).card : ℝ) := hrow
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end RyserCoveringCounterexample.Incidence

end OAI
