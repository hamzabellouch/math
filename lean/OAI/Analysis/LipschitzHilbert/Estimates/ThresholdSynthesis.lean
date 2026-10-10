import OAI.Analysis.LipschitzHilbert.Packets.HilbertPacketSums

namespace OAI

/-! A monotone threshold selects one terminal interval of dyadic scales.
Its synthesis is controlled by the actual partial-sum variation. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem increment_cube_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ‖F b - F a‖^3 ≤ finiteCubicVariation F N := by
  classical
  by_cases hN : N = 0
  · subst N
    have : a = 0 ∧ b = 0 := by omega
    rcases this with ⟨rfl,rfl⟩
    simpa using finiteCubicVariation_nonneg F 0
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let p : Fin (N+1) → Fin (N+1) := fun i =>
    if i.val = 0 then ⟨a, by omega⟩ else ⟨b, by omega⟩
  have hp : Monotone p := by
    intro i j hij
    dsimp [p]
    split_ifs with hi hj hj
    · exact le_rfl
    · exact hab
    · have hij' : i.val ≤ j.val := hij
      omega
    · exact le_rfl
  have hsum := partition_le_finiteCubicVariation F N p hp
  have hs : ‖F b - F a‖^3 ≤
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖^3 := by
    have h := Finset.single_le_sum
      (f := fun i : Fin N => ‖F (p i.succ) - F (p i.castSucc)‖^3)
      (s := Finset.univ) (a := (⟨0,hNpos⟩ : Fin N))
      (fun i _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ _)
    simpa only [p, Fin.val_succ, Fin.val_castSucc, Nat.zero_add,
      Nat.one_ne_zero, ite_false, ite_true] using h
  exact hs.trans hsum

theorem increment_le_cubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ‖F b - F a‖ ≤ cubicVariation F N := by
  have h := Real.rpow_le_rpow (pow_nonneg (norm_nonneg (F b-F a)) 3)
    (increment_cube_le_finiteCubicVariation F N a b hab hb)
    (by norm_num : (0:ℝ) ≤ 1/3)
  have heq : (‖F b-F a‖^3)^(1/3:ℝ) = ‖F b-F a‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simpa only [heq, cubicVariation] using h

theorem monotone_threshold_suffix {N : ℕ} (d : Fin N → ℝ)
    (hd : Monotone d) (v : ℝ) :
    ∃ n : ℕ, n ≤ N ∧ ∀ j : Fin N, v ≤ d j ↔ n ≤ j.val := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => v ≤ d j)
  by_cases hs : s.Nonempty
  · let j0 := s.min' hs
    have hj0 : v ≤ d j0 := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
    refine ⟨j0.val, Nat.le_of_lt j0.isLt, ?_⟩
    intro j
    constructor
    · intro hj
      exact Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
    · intro hj
      exact hj0.trans (hd hj)
  · refine ⟨N, le_rfl, ?_⟩
    intro j
    constructor
    · intro hj
      exact False.elim (hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
    · intro hj
      omega

theorem threshold_sum_eq_partial_difference {E : Type*} [AddCommGroup E]
    {N : ℕ} (f : Fin N → E) (d : Fin N → ℝ) (hd : Monotone d) (v : ℝ) :
    ∃ n : ℕ, n ≤ N ∧ (∑ j, if v ≤ d j then f j else 0) =
      packetPartialSum f N - packetPartialSum f n := by
  obtain ⟨n,hn,hselect⟩ := monotone_threshold_suffix d hd v
  refine ⟨n,hn,?_⟩
  unfold packetPartialSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left j.isLt]
  by_cases hj : v ≤ d j
  · have hn' : ¬ j.val < n := Nat.not_lt.mpr ((hselect j).mp hj)
    simp only [ite_eq_left hj, ite_eq_right hn', sub_zero]
  · have hn' : j.val < n := Nat.lt_of_not_ge (fun h => hj ((hselect j).mpr h))
    simp only [ite_eq_right hj, ite_eq_left hn', sub_self]

theorem threshold_sum_le_variation {E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (f : Fin N → E) (d : Fin N → ℝ) (hd : Monotone d) (v : ℝ) :
    ‖∑ j, if v ≤ d j then f j else 0‖ ≤ cubicVariation (packetPartialSum f) N := by
  obtain ⟨n,hn,heq⟩ := threshold_sum_eq_partial_difference f d hd v
  rw [heq]
  exact increment_le_cubicVariation _ N n N hn le_rfl

end LipschitzHilbert

end

end OAI
