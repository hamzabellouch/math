import OAI.Combinatorics.EditApproximation.Geometry.RefinementBandSupport
import OAI.Combinatorics.EditApproximation.Geometry.InitialInputBudget

namespace OAI

/-! Cardinality of the actual raw initial-data and band-data lists. The
counts apply before any good-seed event and include rejected candidates. -/

namespace EditApproximation

theorem list_eraseDups_length_le {α : Type*} [BEq α] (items : List α) :
    items.eraseDups.length ≤ items.length := by
  cases items with
  | nil => exact le_rfl
  | cons first rest =>
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    exact Nat.succ_le_succ ((list_eraseDups_length_le _).trans (List.length_filter_le _ _))
termination_by items.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == first) rest
  simp only [List.length_cons]
  omega

theorem rawRefinementCenters_length {n : ℕ} (N P F : ℕ) (a value : ℚ)
    (q : TargetInterval n) (hP : 0 < P) (hF : 1 ≤ F) :
    (rawRefinementCenters N P F a value q).length ≤
      (dyadicQueryWindow N value a F).length * (64 * F * P + 2) ^ 2 := by
  apply (list_eraseDups_length_le _).trans
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hceil : ⌈value⌉₊ ≤ 16 * F * b := by
    apply Nat.ceil_le.mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow.1
    push_cast
    nlinarith only [h]
  simpa only [show 4 * (16 * F) * P = 64 * F * P by ring] using
    localTargetStates_length_from_scale P b ⌈value⌉₊ (16 * F) q hP hceil

theorem cellTargetStates_length_dyadic {n P b : ℕ} (theta : ℚ) (cell : ℕ × ℕ)
    (htheta : 0 ≤ theta ∧ theta ≤ 1)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellTargetStates n (seedGridSpacing b P) (theta * b) cell).length ≤ (P + 1) ^ 2 := by
  have hg : (0 : ℚ) < seedGridSpacing b P := by
    exact_mod_cast (show 0 < seedGridSpacing b P by unfold seedGridSpacing; omega)
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hb hP
  have hsize : theta * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hg).2
    have hsmall : theta * b ≤ (b : ℚ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg b)
    exact hsmall.trans hcover
  exact (cellTargetStates_length_le cell
    (mul_nonneg htheta.1 (Nat.cast_nonneg b)) hsize).trans
    (Nat.pow_le_pow_left (Nat.le_succ P) 2)

theorem refinementInitialSupport_length {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q : TargetInterval n) (hP : ∃ e : ℕ, P = 2 ^ e) (hF : 1 ≤ F) (hw : 0 ≤ value) :
    (refinementInitialSupport N P F exponent a value q).length ≤
      1 + (dyadicQueryWindow N value a F).length *
        ((64 * F * P + 2) ^ 2 + ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  have hlocal := rawRefinementCenters_length N P F a value q hPpos hF
  have hcells := localGroupQueryKeys_length N F exponent a (fun _ => value) q hF hw
  have hmembers : ((localGroupQueryKeys N F exponent a (fun _ => value) q).flatMap fun key =>
      cellTargetStates n (seedGridSpacing key.1 P) ((2 : ℚ) ^ (-(exponent : ℤ)) * key.1) key.2).length ≤
      (localGroupQueryKeys N F exponent a (fun _ => value) q).length * (P + 1) ^ 2 := by
    apply list_flatMap_length_le
    intro key hk
    have hscale := localGroupQueryKeys_scale hk
    obtain ⟨e, _, heq⟩ := List.mem_map.mp hscale
    exact cellTargetStates_length_dyadic _ key.2
      ⟨by positivity, zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)⟩
      ⟨e, heq.symm⟩ hP
  unfold refinementInitialSupport
  simp only [List.length_cons, List.length_append, List.length_map]
  nlinarith only [hlocal, hmembers, Nat.mul_le_mul_right ((P + 1) ^ 2) hcells]

theorem wideWarmupInputs_length {nx ny M : ℕ} (parent : TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (hP : 0 < P) :
    (wideWarmupInputs (M := M) parent P representatives).length ≤
      representatives.length * M * (40 * P + 2) ^ 2 := by
  apply (list_eraseDups_length_le _).trans
  have h : (representatives.flatMap fun br => (List.finRange M).flatMap fun i =>
      (wideChildStateList parent br.2 br.1 P i).map fun r => (i, r)).length ≤
      representatives.length * (M * (40 * P + 2) ^ 2) := by
    apply list_flatMap_length_le
    intro br hbr
    have hi : ((List.finRange M).flatMap fun i =>
        (wideChildStateList parent br.2 br.1 P i).map fun r => (i, r)).length ≤
        (List.finRange M).length * (40 * P + 2) ^ 2 := by
      apply list_flatMap_length_le
      intro i hi
      simpa only [List.length_map] using wideEarlierChildStateList_length_le parent br.2 br.1 P hP i
    simpa only [List.length_finRange] using hi
  exact h.trans_eq (by ring)

theorem refinementBandInputList_length {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent : ℕ) (a : ℚ) (initial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (hP : ∃ e : ℕ, P = 2 ^ e) (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (refinementBandInputList (M := M) parent N P F exponent a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((64 * F * P + 2) ^ 2 + ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) *
        M * (40 * P + 2) ^ 2 := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  exact (wideWarmupInputs_length parent P _ hPpos).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right M
      (queryEarlierRepresentatives_length N P F exponent a initial q hP hF hw)))

end EditApproximation

end OAI
