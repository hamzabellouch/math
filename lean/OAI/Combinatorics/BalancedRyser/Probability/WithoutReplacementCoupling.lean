import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace Balanced.WithoutReplacement

variable {α : Type*} [DecidableEq α]

def swapSet (x y : α) (S : Finset α) : Finset α :=
  (Equiv.swap x y).finsetCongr S

@[simp] theorem mem_swapSet (x y z : α) (S : Finset α) :
    z ∈ swapSet x y S ↔ Equiv.swap x y z ∈ S := by
  simp [swapSet, Finset.mem_map_equiv]

@[simp] theorem card_swapSet (x y : α) (S : Finset α) :
    (swapSet x y S).card = S.card := by
  simp [swapSet]

@[simp] theorem swapSet_involutive (x y : α) (S : Finset α) :
    swapSet x y (swapSet x y S) = S := by
  ext z
  simp

theorem swap_mem_iff {U : Finset α} {x y z : α} (hx : x ∈ U) (hy : y ∈ U) :
    Equiv.swap x y z ∈ U ↔ z ∈ U := by
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  by_cases hzy : z = y
  · subst z
    simp [hx, hy]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem swapSet_mem_completions_iff {U S : Finset α} {x y : α} {r : ℕ}
    (hx : x ∈ U) (hy : y ∈ U) :
    swapSet x y S ∈ (U.erase y).powersetCard r ↔
      S ∈ (U.erase x).powersetCard r := by
  simp only [Finset.mem_powersetCard, card_swapSet]
  have hsub : swapSet x y S ⊆ U.erase y ↔ S ⊆ U.erase x := by
    constructor
    · intro h z hz
      have hm : Equiv.swap x y z ∈ swapSet x y S := by simpa using hz
      have hmem := Finset.mem_erase.mp (h hm)
      refine Finset.mem_erase.mpr ⟨?_, (swap_mem_iff hx hy).mp hmem.2⟩
      intro hzx
      subst z
      simpa using hmem.1
    · intro h z hz
      have hmem := Finset.mem_erase.mp (h ((mem_swapSet x y z S).mp hz))
      refine Finset.mem_erase.mpr ⟨?_, (swap_mem_iff hx hy).mp hmem.2⟩
      intro hzy
      subst z
      simpa using hmem.1
  rw [hsub]

theorem swapSet_eq_self_of_notMem {S : Finset α} {x y : α}
    (hx : x ∉ S) (hy : y ∉ S) : swapSet x y S = S := by
  ext z
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  by_cases hzy : z = y
  · subst z
    simp [hx, hy]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem swapSet_eq_self_of_mem {S : Finset α} {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) : swapSet x y S = S := by
  ext z
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  by_cases hzy : z = y
  · subst z
    simp [hx, hy]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]

theorem swapSet_eq_exchange {S : Finset α} {x y : α}
    (hx : x ∈ S) (hy : y ∉ S) : swapSet x y S = insert y (S.erase x) := by
  ext z
  by_cases hzx : z = x
  · subst z
    have hxy : x ≠ y := by intro h; subst y; exact hy hx
    simp [hy, hxy]
  by_cases hzy : z = y
  · subst z
    simp [hx]
  simp [Equiv.swap_apply_of_ne_of_ne hzx hzy, hzx, hzy]

@[simp] theorem swapSet_insert (x y z : α) (S : Finset α) :
    swapSet x y (insert z S) = insert (Equiv.swap x y z) (swapSet x y S) := by
  simp [swapSet]

theorem swapSet_comm (x y : α) (S : Finset α) :
    swapSet x y S = swapSet y x S := by
  simp only [swapSet, Equiv.swap_comm]

theorem abs_sub_swapSet_le (U : Finset α) (f : Finset α → ℝ) {c : ℝ} {n : ℕ}
    (hc : 0 ≤ c)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = n →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c)
    {S : Finset α} (hSU : S ⊆ U) (hcard : S.card = n)
    {x y : α} (hxU : x ∈ U) (hyU : y ∈ U) :
    |f S - f (swapSet x y S)| ≤ c := by
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · rw [swapSet_eq_self_of_mem hx hy]
      simpa using hc
    · rw [swapSet_eq_exchange hx hy]
      exact hf S hSU hcard x hx y hyU hy
  · by_cases hy : y ∈ S
    · rw [swapSet_comm, swapSet_eq_exchange hy hx]
      exact hf S hSU hcard y hy x hxU hx
    · rw [swapSet_eq_self_of_notMem hx hy]
      simpa using hc

noncomputable def completionAverage (U : Finset α) (r : ℕ) (x : α)
    (f : Finset α → ℝ) : ℝ :=
  𝔼 S ∈ (U.erase x).powersetCard r, f (insert x S)

theorem completionAverage_eq_sum_div_choose (U : Finset α) (r : ℕ) (x : α)
    (f : Finset α → ℝ) :
    completionAverage U r x f =
      (∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) /
        (Nat.choose (U.erase x).card r : ℝ) := by
  simp only [completionAverage, Finset.expect_eq_sum_div_card, Finset.card_powersetCard]

theorem completionAverage_swap {U : Finset α} (r : ℕ) (f : Finset α → ℝ)
    {x y : α} (hx : x ∈ U) (hy : y ∈ U) :
    completionAverage U r y f =
      𝔼 S ∈ (U.erase x).powersetCard r, f (insert y (swapSet x y S)) := by
  symm
  apply Finset.expect_equiv (Equiv.swap x y).finsetCongr
  · intro S
    exact (swapSet_mem_completions_iff hx hy).symm
  · intro S _
    rfl

theorem completionAverage_oscillation (U : Finset α) (r : ℕ)
    (f : Finset α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hr : r < U.card)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = r + 1 →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c)
    {x y : α} (hx : x ∈ U) (hy : y ∈ U) :
    |completionAverage U r x f - completionAverage U r y f| ≤ c := by
  rw [completionAverage_swap r f hx hy]
  change |(𝔼 S ∈ (U.erase x).powersetCard r, f (insert x S)) -
    (𝔼 S ∈ (U.erase x).powersetCard r, f (insert y (swapSet x y S)))| ≤ c
  rw [← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le
  · apply Finset.powersetCard_nonempty.mpr
    rw [Finset.card_erase_of_mem hx]
    omega
  · intro S hS
    obtain ⟨hSU, hScard⟩ := Finset.mem_powersetCard.mp hS
    have hnot : x ∉ S := fun h => (Finset.mem_erase.mp (hSU h)).1 rfl
    have hsub : insert x S ⊆ U := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact (Finset.mem_erase.mp (hSU hz)).2
    have hcard : (insert x S).card = r + 1 := by simp [Finset.card_insert_of_notMem hnot, hScard]
    simpa using abs_sub_swapSet_le U f hc hf hsub hcard hx hy

theorem sum_completions_eq_sum_filter {U : Finset α} (r : ℕ)
    (f : Finset α → ℝ) {x : α} (hx : x ∈ U) :
    (∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) =
      ∑ T ∈ (U.powersetCard (r + 1)).filter (fun T => x ∈ T), f T := by
  apply Finset.sum_bij (fun S _ => insert x S)
  · intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    have hnot : x ∉ S := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset hx (hsub.trans (Finset.erase_subset _ _))
    · simp [hnot, hcard]
  · intro S hS T hT heq
    have hs : x ∉ S := by
      intro hxS
      exact (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hS).1 hxS)).1 rfl
    have ht : x ∉ T := by
      intro hxT
      exact (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hT).1 hxT)).1 rfl
    have := congrArg (fun W : Finset α => W.erase x) heq
    simpa [Finset.erase_insert hs, Finset.erase_insert ht] using this
  · intro T hT
    obtain ⟨hT, hxT⟩ := Finset.mem_filter.mp hT
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
    refine ⟨T.erase x, ?_, Finset.insert_erase hxT⟩
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨hne, hzT⟩ := Finset.mem_erase.mp hz
      exact Finset.mem_erase.mpr ⟨hne, hsub hzT⟩
    · simp [Finset.card_erase_of_mem hxT, hcard]
  · intro S _
    rfl

theorem sum_completions (U : Finset α) (r : ℕ) (f : Finset α → ℝ) :
    (∑ x ∈ U, ∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) =
      ((r : ℝ) + 1) * ∑ T ∈ U.powersetCard (r + 1), f T := by
  calc
    _ = ∑ x ∈ U, ∑ T ∈ U.powersetCard (r + 1), if x ∈ T then f T else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [sum_completions_eq_sum_filter r f hx, Finset.sum_filter]
    _ = ∑ T ∈ U.powersetCard (r + 1), ∑ x ∈ U, if x ∈ T then f T else 0 :=
      Finset.sum_comm
    _ = ∑ T ∈ U.powersetCard (r + 1), ((r : ℝ) + 1) * f T := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
      simp [hcard]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem average_completion_eq (U : Finset α) (r : ℕ) (f : Finset α → ℝ)
    (hr : r < U.card) :
    (𝔼 x ∈ U, completionAverage U r x f) =
      𝔼 T ∈ U.powersetCard (r + 1), f T := by
  have hUpos : 0 < U.card := lt_of_le_of_lt (Nat.zero_le r) hr
  have hn : U.card - 1 + 1 = U.card := Nat.sub_add_cancel hUpos
  have hbinom : (U.card : ℝ) * (Nat.choose (U.card - 1) r : ℝ) =
      (Nat.choose U.card (r + 1) : ℝ) * ((r : ℝ) + 1) := by
    have h := Nat.add_one_mul_choose_eq (U.card - 1) r
    rw [hn] at h
    exact_mod_cast h
  have hcardpos : (0 : ℝ) < U.card := by exact_mod_cast hUpos
  have hchoosepos : (0 : ℝ) < Nat.choose U.card (r + 1) := by
    exact_mod_cast Nat.choose_pos (by omega : r + 1 ≤ U.card)
  calc
    _ = (∑ x ∈ U, (∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) /
        (Nat.choose (U.card - 1) r : ℝ)) / (U.card : ℝ) := by
      rw [Finset.expect_eq_sum_div_card]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [completionAverage_eq_sum_div_choose, Finset.card_erase_of_mem hx]
    _ = (∑ x ∈ U, ∑ S ∈ (U.erase x).powersetCard r, f (insert x S)) /
        ((Nat.choose (U.card - 1) r : ℝ) * (U.card : ℝ)) := by
      rw [← Finset.sum_div, div_div]
    _ = (((r : ℝ) + 1) * ∑ T ∈ U.powersetCard (r + 1), f T) /
        ((Nat.choose U.card (r + 1) : ℝ) * ((r : ℝ) + 1)) := by
      rw [sum_completions, mul_comm (Nat.choose (U.card - 1) r : ℝ), hbinom]
    _ = (∑ T ∈ U.powersetCard (r + 1), f T) /
        (Nat.choose U.card (r + 1) : ℝ) := by
      field_simp
    _ = _ := by rw [Finset.expect_eq_sum_div_card, Finset.card_powersetCard]

theorem completionAverage_increment (U : Finset α) (r : ℕ)
    (f : Finset α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hr : r < U.card)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = r + 1 →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c)
    {x : α} (hx : x ∈ U) :
    |completionAverage U r x f - (𝔼 T ∈ U.powersetCard (r + 1), f T)| ≤ c := by
  rw [← average_completion_eq U r f hr]
  have hU : U.Nonempty := ⟨x, hx⟩
  rw [← Finset.expect_const hU (completionAverage U r x f), ← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le hU
  intro y hy
  exact completionAverage_oscillation U r f hc hr hf hx hy

theorem completionAverage_increment_secondMoment (U : Finset α) (r : ℕ)
    (f : Finset α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hr : r < U.card)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = r + 1 →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c) :
    (𝔼 x ∈ U, (completionAverage U r x f -
      (𝔼 T ∈ U.powersetCard (r + 1), f T)) ^ 2) ≤ c ^ 2 := by
  apply Finset.expect_le (Finset.card_pos.mp (by omega))
  intro x hx
  have h := completionAverage_increment U r f hc hr hf hx
  have hsquare := (sq_le_sq₀ (abs_nonneg _) hc).mpr h
  simpa using hsquare

noncomputable def finiteVariance {β : Type*} (s : Finset β) (f : β → ℝ) : ℝ :=
  𝔼 x ∈ s, (f x - (𝔼 y ∈ s, f y)) ^ 2

theorem expect_sq_sub_eq {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (f : β → ℝ) (a : ℝ) :
    (𝔼 x ∈ s, (f x - a)^2) =
      (𝔼 x ∈ s, (f x)^2) - 2 * a * (𝔼 x ∈ s, f x) + a^2 := by
  calc
    _ = 𝔼 x ∈ s, ((f x)^2 - (2 * a) * f x + a^2) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        ← Finset.mul_expect, Finset.expect_const hs]

theorem expect_sq_sub_mean_eq {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (f : β → ℝ) (a : ℝ) :
    (𝔼 x ∈ s, (f x - a)^2) =
      finiteVariance s f + ((𝔼 x ∈ s, f x) - a)^2 := by
  rw [expect_sq_sub_eq s hs f a, finiteVariance, expect_sq_sub_eq s hs f]
  ring

theorem finiteVariance_powersetCard_le (U : Finset α) (n : ℕ)
    (f : Finset α → ℝ) {c : ℝ} (hc : 0 ≤ c) (hn : n ≤ U.card)
    (hf : ∀ S : Finset α, S ⊆ U → S.card = n →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S → |f S - f (insert b (S.erase a))| ≤ c) :
    finiteVariance (U.powersetCard n) f ≤ (n : ℝ) * c^2 := by
  induction n generalizing U f with
  | zero => simp [finiteVariance]
  | succ r ih =>
    have hr : r < U.card := by omega
    have hU : U.Nonempty := Finset.card_pos.mp (by omega)
    let M : ℝ := 𝔼 T ∈ U.powersetCard (r+1), f T
    have hparent : finiteVariance (U.powersetCard (r+1)) f =
        𝔼 x ∈ U, 𝔼 S ∈ (U.erase x).powersetCard r, (f (insert x S) - M)^2 := by
      simpa only [finiteVariance, completionAverage, M] using
        (average_completion_eq U r (fun T => (f T - M)^2) hr).symm
    rw [hparent]
    refine (Finset.expect_le hU (a := (r : ℝ) * c^2 + c^2) ?_).trans_eq (by push_cast; ring)
    intro x hx
    have hrx : r ≤ (U.erase x).card := by
      rw [Finset.card_erase_of_mem hx]
      omega
    have hs : ((U.erase x).powersetCard r).Nonempty :=
      Finset.powersetCard_nonempty.mpr hrx
    rw [expect_sq_sub_mean_eq _ hs]
    have hchild : finiteVariance ((U.erase x).powersetCard r)
        (fun S => f (insert x S)) ≤ (r : ℝ) * c^2 := by
      apply ih (U.erase x) (fun S => f (insert x S)) hrx
      intro S hSU hScard a ha b hb hbS
      have hxS : x ∉ S := fun h => (Finset.mem_erase.mp (hSU h)).1 rfl
      have hax : a ≠ x := (Finset.mem_erase.mp (hSU ha)).1
      have hbx : b ≠ x := (Finset.mem_erase.mp hb).1
      have hsub : insert x S ⊆ U :=
        Finset.insert_subset hx (hSU.trans (Finset.erase_subset _ _))
      have hcard : (insert x S).card = r+1 := by simp [hxS, hScard]
      have h := hf (insert x S) hsub hcard a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_erase.mp hb).2 (by simp [hbx, hbS])
      simpa only [Finset.erase_insert_of_ne hax.symm, Finset.insert_comm x b] using h
    have hinc := completionAverage_increment U r f hc hr hf hx
    have hsq := (sq_le_sq₀ (abs_nonneg _) hc).mpr hinc
    have hsq' : (completionAverage U r x f - M)^2 ≤ c^2 := by
      simpa only [sq_abs, M] using hsq
    change finiteVariance ((U.erase x).powersetCard r) (fun S => f (insert x S)) +
      (completionAverage U r x f - M)^2 ≤ (r : ℝ) * c^2 + c^2
    exact add_le_add hchild hsq'

end Balanced.WithoutReplacement

end OAI
