import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The two replacement denominators associated to a proper divisor. -/
def divisorSplitSmall (n d : ℕ) : ℕ := n + d
def divisorSplitLarge (n d : ℕ) : ℕ := n * (n / d + 1)

lemma divisor_split_data {n d : ℕ} (hd : d ∣ n) (hpos : 0 < d) (hlt : d < n) :
    n < divisorSplitSmall n d ∧ divisorSplitSmall n d < 2*n ∧
      2*n < divisorSplitLarge n d := by
  have hmul := Nat.mul_div_cancel' hd
  have hquot : 2 ≤ n / d := by nlinarith
  dsimp [divisorSplitSmall, divisorSplitLarge]
  constructor
  · omega
  constructor
  · omega
  · nlinarith

lemma divisor_split_identity {n d : ℕ} (hd : d ∣ n) (hpos : 0 < d) (hlt : d < n) :
    (1 : ℚ) / n = 1 / divisorSplitSmall n d + 1 / divisorSplitLarge n d := by
  have hn : 0 < n := lt_trans hpos hlt
  have hq : 0 < n / d := Nat.div_pos (Nat.le_of_lt hlt) hpos
  have hm : (d : ℚ) * (n / d : ℕ) = n := by exact_mod_cast Nat.mul_div_cancel' hd
  have hdq : (d : ℚ) ≠ 0 := by positivity
  have hqq : ((n / d : ℕ) : ℚ) ≠ 0 := by positivity
  dsimp [divisorSplitSmall, divisorSplitLarge]
  push_cast
  rw [← hm]
  field_simp

lemma divisor_split_small_injective (n : ℕ) : Function.Injective (divisorSplitSmall n) := by
  intro a b h
  dsimp [divisorSplitSmall] at h
  omega

lemma divisor_split_large_injOn (n : ℕ) :
    Set.InjOn (divisorSplitLarge n) (↑n.properDivisors : Set ℕ) := by
  intro a ha b hb hab
  obtain ⟨ha, hna⟩ := Nat.mem_properDivisors.mp ha
  obtain ⟨hb, hnb⟩ := Nat.mem_properDivisors.mp hb
  have hn : 0 < n := by omega
  have ham := Nat.mul_div_cancel' ha
  have hbm := Nat.mul_div_cancel' hb
  have hq : n / a = n / b := by
    dsimp [divisorSplitLarge] at hab
    nlinarith
  have hqp : 0 < n / a := by nlinarith
  rw [← hq] at hbm
  nlinarith

/-- Two injective collision maps remove at most twice the size of the forbidden set. -/
lemma filter_avoiding_two_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (T : Finset β) (f g : α → β)
    (hf : Set.InjOn f (↑I : Set α)) (hg : Set.InjOn g (↑I : Set α)) :
    I.card ≤ (I.filter (fun d => f d ∉ T ∧ g d ∉ T)).card + 2*T.card := by
  classical
  let G := I.filter (fun d => f d ∉ T ∧ g d ∉ T)
  let B₁ := I.filter (fun d => f d ∈ T)
  let B₂ := I.filter (fun d => g d ∈ T)
  have h₁ : B₁.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn f
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro a ha b hb hab
      exact hf (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  have h₂ : B₂.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn g
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro a ha b hb hab
      exact hg (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  have hc : I ⊆ G ∪ (B₁ ∪ B₂) := by
    intro d hd
    simp only [G, B₁, B₂, Finset.mem_union, Finset.mem_filter]
    tauto
  have hcard := Finset.card_le_card hc
  have hu := Finset.card_union_le G (B₁ ∪ B₂)
  have hub := Finset.card_union_le B₁ B₂
  change I.card ≤ G.card + 2*T.card
  omega

/-- Proper divisors whose two new denominators avoid all fixed denominators. -/
def goodSplitDivisors (n : ℕ) (T : Finset ℕ) : Finset ℕ :=
  n.properDivisors.filter (fun d => divisorSplitSmall n d ∉ T ∧ divisorSplitLarge n d ∉ T)

lemma good_split_divisors_card (n : ℕ) (hn : 0 < n) (T : Finset ℕ) :
    n.divisors.card ≤ (goodSplitDivisors n T).card + 2*T.card + 1 := by
  have h := filter_avoiding_two_card n.properDivisors T
    (divisorSplitSmall n) (divisorSplitLarge n)
    (divisor_split_small_injective n).injOn (divisor_split_large_injOn n)
  have hc : n.properDivisors.card + 1 = n.divisors.card := by
    rw [← Nat.insert_self_properDivisors (Nat.ne_of_gt hn)]
    exact (Finset.card_insert_of_notMem Nat.self_notMem_properDivisors).symm
  change n.divisors.card ≤ (goodSplitDivisors n T).card + 2*T.card + 1
  dsimp [goodSplitDivisors]
  omega

/-- Replace one denominator, keeping the other denominators in `T`. -/
def divisorSplitSet (n : ℕ) (T : Finset ℕ) (d : ℕ) : Finset ℕ :=
  insert (divisorSplitSmall n d) (insert (divisorSplitLarge n d) T)

lemma good_split_divisor_data {n d : ℕ} {T : Finset ℕ}
    (hd : d ∈ goodSplitDivisors n T) :
    d ∣ n ∧ 0 < d ∧ d < n ∧
      divisorSplitSmall n d ∉ T ∧ divisorSplitLarge n d ∉ T := by
  obtain ⟨hproper, hsmall, hlarge⟩ := Finset.mem_filter.mp hd
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hproper
  exact ⟨hdvd, Nat.pos_of_dvd_of_pos hdvd (by omega), hlt, hsmall, hlarge⟩

lemma divisor_split_set_card {n d : ℕ} {T : Finset ℕ}
    (hd : d ∈ goodSplitDivisors n T) :
    (divisorSplitSet n T d).card = T.card + 2 := by
  obtain ⟨hdvd, hpos, hlt, hs, hl⟩ := good_split_divisor_data hd
  have horder := divisor_split_data hdvd hpos hlt
  have hne : divisorSplitSmall n d ≠ divisorSplitLarge n d := by omega
  simp [divisorSplitSet, Finset.card_insert_of_notMem, hs, hl, hne]

lemma divisor_split_set_sum {n d : ℕ} {T : Finset ℕ}
    (hd : d ∈ goodSplitDivisors n T) :
    (∑ x ∈ divisorSplitSet n T d, (1 : ℚ) / x) =
      (∑ x ∈ T, (1 : ℚ) / x) + 1/n := by
  obtain ⟨hdvd, hpos, hlt, hs, hl⟩ := good_split_divisor_data hd
  have horder := divisor_split_data hdvd hpos hlt
  have hne : divisorSplitSmall n d ≠ divisorSplitLarge n d := by omega
  have hsi : divisorSplitSmall n d ∉ insert (divisorSplitLarge n d) T := by simp [hne, hs]
  rw [divisorSplitSet, Finset.sum_insert hsi, Finset.sum_insert hl,
    divisor_split_identity hdvd hpos hlt]
  ring

lemma divisor_split_set_positive {n d : ℕ} {T : Finset ℕ}
    (hT : ∀ x ∈ T, 0 < x) (hd : d ∈ goodSplitDivisors n T) :
    ∀ x ∈ divisorSplitSet n T d, 0 < x := by
  obtain ⟨hdvd, hpos, hlt, _, _⟩ := good_split_divisor_data hd
  have horder := divisor_split_data hdvd hpos hlt
  intro x hx
  simp only [divisorSplitSet, Finset.mem_insert] at hx
  rcases hx with rfl | rfl | hx
  · omega
  · omega
  · exact hT x hx

lemma divisor_split_set_injOn (n : ℕ) (T : Finset ℕ) :
    Set.InjOn (divisorSplitSet n T) (↑(goodSplitDivisors n T) : Set ℕ) := by
  intro a ha b hb hab
  obtain ⟨hadvd, hapos, halt, has, _⟩ := good_split_divisor_data ha
  obtain ⟨hbdvd, hbpos, hblt, _, _⟩ := good_split_divisor_data hb
  have hao := divisor_split_data hadvd hapos halt
  have hbo := divisor_split_data hbdvd hbpos hblt
  have hmem : divisorSplitSmall n a ∈ divisorSplitSet n T b := by
    rw [← hab]
    simp [divisorSplitSet]
  simp only [divisorSplitSet, Finset.mem_insert] at hmem
  rcases hmem with h | h | h
  · exact divisor_split_small_injective n h
  · omega
  · exact (has h).elim

/-- An expansion containing a highly divisible denominator branches into many distinct
expansions, all with precisely one additional term. -/
theorem divisor_branching_family (S : Finset ℕ)
    (hpos : ∀ x ∈ S, 0 < x) (hsum : (∑ x ∈ S, (1 : ℚ) / x) = 1)
    (n : ℕ) (hn : n ∈ S) :
    ∃ U : Finset (Finset ℕ),
      n.divisors.card ≤ U.card + 2*(S.card - 1) + 1 ∧
      ∀ T ∈ U, T.card = S.card + 1 ∧
        (∀ x ∈ T, 0 < x) ∧ (∑ x ∈ T, (1 : ℚ) / x) = 1 := by
  let T := S.erase n
  let U := (goodSplitDivisors n T).image (divisorSplitSet n T)
  have hTcard : T.card + 1 = S.card := Finset.card_erase_add_one hn
  have hcard : U.card = (goodSplitDivisors n T).card :=
    Finset.card_image_of_injOn (divisor_split_set_injOn n T)
  refine ⟨U, ?_, ?_⟩
  · have h := good_split_divisors_card n (hpos n hn) T
    rw [← hcard] at h
    omega
  · intro V hV
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hV
    refine ⟨?_, ?_, ?_⟩
    · rw [divisor_split_set_card hd]
      omega
    · apply divisor_split_set_positive _ hd
      intro x hx
      exact hpos x (Finset.mem_of_mem_erase hx)
    · rw [divisor_split_set_sum hd]
      exact (Finset.sum_erase_add S (fun x => (1 : ℚ) / x) hn).trans hsum

end Problem337

end

end OAI
