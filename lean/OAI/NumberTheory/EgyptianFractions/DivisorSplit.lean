import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The larger denominator in the split of `1 / n` indexed by `d ∣ n`. -/
def divisorSplitUpper (n d : ℕ) : ℕ := (n / d) * (n + d)

lemma divisorSplit_quotient_ge_two {n d : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) (hlt : d < n) : 2 ≤ n / d := by
  have hmul : n / d * d = n := Nat.div_mul_cancel hdn
  by_contra h
  have hq : n / d ≤ 1 := by omega
  have : n / d * d ≤ d := by
    simpa using mul_le_mul_of_nonneg_right hq hd.le
  omega

lemma divisorSplit_order {n d : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) (hlt : d < n) :
    n < n + d ∧ n + d < divisorSplitUpper n d := by
  have hq := divisorSplit_quotient_ge_two hd hdn hlt
  unfold divisorSplitUpper
  constructor
  · omega
  · have hp : 0 < n + d := by omega
    nlinarith

lemma divisorSplit_identity {n d : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + d : ℕ) + 1 / divisorSplitUpper n d := by
  have hmul : n / d * d = n := Nat.div_mul_cancel hdn
  have hq : 0 < n / d := by
    by_contra h
    have hz : n / d = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hmul
    omega
  have hnq : (n : ℚ) ≠ 0 := by positivity
  have hdq : (d : ℚ) ≠ 0 := by positivity
  have hpd : ((n + d : ℕ) : ℚ) ≠ 0 := by positivity
  have hqq : ((n / d : ℕ) : ℚ) ≠ 0 := by positivity
  have hmulq : ((n / d : ℕ) : ℚ) * d = n := by exact_mod_cast hmul
  unfold divisorSplitUpper
  push_cast
  field_simp
  nlinarith

lemma divisorSplitUpper_injOn {n : ℕ} (hn : 0 < n) :
    Set.InjOn (divisorSplitUpper n) {d : ℕ | 0 < d ∧ d ∣ n} := by
  intro d hd e he hde
  have hdi := divisorSplit_identity hd.1 hd.2 hn
  have hei := divisorSplit_identity he.1 he.2 hn
  have heq : (1 : ℚ) / (n + d : ℕ) = 1 / (n + e : ℕ) := by
    rw [hde] at hdi
    linarith
  have hnd : ((n + d : ℕ) : ℚ) ≠ 0 := by positivity
  have hne : ((n + e : ℕ) : ℚ) ≠ 0 := by positivity
  have hnat : n + d = n + e := by
    have hcast : ((n + d : ℕ) : ℚ) = (n + e : ℕ) := by
      field_simp at heq
      linarith
    exact_mod_cast hcast
  omega

/-- A split is good when neither new denominator collides with an unchanged term. -/
def countingGoodSplitDivisors (n : ℕ) (s : Finset ℕ) : Finset ℕ :=
  n.properDivisors.filter (fun d => n + d ∉ s ∧ divisorSplitUpper n d ∉ s)

/-- Append the two denominators indexed by a divisor to a fixed unchanged set. -/
def countingDivisorSplitSet (n d : ℕ) (s : Finset ℕ) : Finset ℕ :=
  insert (n + d) (insert (divisorSplitUpper n d) s)

lemma countingGoodSplitDivisors_spec {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) :
    0 < d ∧ d ∣ n ∧ d < n ∧ n + d ∉ s ∧ divisorSplitUpper n d ∉ s := by
  rcases Finset.mem_filter.mp hd with ⟨hp, ha, hb⟩
  exact ⟨Nat.pos_of_mem_properDivisors hp, (Nat.mem_properDivisors.mp hp).1,
    (Nat.mem_properDivisors.mp hp).2, ha, hb⟩

lemma countingDivisorSplitSet_card {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) :
    (countingDivisorSplitSet n d s).card = s.card + 2 := by
  obtain ⟨hpos, hdvd, hlt, ha, hb⟩ := countingGoodSplitDivisors_spec hd
  have hne := (divisorSplit_order hpos hdvd hlt).2.ne
  simp [countingDivisorSplitSet, ha, hb, hne]

lemma countingDivisorSplitSet_sum {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) :
    (∑ a ∈ countingDivisorSplitSet n d s, (1 : ℚ) / a) =
      (∑ a ∈ s, (1 : ℚ) / a) + 1 / n := by
  obtain ⟨hpos, hdvd, hlt, ha, hb⟩ := countingGoodSplitDivisors_spec hd
  have hne := (divisorSplit_order hpos hdvd hlt).2.ne
  have hi := divisorSplit_identity hpos hdvd (lt_trans hpos hlt)
  simp [countingDivisorSplitSet, ha, hb, hne]
  simp only [one_div, Nat.cast_add] at hi
  linarith

lemma countingDivisorSplitSet_injOn (n : ℕ) (s : Finset ℕ) :
    Set.InjOn (fun d => countingDivisorSplitSet n d s) (countingGoodSplitDivisors n s) := by
  intro d hd e he hde
  change countingDivisorSplitSet n d s = countingDivisorSplitSet n e s at hde
  obtain ⟨hdpos, hddvd, hdlt, hda, hdb⟩ := countingGoodSplitDivisors_spec hd
  obtain ⟨hepos, hedvd, helt, hea, heb⟩ := countingGoodSplitDivisors_spec he
  have hdo := (divisorSplit_order hdpos hddvd hdlt).2
  have heo := (divisorSplit_order hepos hedvd helt).2
  have hdm : n + d ∈ countingDivisorSplitSet n e s := by
    rw [← hde]
    simp [countingDivisorSplitSet]
  have hem : n + e ∈ countingDivisorSplitSet n d s := by
    rw [hde]
    simp [countingDivisorSplitSet]
  simp only [countingDivisorSplitSet, Finset.mem_insert] at hdm hem
  rcases hdm with h | h | h
  · omega
  · rcases hem with h' | h' | h'
    · omega
    · omega
    · exact (hea h').elim
  · exact (hda h).elim

lemma countingGoodSplitDivisors_card_bound (n : ℕ) (s : Finset ℕ) :
    n.properDivisors.card ≤ (countingGoodSplitDivisors n s).card + 2 * s.card := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let bad₁ := n.properDivisors.filter (fun d => n + d ∈ s)
  let bad₂ := n.properDivisors.filter (fun d => divisorSplitUpper n d ∈ s)
  have hb₁ : bad₁.card ≤ s.card := by
    apply Finset.card_le_card_of_injOn (fun d => n + d)
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro d hd e he hde
      change n + d = n + e at hde
      omega
  have hb₂ : bad₂.card ≤ s.card := by
    apply Finset.card_le_card_of_injOn (divisorSplitUpper n)
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro d hd e he hde
      have hdp := (Finset.mem_filter.mp hd).1
      have hep := (Finset.mem_filter.mp he).1
      exact divisorSplitUpper_injOn hnpos
        ⟨Nat.pos_of_mem_properDivisors hdp, (Nat.mem_properDivisors.mp hdp).1⟩
        ⟨Nat.pos_of_mem_properDivisors hep, (Nat.mem_properDivisors.mp hep).1⟩ hde
  have hcover : n.properDivisors ⊆ countingGoodSplitDivisors n s ∪ (bad₁ ∪ bad₂) := by
    intro d hd
    by_cases ha : n + d ∈ s
    · simp [bad₁, ha, hd]
    by_cases hb : divisorSplitUpper n d ∈ s
    · simp [bad₂, hb, hd]
    · simp [countingGoodSplitDivisors, hd, ha, hb]
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le (countingGoodSplitDivisors n s) (bad₁ ∪ bad₂)
  have hv := Finset.card_union_le bad₁ bad₂
  omega

lemma countingGoodSplitDivisors_card_lower (n : ℕ) (s : Finset ℕ) :
    n.divisors.card - 1 - 2 * s.card ≤ (countingGoodSplitDivisors n s).card := by
  have hb := countingGoodSplitDivisors_card_bound n s
  by_cases hn : n = 0
  · simp [hn]
  have hc : n.divisors.card = n.properDivisors.card + 1 := by
    rw [← Nat.insert_self_properDivisors hn]
    simp
  omega

/-- Distinct good divisors give equally many different denominator sets. -/
lemma countingDivisorSplitSet_image_card (n : ℕ) (s : Finset ℕ) :
    ((countingGoodSplitDivisors n s).image (fun d => countingDivisorSplitSet n d s)).card =
      (countingGoodSplitDivisors n s).card := by
  exact Finset.card_image_of_injOn (countingDivisorSplitSet_injOn n s)

end Problem337

end

end OAI
