import OAI.Combinatorics.Ryser.Incidence.WalkCounts
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

theorem walkCard_mul_le_labelCard_pow_four {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (T : Finset α) (D : Finset β) (eval : (β × β) × (β × β) → α) (L : ℝ)
    (hf : ∀ t ∈ T,
      L ≤ ((((D ×ˢ D) ×ˢ (D ×ˢ D)).filter fun q => eval q = t).card : ℝ)) :
    (T.card : ℝ) * L ≤ (D.card : ℝ) ^ 4 := by
  classical
  have hcount := Finset.card_nsmul_le_card_nsmul (R := ℝ)
    (s := T) (t := (D ×ˢ D) ×ˢ (D ×ˢ D)) (m := L) (n := 1)
    (fun t q => eval q = t) hf (by
      intro q _
      have hcard : (T.bipartiteBelow (fun t q => eval q = t) q).card ≤ 1 := by
        apply Finset.card_le_one_iff.mpr
        intro x y hx hy
        exact (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
      exact_mod_cast hcard)
  calc
    (T.card : ℝ) * L ≤ (((D ×ˢ D) ×ˢ (D ×ˢ D)).card : ℝ) := by
      simpa only [nsmul_eq_mul, mul_one] using hcount
    _ = (D.card : ℝ) ^ 4 := by
      simp only [Finset.card_product, Nat.cast_mul]
      ring

theorem expansion_bound_of_card_mul_le {c d n V : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hn : 0 < n) (hV : 2 ≤ V)
    (hdV : d ≤ V * n)
    (h : c * (n ^ 3 / (2 ^ 20 * V ^ 18)) ≤ d ^ 4) :
    c ≤ 2 ^ 20 * V ^ 22 * n := by
  let _ := hc
  have hVpos : 0 < V := lt_of_lt_of_le (by norm_num) hV
  have hLpos : 0 < n ^ 3 / (2 ^ 20 * V ^ 18) := by positivity
  apply (mul_le_mul_iff_left₀ hLpos).mp
  calc
    c * (n ^ 3 / (2 ^ 20 * V ^ 18)) ≤ d ^ 4 := h
    _ ≤ (V * n) ^ 4 := pow_le_pow_left₀ hd hdV 4
    _ = (2 ^ 20 * V ^ 22 * n) * (n ^ 3 / (2 ^ 20 * V ^ 18)) := by
      field_simp [ne_of_gt hVpos]

theorem fourWalks_mem_data {F : Type*} [DecidableEq F]
    {A B : Finset F} {G : Finset (F × F)} {a a' : F}
    {w : Σ _ : F, F × F} (hw : w ∈ fourWalks A B G a a') :
    w.1 ∈ A ∧ w.2.1 ∈ B ∧ w.2.2 ∈ B ∧
      (a, w.2.1) ∈ G ∧ (w.1, w.2.1) ∈ G ∧
      (w.1, w.2.2) ∈ G ∧ (a', w.2.2) ∈ G := by
  have h := Finset.mem_sigma.mp hw
  have hp := Finset.mem_product.mp h.2
  have hleft := Finset.mem_filter.mp hp.1
  have hright := Finset.mem_filter.mp hp.2
  exact ⟨h.1, hleft.1, hright.1, hleft.2.1, hleft.2.2,
    hright.2.1, hright.2.2⟩

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def edgeDifferences (G : Finset (F × F)) : Finset F :=
  G.image fun e => e.1 - e.2

private def differenceWalkLabels (a a' : F) (w : Σ _ : F, F × F) :
    (F × F) × (F × F) :=
  ((a - w.2.1, w.1 - w.2.1), (w.1 - w.2.2, a' - w.2.2))

private theorem differenceWalkLabels_injective (a a' : F) :
    Function.Injective (differenceWalkLabels a a') := let _ := instDecidableEqF; by
  intro w v h
  rcases w with ⟨m, b₁, b₂⟩
  rcases v with ⟨m', c₁, c₂⟩
  have h₁ := congrArg (fun q : (F × F) × (F × F) => q.1.1) h
  have h₂ := congrArg (fun q : (F × F) × (F × F) => q.1.2) h
  have h₃ := congrArg (fun q : (F × F) × (F × F) => q.2.1) h
  change a - b₁ = a - c₁ at h₁
  change m - b₁ = m' - c₁ at h₂
  change m - b₂ = m' - c₂ at h₃
  have hb₁ : b₁ = c₁ := by linear_combination -h₁
  subst c₁
  have hm : m = m' := by linear_combination h₂
  subst m'
  have hb₂ : b₂ = c₂ := by linear_combination -h₃
  subst c₂
  rfl

theorem difference_bound_of_many_fourWalks
    (A B : Finset F) (G : Finset (F × F)) (S : Finset F)
    {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hD : ((edgeDifferences G).card : ℝ) ≤ V * n)
    (hw : ∀ a ∈ S, ∀ a' ∈ S,
      n ^ 3 / (2 ^ 20 * V ^ 18) ≤ ((fourWalks A B G a a').card : ℝ)) :
    ((S - S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n := by
  classical
  apply expansion_bound_of_card_mul_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hn hV hD
  apply walkCard_mul_le_labelCard_pow_four (S - S) (edgeDifferences G)
    (fun q => q.1.1 - q.1.2 + q.2.1 - q.2.2)
  intro d hd
  obtain ⟨a, ha, a', ha', rfl⟩ := Finset.mem_sub.mp hd
  have hcard : (fourWalks A B G a a').card ≤
      ((((edgeDifferences G ×ˢ edgeDifferences G) ×ˢ
          (edgeDifferences G ×ˢ edgeDifferences G)).filter
        fun q => q.1.1 - q.1.2 + q.2.1 - q.2.2 = a - a').card) := by
    apply Finset.card_le_card_of_injOn (differenceWalkLabels a a')
    · intro w hwmem
      obtain ⟨_, _, _, h₁, h₂, h₃, h₄⟩ := fourWalks_mem_data hwmem
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_product.mpr
          exact ⟨Finset.mem_image.mpr ⟨(a, w.2.1), h₁, rfl⟩,
            Finset.mem_image.mpr ⟨(w.1, w.2.1), h₂, rfl⟩⟩
        · apply Finset.mem_product.mpr
          exact ⟨Finset.mem_image.mpr ⟨(w.1, w.2.2), h₃, rfl⟩,
            Finset.mem_image.mpr ⟨(a', w.2.2), h₄, rfl⟩⟩
      · dsimp [differenceWalkLabels]
        ring
    · exact (differenceWalkLabels_injective a a').injOn
  exact (hw a ha a' ha').trans (by exact_mod_cast hcard)

end RyserCoveringCounterexample.Incidence

end

end OAI
