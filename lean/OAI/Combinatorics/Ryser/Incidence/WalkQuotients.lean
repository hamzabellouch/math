import OAI.Combinatorics.Ryser.Incidence.WalkExpansion
import OAI.Combinatorics.Ryser.Incidence.WalkExtraction
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def edgeQuotients (G : Finset (F × F)) : Finset F :=
  G.image (fun e => e.1 / e.2)

theorem div_mem_edgeQuotients {G : Finset (F × F)} {a b : F}
    (h : (a, b) ∈ G) : a / b ∈ edgeQuotients G :=
  Finset.mem_image.mpr ⟨(a, b), h, rfl⟩

def walkQuotientLabels (a a' : F) (w : Σ _ : F, F × F) :
    (F × F) × (F × F) :=
  ((a / w.2.1, w.1 / w.2.1), (w.1 / w.2.2, a' / w.2.2))

def quotientWalkEval (q : (F × F) × (F × F)) : F :=
  q.1.1 * q.2.1 / (q.1.2 * q.2.2)

theorem walkQuotientLabels_injective_at {a a' : F}
    {w v : Σ _ : F, F × F}
    (ha : a ≠ 0) (hm : w.1 ≠ 0) (hb : w.2.1 ≠ 0)
    (h : walkQuotientLabels a a' w = walkQuotientLabels a a' v) :
    w = v := let _ := instDecidableEqF; by
  rcases w with ⟨m, b₁, b₂⟩
  rcases v with ⟨n, c₁, c₂⟩
  have h₁ : a / b₁ = a / c₁ :=
    congrArg (fun q : (F × F) × (F × F) => q.1.1) h
  have hb₁ : b₁ = c₁ := by
    simpa only [div_eq_mul_inv, mul_right_inj' ha, inv_inj] using h₁
  have h₂ : m / b₁ = n / c₁ :=
    congrArg (fun q : (F × F) × (F × F) => q.1.2) h
  rw [← hb₁] at h₂
  have hmn : m = n := (div_left_inj' hb).mp h₂
  have h₃ : m / b₂ = n / c₂ :=
    congrArg (fun q : (F × F) × (F × F) => q.2.1) h
  rw [← hmn] at h₃
  have hb₂ : b₂ = c₂ := by
    simpa only [div_eq_mul_inv, mul_right_inj' hm, inv_inj] using h₃
  cases hmn
  cases hb₁
  cases hb₂
  rfl

theorem quotientWalkEval_labels {a a' : F} {w : Σ _ : F, F × F}
    (hm : w.1 ≠ 0) (hb₁ : w.2.1 ≠ 0) (hb₂ : w.2.2 ≠ 0) :
    quotientWalkEval (walkQuotientLabels a a' w) = a / a' := let _ := instDecidableEqF; by
  unfold quotientWalkEval walkQuotientLabels
  rw [mul_div_mul_comm, div_div_div_cancel_right₀ hb₁,
    div_div_div_cancel_right₀ hb₂, div_mul_div_cancel₀ hm]

theorem walkQuotientLabels_mem {A B : Finset F} {G : Finset (F × F)}
    {a a' : F} {w : Σ _ : F, F × F}
    (hw : w ∈ fourWalks A B G a a') :
    walkQuotientLabels a a' w ∈
      (edgeQuotients G ×ˢ edgeQuotients G) ×ˢ
        (edgeQuotients G ×ˢ edgeQuotients G) := by
  obtain ⟨_, _, _, h₁, h₂, h₃, h₄⟩ := fourWalks_mem_data hw
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr
      ⟨div_mem_edgeQuotients h₁, div_mem_edgeQuotients h₂⟩,
      Finset.mem_product.mpr
      ⟨div_mem_edgeQuotients h₃, div_mem_edgeQuotients h₄⟩⟩

theorem quotient_bound_of_many_fourWalks
    (A B : Finset F) (G : Finset (F × F)) (S : Finset F)
    (hS : S ⊆ A) (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B, b ≠ 0)
    {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hD : ((edgeQuotients G).card : ℝ) ≤ V * n)
    (hw : ∀ a ∈ S, ∀ a' ∈ S,
      n ^ 3 / (2 ^ 20 * V ^ 18) ≤ ((fourWalks A B G a a').card : ℝ)) :
    ((S / S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n := by
  have hcount : ((S / S).card : ℝ) * (n ^ 3 / (2 ^ 20 * V ^ 18)) ≤
      ((edgeQuotients G).card : ℝ) ^ 4 := by
    apply walkCard_mul_le_labelCard_pow_four
      (S / S) (edgeQuotients G) quotientWalkEval
      (n ^ 3 / (2 ^ 20 * V ^ 18))
    intro t ht
    obtain ⟨a, ha, a', ha', rfl⟩ := Finset.mem_div.mp ht
    have hc : (fourWalks A B G a a').card ≤
        (((edgeQuotients G ×ˢ edgeQuotients G) ×ˢ
          (edgeQuotients G ×ˢ edgeQuotients G)).filter
            (fun q => quotientWalkEval q = a / a')).card := by
      refine Finset.card_le_card_of_injOn (walkQuotientLabels a a') ?_ ?_
      · intro w hw'
        have hwdata := fourWalks_mem_data hw'
        exact Finset.mem_filter.mpr
          ⟨walkQuotientLabels_mem hw',
            quotientWalkEval_labels (hA0 _ hwdata.1)
              (hB0 _ hwdata.2.1) (hB0 _ hwdata.2.2.1)⟩
      · intro w hw' v _ heq
        have hwdata := fourWalks_mem_data hw'
        exact walkQuotientLabels_injective_at
          (hA0 _ (hS ha)) (hA0 _ hwdata.1) (hB0 _ hwdata.2.1) heq
    exact (hw a ha a' ha').trans (Nat.cast_le.mpr hc)
  exact expansion_bound_of_card_mul_le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn hV hD hcount

theorem exists_simultaneous_small_difference_quotient
    (A B : Finset F) (G : Finset (F × F)) (hG : G ⊆ A ×ˢ B)
    (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B, b ≠ 0)
    {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hA : (A.card : ℝ) ≤ V * n) (hB : (B.card : ℝ) ≤ V * n)
    (hE : n ^ 2 / V ≤ (G.card : ℝ))
    (hD : ((edgeDifferences G).card : ℝ) ≤ V * n)
    (hQ : ((edgeQuotients G).card : ℝ) ≤ V * n) :
    ∃ S : Finset F, S ⊆ A ∧
      3 * n / (8 * V ^ 2) ≤ (S.card : ℝ) ∧
      (S.card : ℝ) ≤ V * n ∧
      ((S - S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n ∧
      ((S / S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n := by
  obtain ⟨S, hS, hScard, hw⟩ :=
    exists_many_fourWalks A B G hG hn hV hA hB hE
  exact ⟨S, hS, hScard,
    (Nat.cast_le.mpr (Finset.card_le_card hS)).trans hA,
    difference_bound_of_many_fourWalks A B G S hn hV hD hw,
    quotient_bound_of_many_fourWalks A B G S hS hA0 hB0 hn hV hQ hw⟩

end RyserCoveringCounterexample.Incidence

end OAI
