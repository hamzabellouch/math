import OAI.Combinatorics.BalancedRyser.Probability.WithoutReplacementCoupling

namespace OAI

open scoped BigOperators

namespace Balanced.WithoutReplacement

theorem finiteVariance_product {α β : Type*} (s : Finset α) (t : Finset β)
    (ht : t.Nonempty) (f : α → β → ℝ) :
    finiteVariance (s ×ˢ t) (fun p => f p.1 p.2) =
      (𝔼 x ∈ s, finiteVariance t (f x)) +
        finiteVariance s (fun x => 𝔼 y ∈ t, f x y) := by
  unfold finiteVariance
  rw [Finset.expect_product]
  simp_rw [Finset.expect_product]
  calc
    _ = 𝔼 x ∈ s, ((𝔼 y ∈ t, (f x y - (𝔼 z ∈ t, f x z))^2) +
        ((𝔼 y ∈ t, f x y) - (𝔼 a ∈ s, 𝔼 b ∈ t, f a b))^2) := by
      apply Finset.expect_congr rfl
      intro x _
      exact expect_sq_sub_mean_eq t ht (f x) _
    _ = _ := by rw [Finset.expect_add_distrib]

theorem abs_expect_sub_expect_le {β : Type*} (t : Finset β) (ht : t.Nonempty)
    (f g : β → ℝ) {c : ℝ} (h : ∀ y ∈ t, |f y - g y| ≤ c) :
    |(𝔼 y ∈ t, f y) - (𝔼 y ∈ t, g y)| ≤ c := by
  rw [← Finset.expect_sub_distrib]
  exact (Finset.abs_expect_le _ _).trans (Finset.expect_le ht h)

theorem finiteVariance_powersetCard_product_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (m n : ℕ)
    (f : Finset α → Finset β → ℝ) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hm : m ≤ U.card) (hn : n ≤ V.card)
    (hfirst : ∀ S : Finset α, S ⊆ U → S.card = m →
      ∀ T : Finset β, T ⊆ V → T.card = n →
      ∀ a ∈ S, ∀ b ∈ U, b ∉ S →
        |f S T - f (insert b (S.erase a)) T| ≤ c)
    (hsecond : ∀ S : Finset α, S ⊆ U → S.card = m →
      ∀ T : Finset β, T ⊆ V → T.card = n →
      ∀ a ∈ T, ∀ b ∈ V, b ∉ T →
        |f S T - f S (insert b (T.erase a))| ≤ d) :
    finiteVariance (U.powersetCard m ×ˢ V.powersetCard n)
      (fun p => f p.1 p.2) ≤ (m : ℝ)*c^2 + (n : ℝ)*d^2 := by
  have hU := Finset.powersetCard_nonempty.mpr hm
  have hV := Finset.powersetCard_nonempty.mpr hn
  rw [finiteVariance_product _ _ hV]
  have hconditional : (𝔼 S ∈ U.powersetCard m,
      finiteVariance (V.powersetCard n) (f S)) ≤ (n : ℝ)*d^2 := by
    apply Finset.expect_le hU
    intro S hS
    obtain ⟨hSU, hScard⟩ := Finset.mem_powersetCard.mp hS
    exact finiteVariance_powersetCard_le V n (f S) hd hn (hsecond S hSU hScard)
  have hmeans : finiteVariance (U.powersetCard m)
      (fun S => 𝔼 T ∈ V.powersetCard n, f S T) ≤ (m : ℝ)*c^2 := by
    apply finiteVariance_powersetCard_le U m _ hc hm
    intro S hSU hScard a ha b hb hbS
    apply abs_expect_sub_expect_le _ hV
    intro T hT
    obtain ⟨hTV, hTcard⟩ := Finset.mem_powersetCard.mp hT
    exact hfirst S hSU hScard T hTV hTcard a ha b hb hbS
  exact (add_le_add hconditional hmeans).trans_eq (add_comm _ _)

end Balanced.WithoutReplacement

end OAI
