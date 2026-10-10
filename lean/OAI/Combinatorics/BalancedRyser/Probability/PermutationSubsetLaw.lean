import Mathlib

namespace OAI

open scoped BigOperators

namespace Balanced.PermutationSubsetLaw

theorem expect_comp_of_fiber_card_eq {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (t : Finset β) (f : Ω → β) (m : ℕ) (hm : 0 < m)
    (hmap : ∀ ω ∈ s, f ω ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter (fun ω => f ω = b)).card = m)
    (g : β → ℝ) :
    (𝔼 ω ∈ s, g (f ω)) = 𝔼 b ∈ t, g b := by
  classical
  have hcard : s.card = t.card * m := by
    have h := Finset.sum_card_fiberwise_eq_card_filter s t f
    rw [Finset.filter_eq_self.mpr hmap] at h
    calc
      s.card = ∑ b ∈ t, (s.filter (fun ω => f ω = b)).card := h.symm
      _ = ∑ _b ∈ t, m := Finset.sum_congr rfl hfiber
      _ = t.card * m := by simp
  have hsum : (∑ ω ∈ s, g (f ω)) = (m : ℝ) * ∑ b ∈ t, g b := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    calc
      _ = ∑ b ∈ t, (m : ℝ) * g b := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          (∑ ω ∈ s.filter (fun ω => f ω = b), g (f ω)) =
              ∑ _ω ∈ s.filter (fun ω => f ω = b), g b := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [(Finset.mem_filter.mp hω).2]
          _ = _ := by simp [hfiber b hb]
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, hsum, hcard]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  by_cases ht : (t.card : ℝ) = 0
  · simp [ht]
  · field_simp

variable {α : Type*} [DecidableEq α]

theorem exists_perm_fixing_map (S T : Finset α) (x : α)
    (hcard : S.card = T.card) (hxS : x ∉ S) (hxT : x ∉ T) :
    ∃ τ : Equiv.Perm α, τ x = x ∧ S.map τ.toEmbedding = T := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
  have hsx : σ x ∉ T := by
    intro h
    rw [← hσ] at h
    obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp h
    exact hxS ((σ.injective hzx) ▸ hz)
  have hswap : T.map (Equiv.swap (σ x) x).toEmbedding = T := by
    apply Finset.eq_of_subset_of_card_le _ (by simp)
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    change Equiv.swap (σ x) x z ∈ T
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hz hsx)
      (ne_of_mem_of_not_mem hz hxT)]
    exact hz
  refine ⟨σ.trans (Equiv.swap (σ x) x), by simp, ?_⟩
  change S.map (σ.toEmbedding.trans (Equiv.swap (σ x) x).toEmbedding) = T
  rw [← Finset.map_map, hσ, hswap]

def postcompose (τ : Equiv.Perm α) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.trans τ
  invFun σ := σ.trans τ.symm
  left_inv σ := by ext a; simp
  right_inv σ := by ext a; simp

theorem target_image_fiber_card_eq [Fintype α]
    (I S T : Finset α) (i x : α) (hcard : S.card = T.card)
    (hxS : x ∉ S) (hxT : x ∉ T) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α =>
      σ i = x ∧ I.map σ.toEmbedding = S)).card) =
    ((Finset.univ.filter (fun σ : Equiv.Perm α =>
      σ i = x ∧ I.map σ.toEmbedding = T)).card) := by
  classical
  obtain ⟨τ, hτx, hτ⟩ := exists_perm_fixing_map S T x hcard hxS hxT
  apply Finset.card_equiv (postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change τ (σ i) = x
      rw [h.1, hτx]
    · change I.map (σ.toEmbedding.trans τ.toEmbedding) = T
      rw [← Finset.map_map, h.2, hτ]
  · intro h
    have hi : σ i = x := by
      apply τ.injective
      exact h.1.trans hτx.symm
    refine ⟨hi, ?_⟩
    apply Finset.map_injective τ.toEmbedding
    rw [hτ]
    have himage := h.2
    change I.map (σ.toEmbedding.trans τ.toEmbedding) = T at himage
    simpa only [Finset.map_map] using himage

theorem expect_image_conditioned_target [Fintype α]
    (I : Finset α) (i x : α) (hi : i ∉ I) (g : Finset α → ℝ) :
    (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x),
      g (I.map σ.toEmbedding)) =
    𝔼 S ∈ (Finset.univ.erase x).powersetCard I.card, g S := by
  classical
  let s := Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)
  let t := (Finset.univ.erase x).powersetCard I.card
  have hmaps (σ : Equiv.Perm α) (hσ : σ ∈ s) : I.map σ.toEmbedding ∈ t := by
    have hσx : σ i = x := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp⟩
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hax
    exact hi ((σ.injective (hax.trans hσx.symm)) ▸ ha)
  let σ₀ := Equiv.swap i x
  have hσ₀ : σ₀ ∈ s := by simp [s, σ₀]
  let S₀ := I.map σ₀.toEmbedding
  have hS₀ : S₀ ∈ t := hmaps σ₀ hσ₀
  let m := (s.filter (fun σ => I.map σ.toEmbedding = S₀)).card
  have hm : 0 < m := Finset.card_pos.mpr ⟨σ₀, Finset.mem_filter.mpr ⟨hσ₀, rfl⟩⟩
  apply expect_comp_of_fiber_card_eq s t (fun σ => I.map σ.toEmbedding) m hm hmaps
  intro S hS
  have hS' := Finset.mem_powersetCard.mp hS
  have hS₀' := Finset.mem_powersetCard.mp hS₀
  have hxS : x ∉ S := fun hx => (Finset.mem_erase.mp (hS'.1 hx)).1 rfl
  have hxS₀ : x ∉ S₀ := fun hx => (Finset.mem_erase.mp (hS₀'.1 hx)).1 rfl
  have h := target_image_fiber_card_eq I S S₀ i x
    (hS'.2.trans hS₀'.2.symm) hxS hxS₀
  simpa only [m, s, Finset.filter_filter] using h

theorem image_fiber_card_eq [Fintype α] (I S T : Finset α)
    (hcard : S.card = T.card) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α => I.map σ.toEmbedding = S)).card) =
    ((Finset.univ.filter (fun σ : Equiv.Perm α => I.map σ.toEmbedding = T)).card) := by
  classical
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
  apply Finset.card_equiv (postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    change I.map (σ.toEmbedding.trans τ.toEmbedding) = T
    rw [← Finset.map_map, h, hτ]
  · intro h
    apply Finset.map_injective τ.toEmbedding
    rw [hτ]
    change I.map (σ.toEmbedding.trans τ.toEmbedding) = T at h
    simpa only [Finset.map_map] using h

theorem expect_image [Fintype α] (I : Finset α) (g : Finset α → ℝ) :
    (𝔼 σ : Equiv.Perm α, g (I.map σ.toEmbedding)) =
      𝔼 S ∈ (Finset.univ : Finset α).powersetCard I.card, g S := by
  classical
  let m := ((Finset.univ : Finset (Equiv.Perm α)).filter
    (fun σ => I.map σ.toEmbedding = I)).card
  have hm : 0 < m := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.refl α, by simp⟩
  apply expect_comp_of_fiber_card_eq (Finset.univ : Finset (Equiv.Perm α))
    ((Finset.univ : Finset α).powersetCard I.card) (fun σ : Equiv.Perm α => I.map σ.toEmbedding) m hm
  · intro σ _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩
  · intro S hS
    exact image_fiber_card_eq I S I (Finset.mem_powersetCard.mp hS).2

theorem expect_two_images_conditioned_target [Fintype α]
    {β : Type*} [Fintype β] [DecidableEq β]
    (I : Finset α) (J : Finset β) (i x : α) (hi : i ∉ I)
    (g : Finset α → Finset β → ℝ) :
    (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x),
      𝔼 τ : Equiv.Perm β, g (I.map σ.toEmbedding) (J.map τ.toEmbedding)) =
    𝔼 S ∈ (Finset.univ.erase x).powersetCard I.card,
      𝔼 T ∈ (Finset.univ : Finset β).powersetCard J.card, g S T := by
  calc
    _ = 𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x),
        𝔼 T ∈ (Finset.univ : Finset β).powersetCard J.card,
          g (I.map σ.toEmbedding) T := by
      apply Finset.expect_congr rfl
      intro σ _
      exact expect_image J (g (I.map σ.toEmbedding))
    _ = _ := expect_image_conditioned_target I i x hi
      (fun S => 𝔼 T ∈ (Finset.univ : Finset β).powersetCard J.card, g S T)

theorem expect_eq_expect_fiber_of_card_eq {Ω β : Type*} [DecidableEq β]
    (s : Finset Ω) (t : Finset β) (f : Ω → β) (m : ℕ)
    (hmap : ∀ ω ∈ s, f ω ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter (fun ω => f ω = b)).card = m)
    (g : Ω → ℝ) :
    (𝔼 ω ∈ s, g ω) = 𝔼 b ∈ t, 𝔼 ω ∈ s.filter (fun ω => f ω = b), g ω := by
  classical
  have hcard : s.card = t.card * m := by
    have h := Finset.sum_card_fiberwise_eq_card_filter s t f
    rw [Finset.filter_eq_self.mpr hmap] at h
    calc
      s.card = ∑ b ∈ t, (s.filter (fun ω => f ω = b)).card := h.symm
      _ = ∑ _b ∈ t, m := Finset.sum_congr rfl hfiber
      _ = t.card * m := by simp
  have hsum : (∑ b ∈ t, 𝔼 ω ∈ s.filter (fun ω => f ω = b), g ω) =
      (∑ ω ∈ s, g ω) / (m : ℝ) := by
    calc
      _ = ∑ b ∈ t, (∑ ω ∈ s.filter (fun ω => f ω = b), g ω) / (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.expect_eq_sum_div_card, hfiber b hb]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_fiberwise_of_maps_to hmap]
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, hsum, hcard]
  simp only [Nat.cast_mul, div_div, mul_comm]

theorem target_fiber_card_eq [Fintype α] (i x y : α) :
    ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x)).card) =
    ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = y)).card) := by
  classical
  let τ := Equiv.swap x y
  apply Finset.card_equiv (postcompose τ)
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    change τ (σ i) = y
    simp [τ, h]
  · intro h
    apply τ.injective
    change τ (σ i) = y at h
    simpa [τ] using h

theorem expect_position [Fintype α] (i : α) (g : α → ℝ) :
    (𝔼 σ : Equiv.Perm α, g (σ i)) = 𝔼 x : α, g x := by
  classical
  let m := ((Finset.univ : Finset (Equiv.Perm α)).filter (fun σ => σ i = i)).card
  have hm : 0 < m := Finset.card_pos.mpr ⟨Equiv.refl α, by simp⟩
  apply expect_comp_of_fiber_card_eq (Finset.univ : Finset (Equiv.Perm α))
    (Finset.univ : Finset α) (fun σ : Equiv.Perm α => σ i) m hm
    (fun _ _ => Finset.mem_univ _)
  intro x _
  exact target_fiber_card_eq i x i

theorem target_probability [Fintype α] (i x : α) :
    (𝔼 σ : Equiv.Perm α, if σ i = x then (1 : ℝ) else 0) =
      1 / (Fintype.card α : ℝ) := by
  classical
  simpa [Fintype.expect_eq_sum_div_card] using
    expect_position i (fun y => if y = x then (1 : ℝ) else 0)

theorem expect_by_target [Fintype α] (i : α) (g : Equiv.Perm α → ℝ) :
    (𝔼 σ : Equiv.Perm α, g σ) =
      𝔼 x : α, 𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm α => σ i = x), g σ := by
  classical
  apply expect_eq_expect_fiber_of_card_eq (Finset.univ : Finset (Equiv.Perm α))
    (Finset.univ : Finset α) (fun σ : Equiv.Perm α => σ i)
    ((Finset.univ.filter (fun σ : Equiv.Perm α => σ i = i)).card)
    (fun _ _ => Finset.mem_univ _)
  intro x _
  exact target_fiber_card_eq i x i

end Balanced.PermutationSubsetLaw

end OAI
