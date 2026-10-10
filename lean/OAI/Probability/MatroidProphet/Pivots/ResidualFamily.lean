import OAI.Probability.MatroidProphet.Pivots.Reindex
import OAI.Probability.MatroidProphet.Pivots.Entropy

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α O₁ O₂ : Type*} [Fintype α] [Fintype O₁] [LinearOrder O₁]
    [Fintype O₂] [LinearOrder O₂] {n : ℕ}

noncomputable def smallSubsets (U : Finset α) (q : ℕ) : Finset (Finset α) := by
  classical
  exact U.powerset.filter (fun J => J.card ≤ q)

lemma mem_smallSubsets
    {α : Type u_1} [Fintype α] (U J : Finset α) (q : ℕ) :
    J ∈ smallSubsets U q ↔ J ⊆ U ∧ J.card ≤ q := by
  classical
  simp [smallSubsets]

lemma card_smallSubsets_le (U : Finset α) (q : ℕ) :
    (smallSubsets U q).card ≤ binomialSum U.card q := by
  classical
  have hsub : smallSubsets U q ⊆ (Finset.Iic q).biUnion (fun k => U.powersetCard k) := by
    intro J hJ
    obtain ⟨hJU, hJq⟩ := (mem_smallSubsets U J q).1 hJ
    exact mem_biUnion.mpr ⟨J.card, mem_Iic.mpr hJq, mem_powersetCard.mpr ⟨hJU, rfl⟩⟩
  calc
    (smallSubsets U q).card ≤ ((Finset.Iic q).biUnion (fun k => U.powersetCard k)).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Iic q, (U.powersetCard k).card := card_biUnion_le
    _ = binomialSum U.card q := by simp [binomialSum]

noncomputable def intersectionFamily (F G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (F ×ˢ G).image (fun p => p.1 ∩ p.2)

lemma card_intersectionFamily_le (F G : Finset (Finset (Fin n))) :
    (intersectionFamily F G).card ≤ F.card * G.card := by
  exact card_image_le.trans_eq (card_product F G)

noncomputable def residualFamily (M : Matroid α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) : Finset (Finset (Fin n)) := by
  classical
  exact (smallSubsets U q).biUnion fun J => (smallSubsets U q).biUnion fun Z =>
    intersectionFamily
      (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
      (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)

lemma mem_residualFamily (M : Matroid α) (U J Z : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (T₁ T₂ : Finset (Fin n))
    (hJ : J ⊆ U) (hJq : J.card ≤ q) (hZ : Z ⊆ U) (hZq : Z.card ≤ q)
    (hT₁ : T₁ ∈ freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
    (hT₂ : T₂ ∈ freeMarkedPatterns M old₂
      (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂) :
    T₁ ∩ T₂ ∈ residualFamily M U q old₁ old₂ mark₁ mark₂ test := by
  classical
  apply mem_biUnion.mpr
  refine ⟨J, (mem_smallSubsets U J q).2 ⟨hJ, hJq⟩, mem_biUnion.mpr ?_⟩
  refine ⟨Z, (mem_smallSubsets U Z q).2 ⟨hZ, hZq⟩, ?_⟩
  exact mem_image.mpr ⟨(T₁, T₂), mem_product.mpr ⟨hT₁, hT₂⟩, rfl⟩

lemma card_residualFamily_le (M : Matroid α) (d : α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (hU : (U : Set α) ⊆ M.E)
    (h₁ : ∀ o, old₁ o ∈ M.E) (h₂ : ∀ o, old₂ o ∈ M.E) :
    (residualFamily M U q old₁ old₂ mark₁ mark₂ test).card ≤
      (binomialSum U.card q) ^ 2 * (4 ^ (2 * q) * binomialSum n (2 * q)) ^ 2 := by
  classical
  let B := 4 ^ (2 * q) * binomialSum n (2 * q)
  let C := smallSubsets U q
  have hpair (J : Finset α) (hJ : J ∈ C) (Z : Finset α) (hZ : Z ∈ C) :
      (intersectionFamily
        (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
        (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)).card
        ≤ B ^ 2 := by
    obtain ⟨hJU, hJq⟩ := (mem_smallSubsets U J q).1 hJ
    obtain ⟨hZU, hZq⟩ := (mem_smallSubsets U Z q).1 hZ
    have hfirst : (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁).card ≤ B := by
      apply card_freeMarkedPatterns_le M d old₁ (fun a : J => a.val) test mark₁ (2 * q)
      · simpa using (show J.card ≤ 2 * q by omega)
      · intro o
        cases o with
        | inl o => exact h₁ o
        | inr a => exact hU (hJU a.property)
    have hsecond : (freeMarkedPatterns M old₂
        (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂).card ≤ B := by
      apply card_freeMarkedPatterns_le M d old₂
        (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂ (2 * q)
      · simpa using (show J.card + Z.card ≤ 2 * q by omega)
      · intro o
        cases o with
        | inl o => exact h₂ o
        | inr a =>
          cases a with
          | inl a => exact hU (hJU a.property)
          | inr a => exact hU (hZU a.property)
    exact (card_intersectionFamily_le _ _).trans ((Nat.mul_le_mul hfirst hsecond).trans_eq (pow_two B).symm)
  have hsum : (residualFamily M U q old₁ old₂ mark₁ mark₂ test).card ≤ C.card ^ 2 * B ^ 2 := by
    calc
      _ ≤ ∑ J ∈ C, ((C.biUnion fun Z => intersectionFamily
          (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
          (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂))).card :=
        card_biUnion_le
      _ ≤ ∑ J ∈ C, ∑ Z ∈ C, (intersectionFamily
          (freeMarkedPatterns M old₁ (fun a : J => a.val) test mark₁)
          (freeMarkedPatterns M old₂ (Sum.elim (fun a : J => a.val) (fun a : Z => a.val)) test mark₂)).card :=
        sum_le_sum fun _ _ => card_biUnion_le
      _ ≤ ∑ _J ∈ C, ∑ _Z ∈ C, B ^ 2 := sum_le_sum fun J hJ => sum_le_sum fun Z hZ => hpair J hJ Z hZ
      _ = C.card ^ 2 * B ^ 2 := by simp [pow_two, Nat.mul_assoc]
  exact hsum.trans (Nat.mul_le_mul_right (B ^ 2) (Nat.pow_le_pow_left (card_smallSubsets_le U q) 2))

lemma card_residualFamily_le_exp (M : Matroid α) (d : α) (U : Finset α) (q : ℕ)
    (old₁ : O₁ → α) (old₂ : O₂ → α) (mark₁ : O₁ → Bool) (mark₂ : O₂ → Bool)
    (test : Fin n → α) (hU : (U : Set α) ⊆ M.E)
    (h₁ : ∀ o, old₁ o ∈ M.E) (h₂ : ∀ o, old₂ o ∈ M.E)
    (hn : U.card = n) (κ : ℝ) (hκ : 2 ≤ κ) (hq : (q : ℝ) ≤ (n : ℝ) / κ) :
    ((residualFamily M U q old₁ old₂ mark₁ mark₂ test).card : ℝ) ≤
      Real.exp (1000 * Real.log κ / κ * n) := by
  have h := card_residualFamily_le M d U q old₁ old₂ mark₁ mark₂ test hU h₁ h₂
  rw [hn] at h
  exact (show ((residualFamily M U q old₁ old₂ mark₁ mark₂ test).card : ℝ) ≤
      (((binomialSum n q)^2 * (4^(2*q) * binomialSum n (2*q))^2 : ℕ) : ℝ) by exact_mod_cast h).trans
    (residual_raw_count_le_exp n q κ hκ hq)

end MatroidProphet.Pivots

end OAI
