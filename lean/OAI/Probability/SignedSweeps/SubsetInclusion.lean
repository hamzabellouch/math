import OAI.Probability.SignedSweeps.Irreducibility

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {A : Type*} [DecidableEq A]

def fairSwapWeights (a b : A) (p : A → ℝ) (x : A) : ℝ :=
  (p x + p (Equiv.swap a b x)) / 2

lemma fairSwapWeights_nonneg (a b : A) {p : A → ℝ} (hp : ∀ x, 0 ≤ p x) (x : A) :
    0 ≤ fairSwapWeights a b p x := by
  exact div_nonneg (add_nonneg (hp x) (hp _)) (by norm_num)

lemma fairSwapWeights_fixed (a b : A) (p : A → ℝ) {x : A} (ha : x ≠ a) (hb : x ≠ b) :
    fairSwapWeights a b p x = p x := by
  simp only [fairSwapWeights, Equiv.swap_apply_of_ne_of_ne ha hb]
  ring

lemma fairSwapWeights_left (a b : A) (p : A → ℝ) :
    fairSwapWeights a b p a = (p a + p b) / 2 := by
  simp [fairSwapWeights]

lemma fairSwapWeights_right (a b : A) (p : A → ℝ) :
    fairSwapWeights a b p b = (p a + p b) / 2 := by
  simp only [fairSwapWeights, Equiv.swap_apply_right, add_comm]

lemma prod_swap_fixed (a b : A) (p : A → ℝ) (T : Finset A) (ha : a ∉ T) (hb : b ∉ T) :
    (∏ x ∈ T, p (Equiv.swap a b x)) = ∏ x ∈ T, p x := by
  apply Finset.prod_congr rfl
  intro x hx
  rw [Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact ha hx)
    (by rintro rfl; exact hb hx)]

lemma prod_fairSwapWeights_fixed (a b : A) (p : A → ℝ) (T : Finset A)
    (ha : a ∉ T) (hb : b ∉ T) :
    (∏ x ∈ T, fairSwapWeights a b p x) = ∏ x ∈ T, p x := by
  apply Finset.prod_congr rfl
  intro x hx
  exact fairSwapWeights_fixed a b p (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx))

lemma fair_swap_product_le (a b : A) (p : A → ℝ) (hp : ∀ x, 0 ≤ p x) (T : Finset A) :
    ((∏ x ∈ T, p x) + (∏ x ∈ T, p (Equiv.swap a b x))) / 2 ≤
      ∏ x ∈ T, fairSwapWeights a b p x := by
  by_cases hab : a = b
  · subst b
    have he : fairSwapWeights a a p = p := by funext x; simp [fairSwapWeights]
    simp only [he, Equiv.swap_self, Equiv.refl_apply]
    linarith
  have hs (T : Finset A) (ha : a ∈ T) (hb : b ∉ T) :
      ((∏ x ∈ T, p x) + (∏ x ∈ T, p (Equiv.swap a b x))) / 2 =
        ∏ x ∈ T, fairSwapWeights a b p x := by
    rw [← T.mul_prod_erase p ha, ← T.mul_prod_erase (fun x => p (Equiv.swap a b x)) ha,
      ← T.mul_prod_erase (fairSwapWeights a b p) ha]
    rw [prod_swap_fixed a b p (T.erase a) (by simp) (by simp [hb]),
      prod_fairSwapWeights_fixed a b p (T.erase a) (by simp) (by simp [hb]),
      fairSwapWeights_left, Equiv.swap_apply_left]
    ring
  by_cases ha : a ∈ T
  · by_cases hb : b ∈ T
    · have hb' : b ∈ T.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
      have he (f : A → ℝ) : (∏ x ∈ T, f x) =
          f a * (f b * ∏ x ∈ (T.erase a).erase b, f x) := by
        rw [← T.mul_prod_erase f ha, ← (T.erase a).mul_prod_erase f hb']
      rw [he p, he (fun x => p (Equiv.swap a b x)), he (fairSwapWeights a b p),
        prod_swap_fixed a b p ((T.erase a).erase b) (by simp) (by simp),
        prod_fairSwapWeights_fixed a b p ((T.erase a).erase b) (by simp) (by simp),
        fairSwapWeights_left, fairSwapWeights_right, Equiv.swap_apply_left, Equiv.swap_apply_right]
      have hr := Finset.prod_nonneg (s := (T.erase a).erase b) (f := p) (fun x _ => hp x)
      nlinarith [mul_nonneg (sq_nonneg (p a - p b)) hr]
    · exact (hs T ha hb).le
  · by_cases hb : b ∈ T
    · have hs' := hs (T.image (Equiv.swap a b))
      have hi : a ∈ T.image (Equiv.swap a b) := Finset.mem_image.mpr ⟨b, hb, Equiv.swap_apply_right a b⟩
      have hn : b ∉ T.image (Equiv.swap a b) := by
        intro ht
        obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
        have hx' : x = a := (Equiv.swap a b).injective (he.trans (Equiv.swap_apply_left a b).symm)
        exact ha (hx' ▸ hx)
      have he := hs' hi hn
      rw [Finset.prod_image (Equiv.swap a b).injective.injOn,
        Finset.prod_image (Equiv.swap a b).injective.injOn,
        Finset.prod_image (Equiv.swap a b).injective.injOn] at he
      simp only [Equiv.swap_apply_self] at he
      have hweights (x : A) : fairSwapWeights a b p (Equiv.swap a b x) =
          fairSwapWeights a b p x := by simp [fairSwapWeights, add_comm]
      simp only [hweights] at he
      linarith [he]
    · rw [prod_swap_fixed a b p T ha hb, prod_fairSwapWeights_fixed a b p T ha hb]
      linarith

def fairSwapInclusion (a b : A) (M : Finset A → ℝ) (T : Finset A) : ℝ :=
  (M T + M (T.image (Equiv.swap a b))) / 2

lemma fairSwapInclusion_bound (a b : A) (M : Finset A → ℝ) (p : A → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) (T : Finset A) :
    fairSwapInclusion a b M T ≤ ∏ x ∈ T, fairSwapWeights a b p x := by
  calc
    _ ≤ ((∏ x ∈ T, p x) + ∏ x ∈ T.image (Equiv.swap a b), p x) / 2 := by
      exact div_le_div_of_nonneg_right (add_le_add (hM T) (hM _)) (by norm_num)
    _ = ((∏ x ∈ T, p x) + ∏ x ∈ T, p (Equiv.swap a b x)) / 2 := by
      rw [Finset.prod_image (Equiv.swap a b).injective.injOn]
    _ ≤ _ := fair_swap_product_le a b p hp T

end SignedSweeps
end

end OAI
