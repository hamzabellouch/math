import Mathlib

namespace OAI


noncomputable section

namespace Problem355.PlaneFunctional

variable {ι K : Type*} [Fintype ι] [Field K]

theorem exists_kernel_dot_eq_one (x d : ι → K) (hx : x ≠ 0)
    (hd : ¬ ∃ a : K, d = a • x) :
    ∃ v : ι → K, dotProduct x v = 0 ∧ dotProduct d v = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    apply hx
    funext i
    exact h i
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ (d i / x i) * x j := by
    by_contra! h
    apply hd
    refine ⟨d i / x i, ?_⟩
    funext j
    exact h j
  let u : ι → K := Pi.single j 1 - (x j / x i) • Pi.single i 1
  have hxu : dotProduct x u = 0 := by
    dsimp only [u]
    rw [dotProduct_sub, dotProduct_smul]
    simp only [dotProduct_single, mul_one, smul_eq_mul]
    rw [div_mul_cancel₀ _ hi, sub_self]
  have hduval : dotProduct d u = d j - (d i / x i) * x j := by
    dsimp only [u]
    rw [dotProduct_sub, dotProduct_smul]
    simp only [dotProduct_single, mul_one, smul_eq_mul]
    ring
  have hdu : dotProduct d u ≠ 0 := by
    rw [hduval]
    exact sub_ne_zero.mpr hj
  refine ⟨(dotProduct d u)⁻¹ • u, ?_, ?_⟩
  · rw [dotProduct_smul, hxu, smul_zero]
  · rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hdu]

def modularDotHom (q : ℕ) (d : ι → ZMod q) : (ι → ℤ) →+ ZMod q where
  toFun u := dotProduct d (fun i => (u i : ZMod q))
  map_zero' := by simp [dotProduct]
  map_add' u v := by
    simp only [Pi.add_apply, Int.cast_add, dotProduct, mul_add, Finset.sum_add_distrib]

theorem modularDot_surjective_of_plane_surjective (q : ℕ) [Fact q.Prime]
    (x d : ι → ZMod q) (hx : x ≠ 0)
    (hd : ¬ ∃ a : ZMod q, d = a • x)
    (L : AddSubgroup (ι → ℤ))
    (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
      ∃ w : L, ∀ i, ((w : ι → ℤ) i : ZMod q) = v i) :
    Function.Surjective ((modularDotHom q d).comp L.subtype) := by
  obtain ⟨v, hxv, hdv⟩ := exists_kernel_dot_eq_one x d hx hd
  intro a
  have hxa : dotProduct x (a • v) = 0 := by
    rw [dotProduct_smul, hxv, smul_zero]
  obtain ⟨w, hw⟩ := hL (a • v) hxa
  refine ⟨w, ?_⟩
  change dotProduct d (fun i => ((w : ι → ℤ) i : ZMod q)) = a
  simp only [hw]
  rw [dotProduct_smul, hdv, smul_eq_mul, mul_one]

theorem modular_equation_index (q : ℕ) [Fact q.Prime]
    (x d : ι → ZMod q) (hx : x ≠ 0)
    (hd : ¬ ∃ a : ZMod q, d = a • x)
    (L : AddSubgroup (ι → ℤ))
    (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
      ∃ w : L, ∀ i, ((w : ι → ℤ) i : ZMod q) = v i) :
    (((modularDotHom q d).comp L.subtype).ker).index = q := by
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr
      (modularDot_surjective_of_plane_surjective q x d hx hd L hL),
    AddSubgroup.card_top]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card q

end Problem355.PlaneFunctional

end

end OAI
