import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev Variables (E : Type*) := ℝ × E × E

def jacobian (e : E) (L H : E →L[ℝ] E) : Variables E →L[ℝ] Variables E :=
  ({ toFun := fun z => (inner ℝ e z.2.2, L z.2.1 + z.1 • e, L z.2.2 - H z.2.1)
     map_add' := by
       intro z w
       apply Prod.ext
       · simp [inner_add_right]
       · apply Prod.ext
         · simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
           module
         · simp only [Prod.fst_add, Prod.snd_add, map_add]
           module
     map_smul' := by
       intro r z
       apply Prod.ext
       · simp [real_inner_smul_right]
       · apply Prod.ext <;> simp [smul_add, smul_sub, smul_smul] } :
    Variables E →ₗ[ℝ] Variables E).toContinuousLinearMap

@[simp] lemma jacobian_apply (e : E) (L H : E →L[ℝ] E) (z : Variables E) :
    jacobian e L H z = (inner ℝ e z.2.2, L z.2.1 + z.1 • e, L z.2.2 - H z.2.1) := rfl

theorem jacobian_injective (e : E) (he : e ≠ 0) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (hH : ∀ u, u ≠ 0 → 0 < inner ℝ u (H u)) :
    Function.Injective (jacobian e L.toContinuousLinearMap H) := by
  suffices hk : ∀ z, jacobian e L.toContinuousLinearMap H z = 0 → z = 0 by
    intro z w hzw
    exact sub_eq_zero.mp (hk (z-w) (by rw [map_sub, hzw, sub_self]))
  intro z hz
  have hr : inner ℝ e z.2.2 = 0 := congrArg Prod.fst hz
  have hf : L z.2.1 + z.1 • e = 0 := congrArg (fun w : Variables E => w.2.1) hz
  have hg : L z.2.2 - H z.2.1 = 0 := congrArg (fun w : Variables E => w.2.2) hz
  have hLe : L z.2.1 = -z.1 • e := by
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hf
  have hHL : H z.2.1 = L z.2.2 := (sub_eq_zero.mp hg).symm
  have hq : inner ℝ z.2.1 (H z.2.1) = 0 := by
    have hs : inner ℝ (L z.2.1) z.2.2 = inner ℝ z.2.1 (L z.2.2) := hL _ _
    rw [hHL, ← hs]
    rw [hLe, real_inner_smul_left, hr, mul_zero]
  have hu : z.2.1 = 0 := by
    by_contra hn
    exact (ne_of_gt (hH _ hn)) hq
  have hh : z.1 = 0 := by
    rw [hu, map_zero, zero_add] at hf
    exact (smul_eq_zero.mp hf).resolve_right he
  have hp : z.2.2 = 0 := by
    apply L.injective
    simpa only [hu, map_zero, sub_zero] using hg
  exact Prod.ext hh (Prod.ext hu hp)

theorem exists_jacobian_equiv (e : E) (he : e ≠ 0) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (hH : ∀ u, u ≠ 0 → 0 < inner ℝ u (H u)) :
    ∃ J : Variables E ≃L[ℝ] Variables E, ∀ z, J z = jacobian e L.toContinuousLinearMap H z := by
  have hi := jacobian_injective e he L hL H hH
  let J := LinearEquiv.ofBijective (jacobian e L.toContinuousLinearMap H).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨J.toContinuousLinearEquiv, fun _ => rfl⟩

lemma inverse_elimination (e : E) (L : E ≃L[ℝ] E)
    (hL : L.toLinearEquiv.toLinearMap.IsSymmetric) (H : E →L[ℝ] E)
    (z rhs : Variables E) (hz : jacobian e L.toContinuousLinearMap H z = rhs) :
    z.2.1 = L.symm rhs.2.1 - z.1 • L.symm e ∧
    z.2.2 = L.symm rhs.2.2 + L.symm (H (L.symm rhs.2.1)) - z.1 • L.symm (H (L.symm e)) ∧
    z.1 * inner ℝ (L.symm e) (H (L.symm e)) =
      inner ℝ (L.symm e) rhs.2.2 + inner ℝ (L.symm e) (H (L.symm rhs.2.1)) - rhs.1 := by
  have hr : inner ℝ e z.2.2 = rhs.1 := congrArg Prod.fst hz
  have hf : L z.2.1 + z.1 • e = rhs.2.1 := congrArg (fun w : Variables E => w.2.1) hz
  have hg : L z.2.2 - H z.2.1 = rhs.2.2 := congrArg (fun w : Variables E => w.2.2) hz
  have hu : z.2.1 = L.symm rhs.2.1 - z.1 • L.symm e := by
    apply L.injective
    simp only [map_sub, map_smul, L.apply_symm_apply]
    exact eq_sub_iff_add_eq.mpr hf
  have hp : z.2.2 = L.symm rhs.2.2 + L.symm (H (L.symm rhs.2.1)) - z.1 • L.symm (H (L.symm e)) := by
    apply L.injective
    simp only [map_sub, map_add, map_smul, L.apply_symm_apply]
    rw [hu, map_sub, map_smul] at hg
    rw [sub_eq_iff_eq_add] at hg
    rw [hg]
    module
  refine ⟨hu,hp,?_⟩
  rw [hp, inner_sub_right, inner_add_right, real_inner_smul_right] at hr
  have hs := hL.toLinearMap_symm
  have heq (v : E) : inner ℝ e (L.symm v) = inner ℝ (L.symm e) v := (hs e v).symm
  rw [heq, heq, heq] at hr
  linarith

end
end CurrentKS.KKT

end OAI
