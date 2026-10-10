import OAI.Algebra.AuslanderReiten.Algebras.TrivialExtension
import OAI.Algebra.AuslanderReiten.Algebras.BaseRadical

namespace OAI

namespace ArExplicit.TrivialExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

def projection : TrivialExtension k A →ₐ[k] A where
  toFun := base
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by simp only [Algebra.algebraMap_eq_smul_one, base_smul, base_one]

@[simp] theorem projection_apply (a : TrivialExtension k A) : projection a = a.base := rfl

theorem projection_surjective : Function.Surjective (projection : TrivialExtension k A →ₐ[k] A) :=
  fun a => ⟨inl a, rfl⟩

theorem mul_eq_zero_of_base_eq_zero (a b : TrivialExtension k A)
    (ha : a.base = 0) (hb : b.base = 0) : a * b = 0 := by
  apply TrivialExtension.ext
  · simp [ha, hb]
  · ext c
    simp [ha, hb]

theorem projection_kernel_square :
    (RingHom.ker (projection : TrivialExtension k A →ₐ[k] A)) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  exact mul_eq_zero_of_base_eq_zero a b ha hb

theorem radical_eq_comap :
    Ring.jacobson (TrivialExtension k A) =
      Ideal.comap projection (Ring.jacobson A) := by
  apply jacobson_eq_comap_of_nil_kernel _ projection_surjective
  intro a ha
  exact ⟨2, by simpa only [pow_two] using mul_eq_zero_of_base_eq_zero a a ha ha⟩

theorem mem_jacobson_iff (a : TrivialExtension k A) :
    a ∈ Ring.jacobson (TrivialExtension k A) ↔ a.base ∈ Ring.jacobson A := by
  rw [radical_eq_comap]
  rfl

end ArExplicit.TrivialExtension

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

def diagonalAlg : T k q →ₐ[k] k × k :=
  (BaseAlgebra.diagonalAlg q).comp TrivialExtension.projection

theorem diagonalAlg_surjective : Function.Surjective (diagonalAlg q) :=
  (BaseAlgebra.diagonalAlg_surjective q).comp TrivialExtension.projection_surjective

theorem radical_eq_ker_diagonal :
    Ring.jacobson (T k q) = RingHom.ker (diagonalAlg q) := by
  ext a
  rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
  change (a.base.coeff Letter.e = 0 ∧ a.base.coeff Letter.f = 0) ↔
    (a.base.coeff Letter.e, a.base.coeff Letter.f) = (0, 0)
  simp only [Prod.mk.injEq]

noncomputable def semisimpleQuotientEquiv :
    (T k q ⧸ Ring.jacobson (T k q)) ≃ₐ[k] k × k :=
  (Ideal.quotientEquivAlgOfEq k (radical_eq_ker_diagonal q)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (diagonalAlg_surjective q))

theorem jacobson_fourth_ne_bot (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (Ring.jacobson (T k q)) ^ 4 ≠ ⊥ := by
  let J := Ring.jacobson (T k q)
  have hu : lower q Letter.u ∈ J := by
    rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
    exact ⟨by simp [lower, TrivialExtension.inl], by simp [lower, TrivialExtension.inl]⟩
  have ht : lower q Letter.t ∈ J := by
    rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
    exact ⟨by simp [lower, TrivialExtension.inl], by simp [lower, TrivialExtension.inl]⟩
  have hprod : ((lower q Letter.u * lower q Letter.t) * lower q Letter.u) *
      lower q Letter.t ∈ J ^ 4 := by
    have h4 := Ideal.mul_mem_mul (Ideal.mul_mem_mul (Ideal.mul_mem_mul hu ht) hu) ht
    simpa only [Submodule.pow_succ, Submodule.pow_zero, Submodule.one_mul] using h4
  intro h
  rw [h] at hprod
  have hb := congrArg TrivialExtension.base (show _ = 0 from hprod)
  exact BaseAlgebra.fourfold_product_ne_zero q hq hq1 hb

end ArExplicit.T

end OAI
