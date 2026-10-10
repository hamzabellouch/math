import OAI.Algebra.AuslanderReiten.Algebras.TrivialExtensionRadical
import OAI.Algebra.AuslanderReiten.Algebras.TensorRadical
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI

namespace ArExplicit

open TensorProduct

abbrev A (k : Type*) [Field k] (q : k) := T k q ⊗[k] T k q

theorem A_finrank (k : Type*) [Field k] (q : k) : Module.finrank k (A k q) = 400 := by
  rw [Module.finrank_tensorProduct, T_finrank]

namespace A

variable {k : Type*} [Field k] (q : k)

noncomputable def quotientCoordinates : (k × k) ⊗[k] (k × k) ≃ₐ[k] (k × k) × (k × k) :=
  (Algebra.TensorProduct.prodRight k k (k × k) k k).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid k k (k × k))
      (Algebra.TensorProduct.rid k k (k × k)))

theorem quotient_jacobson : Ring.jacobson ((k × k) ⊗[k] (k × k)) = ⊥ :=
  jacobson_eq_bot_of_equiv (quotientCoordinates (k := k)).toRingEquiv
    (jacobson_prod_eq_bot
      (jacobson_prod_eq_bot (field_jacobson_eq_bot k) (field_jacobson_eq_bot k))
      (jacobson_prod_eq_bot (field_jacobson_eq_bot k) (field_jacobson_eq_bot k)))

def quotientTensorMap : A k q →ₐ[k] (k × k) ⊗[k] (k × k) :=
  Algebra.TensorProduct.map (T.diagonalAlg q) (T.diagonalAlg q)

noncomputable def diagonalAlg : A k q →ₐ[k] (k × k) × (k × k) :=
  (quotientCoordinates (k := k)).toAlgHom.comp (quotientTensorMap q)

theorem radical_eq_ker_tensorMap :
    Ring.jacobson (A k q) = RingHom.ker (quotientTensorMap q) := by
  have hnil : IsNilpotent (RingHom.ker (T.diagonalAlg q)) := by
    rw [← T.radical_eq_ker_diagonal]
    exact finiteAlgebra_radical_isNilpotent (k := k)
  exact tensor_radical_eq_kernel (T.diagonalAlg q) (T.diagonalAlg q)
    (T.diagonalAlg_surjective q) (T.diagonalAlg_surjective q) hnil hnil quotient_jacobson

theorem radical_eq_ker_diagonal :
    Ring.jacobson (A k q) = RingHom.ker (diagonalAlg q) := by
  rw [radical_eq_ker_tensorMap]
  ext a
  change quotientTensorMap q a = 0 ↔
    (quotientCoordinates (k := k)) (quotientTensorMap q a) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (quotientCoordinates (k := k)).injective
    simpa only [map_zero] using h

theorem diagonalAlg_surjective : Function.Surjective (diagonalAlg q) :=
  (quotientCoordinates (k := k)).surjective.comp
    (Algebra.TensorProduct.map_surjective (T.diagonalAlg q) (T.diagonalAlg q)
      (T.diagonalAlg_surjective q) (T.diagonalAlg_surjective q))

noncomputable def semisimpleQuotientEquiv :
    (A k q ⧸ Ring.jacobson (A k q)) ≃ₐ[k] (k × k) × (k × k) :=
  (Ideal.quotientEquivAlgOfEq k (radical_eq_ker_diagonal q)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (diagonalAlg_surjective q))

def radicalU : A k q := T.lower q Letter.u ⊗ₜ[k] 1
def radicalT : A k q := T.lower q Letter.t ⊗ₜ[k] 1

theorem left_radical_mem {a : T k q} (ha : a ∈ Ring.jacobson (T k q)) (b : T k q) :
    a ⊗ₜ[k] b ∈ Ring.jacobson (A k q) := by
  apply nilpotentIdeal_le_jacobson
    (leftTensorIdeal (k := k) (S := T k q) (Ring.jacobson (T k q)))
    (leftTensorIdeal_isNilpotent _ (finiteAlgebra_radical_isNilpotent (k := k)))
  exact tmul_mem_leftTensorIdeal _ ha b

theorem radicalU_mem : radicalU q ∈ Ring.jacobson (A k q) := by
  apply left_radical_mem
  rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
  exact ⟨by simp [T.lower, TrivialExtension.inl], by simp [T.lower, TrivialExtension.inl]⟩

theorem radicalT_mem : radicalT q ∈ Ring.jacobson (A k q) := by
  apply left_radical_mem
  rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
  exact ⟨by simp [T.lower, TrivialExtension.inl], by simp [T.lower, TrivialExtension.inl]⟩

noncomputable def originalProjection : A k q →ₐ[k] BaseAlgebra k q :=
  TrivialExtension.projection.comp
    ((Algebra.TensorProduct.rid k k (T k q)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k (T k q))
        ((AlgHom.snd k k k).comp (T.diagonalAlg q))))

@[simp] theorem originalProjection_radicalU :
    originalProjection q (radicalU q) = BaseAlgebra.basisVector q Letter.u := by
  simp [originalProjection, radicalU, T.lower, TrivialExtension.inl]

@[simp] theorem originalProjection_radicalT :
    originalProjection q (radicalT q) = BaseAlgebra.basisVector q Letter.t := by
  simp [originalProjection, radicalT, T.lower, TrivialExtension.inl]

theorem fourfold_product_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ((radicalU q * radicalT q) * radicalU q) * radicalT q ≠ 0 := by
  intro h
  have h' := congrArg (originalProjection q) h
  simp only [map_mul, originalProjection_radicalU, originalProjection_radicalT, map_zero] at h'
  exact BaseAlgebra.fourfold_product_ne_zero q hq hq1 h'

theorem jacobson_fourth_ne_bot (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (Ring.jacobson (A k q)) ^ 4 ≠ ⊥ := by
  have h4 := Ideal.mul_mem_mul
    (Ideal.mul_mem_mul (Ideal.mul_mem_mul (radicalU_mem q) (radicalT_mem q))
      (radicalU_mem q)) (radicalT_mem q)
  have hmem : ((radicalU q * radicalT q) * radicalU q) * radicalT q ∈
      (Ring.jacobson (A k q)) ^ 4 := by
    simpa only [Submodule.pow_succ, Submodule.pow_zero, Submodule.one_mul] using h4
  intro h
  rw [h] at hmem
  exact fourfold_product_ne_zero q hq hq1 hmem

end A
end ArExplicit

end OAI
