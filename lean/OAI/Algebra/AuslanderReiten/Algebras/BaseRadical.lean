import OAI.Algebra.AuslanderReiten.Algebras.BaseAlgebra
import OAI.Algebra.AuslanderReiten.Algebras.Radical
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

namespace ArExplicit.BaseAlgebra

open ArExplicit.Letter

variable {k : Type*} [Field k] (q : k)

def eCharacter : BaseAlgebra k q →+* k where
  toFun a := a.coeff e
  map_one' := by simp
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def fCharacter : BaseAlgebra k q →+* k where
  toFun a := a.coeff f
  map_one' := by simp
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem eCharacter_surjective : Function.Surjective (eCharacter q) := by
  intro a
  refine ⟨a • basisVector q e, ?_⟩
  change (a • basisVector q e).coeff e = a
  simp

theorem fCharacter_surjective : Function.Surjective (fCharacter q) := by
  intro a
  refine ⟨a • basisVector q f, ?_⟩
  change (a • basisVector q f).coeff f = a
  simp

def diagonal : BaseAlgebra k q →+* k × k := (eCharacter q).prod (fCharacter q)

theorem fifth_power_eq_zero (a : BaseAlgebra k q) (he : a.coeff e = 0)
    (hf : a.coeff f = 0) : a ^ 5 = 0 := by
  ext i
  cases i <;> simp [pow_succ, product, he, hf]

private theorem field_jacobson : Ring.jacobson k = ⊥ := by
  let : (⊥ : Ideal k).IsMaximal := Ideal.bot_isMaximal
  exact le_antisymm (Ring.jacobson_le_of_isMaximal ⊥) bot_le

theorem mem_jacobson_iff (a : BaseAlgebra k q) :
    a ∈ Ring.jacobson (BaseAlgebra k q) ↔ a.coeff e = 0 ∧ a.coeff f = 0 := by
  constructor
  · intro ha
    have : RingHomSurjective (eCharacter q) := ⟨eCharacter_surjective q⟩
    have : RingHomSurjective (fCharacter q) := ⟨fCharacter_surjective q⟩
    have he := Ring.le_comap_jacobson (eCharacter q) ha
    have hf := Ring.le_comap_jacobson (fCharacter q) ha
    rw [field_jacobson] at he hf
    exact ⟨he, hf⟩
  · rintro ⟨he, hf⟩
    have hn : RingHom.ker (diagonal q) ≤ Ring.jacobson (BaseAlgebra k q) := by
      apply ArExplicit.nilIdeal_le_jacobson
      intro b hb
      change (b.coeff e, b.coeff f) = (0, 0) at hb
      exact ⟨5, fifth_power_eq_zero q b (congrArg Prod.fst hb) (congrArg Prod.snd hb)⟩
    apply hn
    change (a.coeff e, a.coeff f) = (0, 0)
    exact Prod.ext he hf

def diagonalAlg : BaseAlgebra k q →ₐ[k] k × k where
  __ := diagonal q
  commutes' c := by
    apply Prod.ext
    · change (algebraMap k (BaseAlgebra k q) c).coeff e = c
      rw [Algebra.algebraMap_eq_smul_one]
      simp
    · change (algebraMap k (BaseAlgebra k q) c).coeff f = c
      rw [Algebra.algebraMap_eq_smul_one]
      simp

theorem diagonalAlg_surjective : Function.Surjective (diagonalAlg q) := by
  rintro ⟨a, b⟩
  refine ⟨a • basisVector q e + b • basisVector q f, ?_⟩
  apply Prod.ext
  · change (a • basisVector q e + b • basisVector q f).coeff e = a
    simp
  · change (a • basisVector q e + b • basisVector q f).coeff f = b
    simp

theorem radical_eq_ker_diagonal :
    Ring.jacobson (BaseAlgebra k q) = RingHom.ker (diagonalAlg q) := by
  ext a
  rw [mem_jacobson_iff]
  change (a.coeff e = 0 ∧ a.coeff f = 0) ↔ (a.coeff e, a.coeff f) = (0, 0)
  simp only [Prod.mk.injEq]

noncomputable def semisimpleQuotientEquiv :
    (BaseAlgebra k q ⧸ Ring.jacobson (BaseAlgebra k q)) ≃ₐ[k] k × k :=
  (Ideal.quotientEquivAlgOfEq k (radical_eq_ker_diagonal q)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (diagonalAlg_surjective q))

theorem jacobson_fourth_ne_bot (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (Ring.jacobson (BaseAlgebra k q)) ^ 4 ≠ ⊥ := by
  let J := Ring.jacobson (BaseAlgebra k q)
  have hu : basisVector q u ∈ J := (mem_jacobson_iff q _).mpr (by simp)
  have ht : basisVector q t ∈ J := (mem_jacobson_iff q _).mpr (by simp)
  have hprod : ((basisVector q u * basisVector q t) * basisVector q u) *
      basisVector q t ∈ J ^ 4 := by
    have h2 := Ideal.mul_mem_mul hu ht
    have h3 := Ideal.mul_mem_mul h2 hu
    have h4 := Ideal.mul_mem_mul h3 ht
    simpa only [Submodule.pow_succ, Submodule.pow_zero, Submodule.one_mul] using h4
  intro h
  rw [h] at hprod
  exact fourfold_product_ne_zero q hq hq1 hprod

end ArExplicit.BaseAlgebra

end OAI
