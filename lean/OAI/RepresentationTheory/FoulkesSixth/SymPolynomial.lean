import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.PolynomialSpan
import OAI.RepresentationTheory.FoulkesSixth.SymDual

namespace OAI

noncomputable section

namespace Foulkes.SymPolynomial
universe u
open Module MvPolynomial SymmetricTensor
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {n : ℕ} (B : Basis (Fin n) ℂ V) (b : ℕ)

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℂ
abbrev H (n b : ℕ) := homogeneousSubmodule (Fin n) ℂ b

def linearPolynomial : V →ₗ[ℂ] Poly n where
  toFun v := ∑ i, B.equivFun v i • X i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [smul_smul, Finset.smul_sum]

@[simp] lemma linearPolynomial_apply (v : V) :
    linearPolynomial B v = ∑ i, B.equivFun v i • X i := rfl

lemma eval_linearPolynomial (x : Fin n → ℂ) (v : V) :
    eval x (linearPolynomial B v) = B.constr ℂ x v := by
  have h : B.constr ℂ x v = ∑ i, B.equivFun v i * x i := by
    conv_lhs => rw [← B.sum_equivFun v]
    simp
  rw [h]
  simp [linearPolynomial, MvPolynomial.smul_eq_C_mul]

def tensorPolynomial : T b V →ₗ[ℂ] Poly n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin b) (Poly n)).compLinearMap
    (fun _ => linearPolynomial B))

@[simp] lemma tensorPolynomial_tprod (v : Fin b → V) :
    tensorPolynomial B b (PiTensorProduct.tprod ℂ v) = ∏ i, linearPolynomial B (v i) := by
  simp [tensorPolynomial]

def polynomial : Sym b V →ₗ[ℂ] Poly n :=
  (tensorPolynomial B b).comp (symmetricTensors b V).subtype

@[simp] lemma polynomial_power (v : V) :
    polynomial B b (power b V v) = linearPolynomial B v ^ b := by
  simp [polynomial, power]

lemma polynomial_eval (x : Fin n → ℂ) (v : Sym b V) :
    eval x (polynomial B b v) = pairing b (power b (Dual ℂ V) (B.constr ℂ x)) v := by
  have hh : (aeval x).toLinearMap.comp (polynomial B b) =
      pairing b (power b (Dual ℂ V) (B.constr ℂ x)) := by
    apply symMap_ext
    intro v
    change eval x (polynomial B b (power b V v)) = _
    rw [polynomial_power, eval_pow, eval_linearPolynomial, pairing_power]
  exact DFunLike.congr_fun hh v

variable [FiniteDimensional ℂ V]

lemma polynomial_injective : Function.Injective (polynomial B b) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (LinearMap.ker_eq_bot').mpr
  intro v hv
  apply (Module.forall_dual_apply_eq_zero_iff ℂ v).mp
  intro l
  have hp : (pairing b (V := V)).flip v = 0 := by
    apply symMap_ext
    intro d
    obtain ⟨x, rfl⟩ := (B.constr ℂ).surjective d
    change pairing b (power b (Dual ℂ V) (B.constr ℂ x)) v = 0
    rw [← polynomial_eval, hv, map_zero]
  have hh := DFunLike.congr_fun hp ((dualEquiv b (V := V)).symm l)
  change dualEquiv b ((dualEquiv b (V := V)).symm l) v = 0 at hh
  rwa [LinearEquiv.apply_symm_apply] at hh

omit [FiniteDimensional ℂ V] in
lemma polynomial_range : (polynomial B b).range = H n b := by
  change (polynomial B b).range = homogeneousSubmodule (Fin n) ℂ b
  rw [← Submodule.map_top, ← span_power b V, LinearMap.map_span,
    PolynomialSpan.homogeneous_eq_span_powers]
  congr 1
  ext p
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨B.equivFun v, (polynomial_power B b v).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨power b V (B.equivFun.symm x), ⟨_, rfl⟩, ?_⟩
    simp

def equiv : Sym b V ≃ₗ[ℂ] H n b :=
  (LinearEquiv.ofInjective (polynomial B b) (polynomial_injective B b)).trans
    (LinearEquiv.ofEq _ _ (polynomial_range B b))

@[simp] lemma equiv_coe (v : Sym b V) : (equiv B b v : Poly n) = polynomial B b v := rfl

end Foulkes.SymPolynomial

end

end OAI
