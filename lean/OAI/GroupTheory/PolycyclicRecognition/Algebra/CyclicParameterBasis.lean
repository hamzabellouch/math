import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialProductParameters
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! # A basis with the added time coordinate last -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ}

def cyclicCoordinateEquiv (b : Basis (Fin d) ℝ V) :
    (V × ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun x := Fin.snoc (b.equivFun x.1) x.2
  invFun z := (b.equivFun.symm (fun i => z i.castSucc), z (Fin.last d))
  left_inv x := by
    simp only [Fin.snoc_castSucc, Fin.snoc_last, LinearEquiv.symm_apply_apply]
  right_inv z := by
    simp only [LinearEquiv.apply_symm_apply]
    exact Fin.snoc_init_self z
  map_add' x y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Prod.snd_add, Pi.add_apply]
    · simp only [Fin.snoc_castSucc, Prod.fst_add, map_add, Pi.add_apply]
  map_smul' r x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, RingHom.id_apply, Prod.smul_snd, Pi.smul_apply]
    · simp only [Fin.snoc_castSucc, RingHom.id_apply, Prod.smul_fst, map_smul, Pi.smul_apply]

def cyclicParameterBasis (b : Basis (Fin d) ℝ V) (s : W ≃ₗ[ℝ] (V × ℝ)) :
    Basis (Fin (d + 1)) ℝ W :=
  Basis.ofEquivFun (s.trans (cyclicCoordinateEquiv b))

theorem cyclicParameterBasis_integer (b : Basis (Fin d) ℝ V)
    (s : W ≃ₗ[ℝ] (V × ℝ)) (z : Fin (d + 1) → ℤ) :
    s ((cyclicParameterBasis b s).equivFun.symm (fun i => (z i : ℝ))) =
      (b.equivFun.symm (fun i => (z i.castSucc : ℝ)), (z (Fin.last d) : ℝ)) := by
  rw [cyclicParameterBasis, Basis.equivFun_ofEquivFun]
  exact s.apply_symm_apply _

theorem transportedProductParameter_integer
    (b : Basis (Fin d) ℝ V) (p : V ≃ V) (s : W ≃ₗ[ℝ] (V × ℝ))
    (E : W ≃ (V × ℝ)) (z : Fin (d + 1) → ℤ) :
    E (transportedProductParameter p s E
      ((cyclicParameterBasis b s).equivFun.symm (fun i => (z i : ℝ)))) =
      (p (b.equivFun.symm (fun i => (z i.castSucc : ℝ))), (z (Fin.last d) : ℝ)) := by
  change E (E.symm ((p.prodCongr (Equiv.refl ℝ))
    (s ((cyclicParameterBasis b s).equivFun.symm (fun i => (z i : ℝ)))))) = _
  rw [E.apply_symm_apply, cyclicParameterBasis_integer]
  rfl

end PolycyclicRecognition

end

end OAI
