import OAI.Algebra.Finitistic.Dimension.PDBalancedRight
import OAI.Algebra.Finitistic.Dimension.PDRadical

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

abbrev radicalProduct := Ring.jacobson A • (⊤ : Submodule A N)
abbrev Top := N ⧸ radicalProduct (A := A) N

def residuePair : Residue (A := A) →ₗ[k] N →ₗ[k] Top (A := A) N := by
  let f : A →ₗ[k] N →ₗ[k] Top (A := A) N :=
    { toFun := fun a =>
        { toFun := fun n => (radicalProduct N).mkQ (a • n)
          map_add' := fun x y => by simp [smul_add]
          map_smul' := fun c n => by simp [smul_comm a c] }
      map_add' := fun a b => by ext n; simp [add_smul]
      map_smul' := fun c a => by ext n; simp [smul_assoc] }
  exact ((rightRadical (A := A)).restrictScalars k).liftQ f (by
    intro a ha
    ext n
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul ha mem_top)

@[simp] theorem residuePair_mk (a : A) (n : N) :
    residuePair (k := k) N (Submodule.Quotient.mk a) n =
      (radicalProduct N).mkQ (a • n) := rfl

def residueEval : BalancedTensor.Tensor k A (Residue (A := A)) N →ₗ[k] Top (A := A) N :=
  BalancedTensor.lift (residuePair (k := k) N) (by
    intro a s n
    induction s using Submodule.Quotient.induction_on with
    | _ b => change (radicalProduct N).mkQ ((b*a) • n) = _; rw [mul_smul]; rfl)

def residueInverse : Top (A := A) N →ₗ[k] BalancedTensor.Tensor k A (Residue (A := A)) N :=
  ((radicalProduct (A := A) N).restrictScalars k).liftQ
    (BalancedTensor.mk k A (Residue (A := A)) N (Submodule.Quotient.mk (1 : A))) (by
      intro n hn
      exact mk_radical_zero (k := k) (Residue (A := A)) residue_annihilated n hn _)

@[simp] theorem residueEval_mk (a : A) (n : N) :
    residueEval (k := k) N (BalancedTensor.mk k A (Residue (A := A)) N
      (Submodule.Quotient.mk a) n) = (radicalProduct N).mkQ (a • n) := rfl

@[simp] theorem residueInverse_mk (n : N) :
    residueInverse (k := k) N ((radicalProduct N).mkQ n) =
      BalancedTensor.mk k A (Residue (A := A)) N (Submodule.Quotient.mk (1 : A)) n := rfl

/-- The actual noncommutative tensor/quotient identification in cor:pd-detection. -/
def residueTensorEquiv : BalancedTensor.Tensor k A (Residue (A := A)) N ≃ₗ[k] Top (A := A) N where
  __ := residueEval (k := k) N
  invFun := residueInverse (k := k) N
  left_inv z := by
    change residueInverse (k := k) N (residueEval (k := k) N z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht s n =>
      induction s using Submodule.Quotient.induction_on with
      | _ a =>
        rw [residueEval_mk, residueInverse_mk, ← BalancedTensor.balance]
        congr 2
        change Submodule.Quotient.mk ((1 : A)*a) = Submodule.Quotient.mk a
        rw [one_mul]
    | ha x y hx hy => simp [hx,hy]
  right_inv z := by
    induction z using Submodule.Quotient.induction_on with
    | _ n =>
      change residueEval (k := k) N (residueInverse (k := k) N ((radicalProduct N).mkQ n)) = _
      rw [residueInverse_mk, residueEval_mk, one_smul]
      rfl

/-- Nakayama proves tensor detection for every finitely generated nonzero module. -/
theorem residueTensor_nontrivial [Module.Finite A N] [Nontrivial N] :
    Nontrivial (BalancedTensor.Tensor k A (Residue (A := A)) N) := by
  have := PDRadical.quotient_radical_nontrivial (A := A) N
  exact (residueTensorEquiv (k := k) N).toEquiv.nontrivial
end LittleFinitistic.PDTensor

end

end OAI
