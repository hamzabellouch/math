import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalTermMaps
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)

def horizontalBetween (n m a b : ℤ) (h : n+1=m) (hab : a+1=b) :
    Term k B P Z a (n + -a) →ₗ[B] Term k B P Z b (m + -b) :=
  termMap (P.d a b) (eqToHom (congrArg Z.X (show n + -a = m + -b by omega)))

def entryBetween (n m a b : ℤ) (h : n+1=m) :
    Term k B P Z a (n + -a) →ₗ[B] Term k B P Z b (m + -b) :=
  if hab : a+1=b then horizontalBetween k B P Z n m a b h hab else 0

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The exact differential of the B-valued total, in arbitrary consecutive total degrees. -/
theorem total_d_apply (n m : ℤ) (h : n+1=m) (x : TotalTerm k B P p Z n) (j : Fin l) :
    ((total k B P p hp Z).d n m).hom x j =
      (show Term k B P Z (p j) (m + -(p j)) from
        ((ComplexTensor.column k B (right k B P) Z (p j)).d n m).hom (x j)) +
      ∑ i : Fin l, entryBetween k B P Z n m (p i) (p j) h (x i) := by
  subst m
  change ((ComplexTensor.finiteTotal k B (right k B P) Z p hp).d n (n+1)).hom x j = _
  simp only [ComplexTensor.finiteTotal, FiniteColumnComplex.total,
    FiniteColumnComplex.complex_d_hom]
  change (show Term k B P Z (p j) ((n+1) + -(p j)) from
      ((ComplexTensor.column k B (right k B P) Z (p j)).d n (n+1)).hom (x j)) +
    (show Term k B P Z (p j) ((n+1) + -(p j)) from
      ComplexTensor.matrix k B (right k B P) Z p n x j) = _
  erw [ComplexTensor.matrix_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold entryBetween ComplexTensor.entry
  split_ifs with h
  · rfl
  · rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
