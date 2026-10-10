import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTerms

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

abbrev totalTerm (n : ℤ) := ∀ i : Fin l, term k S A Q Z (p i) (n + -(p i))

def forgetTotalEquiv (n : ℤ) : totalTerm k S A Q Z p n ≃ₗ[k]
    FiniteColumnComplex.term (ComplexTensor.columns k A (rightComplex k S A Q) Z p) n :=
  LinearEquiv.piCongrRight (fun i => forgetEquiv k S A Q Z (p i) (n + -(p i)))

/-- The horizontal arrow map retains its left action and exact degree transport. -/
def entry (n : ℤ) (i j : Fin l) : term k S A Q Z (p i) (n + -(p i)) →ₗ[S]
    term k S A Q Z (p j) ((n+1) + -(p j)) :=
  if h : p i + 1 = p j then map k S A Q Z (Q.d (p i) (p j))
    (eqToHom (congrArg Z.X (by omega))) else 0

/-- The actual signed differential, now linear for the outside algebra. -/
def differential (n : ℤ) : totalTerm k S A Q Z p n →ₗ[S] totalTerm k S A Q Z p (n+1) :=
  LinearMap.pi (fun j =>
    ((-(p j)).negOnePow • map k S A Q Z (𝟙 (Q.X (p j)))
      (Z.d (n + -(p j)) ((n+1) + -(p j)))).comp (LinearMap.proj j) +
    ∑ i : Fin l, (entry k S A Q Z p n i j).comp (LinearMap.proj i))

theorem forget_entry (n : ℤ) (i j : Fin l) (z : term k S A Q Z (p i) (n + -(p i))) :
    forgetEquiv k S A Q Z (p j) ((n+1) + -(p j)) (entry k S A Q Z p n i j z) =
      ComplexTensor.entry k A (rightComplex k S A Q) Z p n i j
        (forgetEquiv k S A Q Z (p i) (n + -(p i)) z) := by
  unfold entry ComplexTensor.entry
  split_ifs with h
  · exact congrArg (fun f => f z) (forget_map k S A Q Z (Q.d (p i) (p j))
      (eqToHom (congrArg Z.X (show n + -(p i) = (n+1) + -(p j) by omega))))
  · exact map_zero _

/-- Forgetting the outside action gives exactly the previously verified signed differential. -/
theorem forget_differential (n : ℤ) (z : totalTerm k S A Q Z p n) :
    forgetTotalEquiv k S A Q Z p (n+1) (differential k S A Q Z p n z) =
      (FiniteColumnComplex.totalDifferential (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
        (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).d n
        (forgetTotalEquiv k S A Q Z p n z) := by
  funext j
  change forgetEquiv k S A Q Z (p j) ((n+1) + -(p j))
      ((differential k S A Q Z p n z) j) = _
  simp only [forgetTotalEquiv,differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,FiniteColumnComplex.totalDifferential,ComplexTensor.tensorHorizontal,
    FiniteColumnComplex.diagonal_apply,Pi.add_apply,ComplexTensor.matrix_apply]
  simp only [map_add,map_sum,LinearMap.smul_apply,ComplexTensor.column_d]
  apply congrArg₂ (· + ·)
  · change forgetEquiv k S A Q Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) •
          (map k S A Q Z (𝟙 (Q.X (p j))) (Z.d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) •
        (ComplexTensor.map k A (rightComplex k S A Q) Z (𝟙 ((rightComplex k S A Q).X (p j)))
          (Z.d (n + -(p j)) ((n+1) + -(p j)))
          (forgetEquiv k S A Q Z (p j) (n + -(p j)) (z j)))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (forget_map k S A Q Z (𝟙 (Q.X (p j)))
      (Z.d (n + -(p j)) ((n+1) + -(p j))))
  · apply Finset.sum_congr rfl
    intro i _
    exact forget_entry k S A Q Z p n i j (z i)

include hp in
theorem differential_square (n : ℤ) :
    (differential k S A Q Z p (n+1)).comp (differential k S A Q Z p n) = 0 := by
  apply LinearMap.ext
  intro z
  apply (forgetTotalEquiv k S A Q Z p ((n+1)+1)).injective
  change forgetTotalEquiv k S A Q Z p ((n+1)+1)
      (differential k S A Q Z p (n+1) (differential k S A Q Z p n z)) = _
  rw [forget_differential k S A Q Z p hp,forget_differential k S A Q Z p hp,LinearMap.zero_apply,map_zero]
  exact congrArg (fun f => f (forgetTotalEquiv k S A Q Z p n z))
    ((FiniteColumnComplex.totalDifferential (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
      (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).square n)

/-- Actual signed finite tensor total in modules over the outside algebra. -/
def total : CochainComplex (ModuleCat.{u} S) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
    (fun n => ModuleCat.ofHom (differential k S A Q Z p n))
    (fun n => ModuleCat.hom_ext (differential_square k S A Q Z p hp n))
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
