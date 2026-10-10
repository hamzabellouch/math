import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorMixedSign
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFiniteTotal

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ)

abbrev columns := fun i : Fin l => column k A Q Z (p i)

/-- The actual horizontal matrix entry, zero unless the right degrees are consecutive. -/
def entry (n : ℤ) (i j : Fin l) :
    term k A Q Z (p i) (n + -(p i)) →ₗ[k] term k A Q Z (p j) ((n+1) + -(p j)) :=
  if h : p i + 1 = p j then horizontal k A Q Z n (p i) (p j) h else 0

theorem entry_square (n : ℤ) (i j t : Fin l) :
    (entry k A Q Z p (n+1) j t).comp (entry k A Q Z p n i j) = 0 := by
  unfold entry
  split_ifs with h₁ h₂ h₂
  · exact horizontal_square k A Q Z n (p i) (p j) (p t) h₂ h₁
  · simp only [LinearMap.comp_zero]
  · simp only [LinearMap.zero_comp]
  · simp only [LinearMap.zero_comp]

theorem entry_mixed (n : ℤ) (i j : Fin l) :
    (vertical k A Q Z (n+1) (p j)).comp (entry k A Q Z p n i j) +
      (entry k A Q Z p (n+1) i j).comp (vertical k A Q Z n (p i)) = 0 := by
  unfold entry
  split_ifs with h
  · exact horizontal_mixed k A Q Z n (p i) (p j) h
  · simp only [LinearMap.comp_zero,LinearMap.zero_comp,add_zero]

/-- The actual finite horizontal tensor differential, on the sum of all selected columns. -/
def matrix (n : ℤ) : FiniteColumnComplex.term (columns k A Q Z p) n →ₗ[k]
    FiniteColumnComplex.term (columns k A Q Z p) (n+1) :=
  LinearMap.pi (fun j => ∑ i : Fin l, (entry k A Q Z p n i j).comp (LinearMap.proj i))

@[simp] theorem matrix_apply (n : ℤ)
    (z : FiniteColumnComplex.term (columns k A Q Z p) n) (j : Fin l) :
    matrix k A Q Z p n z j = ∑ i : Fin l, entry k A Q Z p n i j (z i) := by
  change ((∑ i : Fin l, (entry k A Q Z p n i j).comp
    (LinearMap.proj i) : (∀ t : Fin l, term k A Q Z (p t) (n + -(p t))) →ₗ[k]
      term k A Q Z (p j) ((n+1) + -(p j))) z) = _
  exact LinearMap.sum_apply _ _ _

theorem matrix_square (n : ℤ) :
    (matrix k A Q Z p (n+1)).comp (matrix k A Q Z p n) = 0 := by
  apply LinearMap.ext
  intro z
  funext j
  change matrix k A Q Z p (n+1) (matrix k A Q Z p n z) j = 0
  simp only [matrix_apply,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro t _
  exact congrArg (fun f => f (z t)) (entry_square k A Q Z p n t i j)

theorem matrix_mixed (n : ℤ) :
    (FiniteColumnComplex.diagonal (columns k A Q Z p) (n+1)).comp (matrix k A Q Z p n) +
    (matrix k A Q Z p (n+1)).comp (FiniteColumnComplex.diagonal (columns k A Q Z p) n) = 0 := by
  apply LinearMap.ext
  intro z
  funext j
  change ((column k A Q Z (p j)).d (n+1) ((n+1)+1)).hom (matrix k A Q Z p n z j) +
    matrix k A Q Z p (n+1) (FiniteColumnComplex.diagonal (columns k A Q Z p) n z) j = 0
  simp only [matrix_apply,FiniteColumnComplex.diagonal_apply]
  erw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have h := congrArg (fun f => f (z i)) (entry_mixed k A Q Z p n i j)
  simp only [vertical] at h
  simp only [column_d]
  exact h

theorem matrix_upper (hp : StrictMono p) (n : ℤ) (j : Fin l)
    (z : FiniteColumnComplex.term (columns k A Q Z p) n)
    (hz : ∀ i : Fin l, i.val < j.val → z i = 0) : matrix k A Q Z p n z j = 0 := by
  rw [matrix_apply]
  apply Finset.sum_eq_zero
  intro i _
  unfold entry
  split_ifs with h
  · have hij : i < j := hp.lt_iff_lt.mp (by omega)
    erw [hz i hij,map_zero]
    rfl
  · rfl

/-- Actual tensor horizontal maps satisfy every requirement of the finite total construction. -/
def tensorHorizontal (hp : StrictMono p) : FiniteColumnComplex.Horizontal (columns k A Q Z p) where
  d := matrix k A Q Z p
  square := matrix_square k A Q Z p
  mixed := matrix_mixed k A Q Z p
  strictUpper := matrix_upper k A Q Z p hp

/-- The signed total tensor complex on a finite interval of the right complex. -/
def finiteTotal (hp : StrictMono p) : CochainComplex (ModuleCat.{u} k) ℤ :=
  FiniteColumnComplex.total (columns k A Q Z p) (tensorHorizontal k A Q Z p hp)
end LittleFinitistic.ComplexTensor

end

end OAI
