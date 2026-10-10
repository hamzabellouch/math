import OAI.Analysis.FactorGeneration.MatrixUnits
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! # A Hilbert basis adapted to a full matrix system

A basis of one diagonal corner is transported by the matrix columns. This
gives an explicit tensor-shaped basis on which every matrix unit has its
standard action, the bridge needed for compatible finite matrix groups.
-/

open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace Generator.MatrixUnitSystem

variable (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (o : ι)

def initialHilbertSpace : Submodule ℂ H := (E.entry o o).range

instance initialHilbertSpace_complete : CompleteSpace (E.initialHilbertSpace o) := by
  have hp : IsIdempotentElem (E.entry o o) := by
    change E.entry o o * E.entry o o = E.entry o o
    simp only [E.mul_entry, ite_true]
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp).completeSpace_coe

theorem initialHilbertSpace_fixed (x : E.initialHilbertSpace o) : E.entry o o x = x := by
  obtain ⟨y, hy⟩ := x.property
  change E.entry o o y = (x : H) at hy
  rw [← hy]
  change (E.entry o o * E.entry o o) y = E.entry o o y
  simp only [E.mul_entry, ite_true]

def initialCoordinate (i : ι) (x : H) : E.initialHilbertSpace o :=
  ⟨E.entry o i x, ⟨E.entry o i x, by
    change (E.entry o o * E.entry o i) x = E.entry o i x
    simp only [E.mul_entry, ite_true]⟩⟩

def initialColumn (i : ι) : E.initialHilbertSpace o →ₗ[ℂ] H :=
  (E.entry i o).toLinearMap.comp (E.initialHilbertSpace o).subtype

@[simp]
theorem initialColumn_apply (i : ι) (x : E.initialHilbertSpace o) :
    E.initialColumn o i x = E.entry i o x := rfl

theorem inner_initialColumns (i j : ι) (x y : E.initialHilbertSpace o) :
    inner ℂ (E.initialColumn o i x) (E.initialColumn o j y) =
      if i = j then inner ℂ x y else 0 := by
  change inner ℂ (E.entry i o x) (E.entry j o y) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (x : H) ((star (E.entry i o) * E.entry j o) (y : H)) = _
  rw [E.star_entry, E.mul_entry]
  split_ifs
  · rw [E.initialHilbertSpace_fixed o y]
    rfl
  · simp

theorem sum_initialColumn_coordinate (x : H) :
    ∑ i, E.initialColumn o i (E.initialCoordinate o i x) = x := by
  have he (i : ι) : E.initialColumn o i (E.initialCoordinate o i x) = E.entry i i x := by
    change (E.entry i o * E.entry o i) x = E.entry i i x
    simp only [E.mul_entry, ite_true]
  simp_rw [he]
  rw [← sum_apply, E.total]
  rfl

variable (b : OrthonormalBasis κ ℂ (E.initialHilbertSpace o))

def adaptedVector (p : ι × κ) : H := E.initialColumn o p.1 (b p.2)

theorem adaptedVector_orthonormal : Orthonormal ℂ (E.adaptedVector o b) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, k⟩ ⟨j, l⟩
  change inner ℂ (E.initialColumn o i (b k)) (E.initialColumn o j (b l)) = _
  rw [E.inner_initialColumns, b.inner_eq_ite]
  by_cases hi : i = j <;> by_cases hk : k = l <;> simp [hi, hk]

omit [DecidableEq κ] in
theorem adaptedVector_span : ⊤ ≤ Submodule.span ℂ (Set.range (E.adaptedVector o b)) := by
  let S := Submodule.span ℂ (Set.range (E.adaptedVector o b))
  have hc (i : ι) (y : E.initialHilbertSpace o) : E.initialColumn o i y ∈ S := by
    rw [← b.sum_repr y, map_sum]
    apply S.sum_mem
    intro k _
    rw [map_smul]
    exact S.smul_mem _ (Submodule.subset_span ⟨(i, k), rfl⟩)
  intro x _
  rw [← E.sum_initialColumn_coordinate o x]
  exact S.sum_mem (fun i _ => hc i _)

/-- The explicit basis obtained by transporting the initial-corner basis. -/
def adaptedBasis : OrthonormalBasis (ι × κ) ℂ H :=
  OrthonormalBasis.mk (E.adaptedVector_orthonormal o b) (E.adaptedVector_span o b)

@[simp]
theorem adaptedBasis_apply (p : ι × κ) : E.adaptedBasis o b p = E.entry p.1 o (b p.2) := by
  change OrthonormalBasis.mk _ _ p = _
  rw [OrthonormalBasis.coe_mk]
  rfl

/-- On the adapted basis the original matrix units act on the first index. -/
theorem entry_adaptedBasis (i j k : ι) (r : κ) :
    E.entry i j (E.adaptedBasis o b (k, r)) =
      if j = k then E.adaptedBasis o b (i, r) else 0 := by
  simp only [E.adaptedBasis_apply]
  change (E.entry i j * E.entry k o) (b r) = _
  rw [E.mul_entry]
  split_ifs <;> rfl

end Generator.MatrixUnitSystem

end

end OAI
