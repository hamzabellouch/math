import OAI.Analysis.KadisonKastler.InfiniteCornerInflation
import OAI.Analysis.FactorGeneration.PartialIsometries

namespace OAI

/-! # Countable equivalent projection families give full matrix corners

The input here is actual projection and partial-isometry data in a represented
von Neumann algebra.  No existence of a semifinite decomposition is assumed as
a published input.  Once such a decomposition has been constructed, the
matrix-corner machinery applies to the explicit operators `v i * star (v j)`.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The matrix entries associated to partial isometries with a common initial
projection. -/
def projectionFamilyEntry (v : ℕ → Algebra M) (i j : ℕ) : Algebra M :=
  v i * star (v j)

@[simp] theorem projectionFamilyEntry_star (v : ℕ → Algebra M) (i j : ℕ) :
    star (projectionFamilyEntry v i j) = projectionFamilyEntry v j i := by
  simp only [projectionFamilyEntry, star_mul, star_star]

theorem projectionFamilyEntry_diagonal
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvf : ∀ i, v i * star (v i) = (p i).val) (i : ℕ) :
    projectionFamilyEntry v i i = (p i).val := hvf i

/-- Orthogonality of the final projections forces the cross-products of the
partial isometries to vanish. -/
theorem projectionFamily_cross_eq_zero
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    {i j : ℕ} (hij : i ≠ j) : star (v i) * v j = 0 := by
  let V (k : ℕ) : PartialIsometry M := ⟨p 0, v k, hvi k⟩
  have ht (k : ℕ) : (V k).target = p k := Subtype.ext (hvf k)
  exact (V i).adjoint.mul_eq_zero (V j) (by
    change (V i).target.val * (V j).target.val = 0
    rw [ht, ht]
    exact horth hij)

theorem projectionFamilyEntry_mul
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (i j k l : ℕ) :
    projectionFamilyEntry v i j * projectionFamilyEntry v k l =
      if j = k then projectionFamilyEntry v i l else 0 := by
  classical
  let V (a : ℕ) : PartialIsometry M := ⟨p 0, v a, hvi a⟩
  by_cases hjk : j = k
  · subst k
    rw [ite_eq_left rfl]
    change (v i * star (v j)) * (v j * star (v l)) = v i * star (v l)
    calc
      _ = (v i * (star (v j) * v j)) * star (v l) := by
        simp only [mul_assoc]
      _ = v i * star (v l) := by
        rw [hvi, show v i * (p 0).val = v i from (V i).mul_support]
  · rw [ite_eq_right hjk]
    change (v i * star (v j)) * (v k * star (v l)) = 0
    calc
      _ = (v i * (star (v j) * v k)) * star (v l) := by
        simp only [mul_assoc]
      _ = 0 := by
        rw [projectionFamily_cross_eq_zero p v hvi hvf horth hjk, mul_zero, zero_mul]

namespace FullMatrixCorner

/-- A countable strong partition into equivalent projections supplies actual
full matrix units with the prescribed initial Hilbert corner. -/
def ofEquivalentProjectionFamily
    (E : Submodule ℂ H) [CompleteSpace E]
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (hp0 : ((p 0).val : H →L[ℂ] H) = E.starProjection)
    (htotal : ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x) x) :
    FullMatrixCorner E where
  entry i j := projectionFamilyEntry v i j
  star_entry i j := congrArg Subtype.val (projectionFamilyEntry_star v i j)
  mul_entry i j k l := by
    classical
    have h := congrArg Subtype.val (projectionFamilyEntry_mul p v hvi hvf horth i j k l)
    by_cases hjk : j = k
    · simpa only [ite_eq_left hjk, MulMemClass.coe_mul] using h
    · simpa only [ite_eq_right hjk, MulMemClass.coe_mul, ZeroMemClass.coe_zero] using h
  zero_zero := (congrArg Subtype.val (hvf 0)).trans hp0
  total x := by
    simpa only [projectionFamilyEntry, hvf] using htotal x

@[simp] theorem ofEquivalentProjectionFamily_entry
    (E : Submodule ℂ H) [CompleteSpace E]
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (hp0 : ((p 0).val : H →L[ℂ] H) = E.starProjection)
    (htotal : ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x) x)
    (i j : ℕ) :
    (ofEquivalentProjectionFamily E p v hvi hvf horth hp0 htotal).entry i j =
      ((v i * star (v j) : Algebra M) : H →L[ℂ] H) := rfl

theorem ofEquivalentProjectionFamily_entry_mem
    (E : Submodule ℂ H) [CompleteSpace E]
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (hp0 : ((p 0).val : H →L[ℂ] H) = E.starProjection)
    (htotal : ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x) x)
    (i j : ℕ) :
    (ofEquivalentProjectionFamily E p v hvi hvf horth hp0 htotal).entry i j ∈ M :=
  (projectionFamilyEntry v i j).property

end FullMatrixCorner

end

end KadisonKastler

end OAI
