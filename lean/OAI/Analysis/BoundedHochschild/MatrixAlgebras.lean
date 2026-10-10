import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Finite matrix subalgebras and their commutants. -/

noncomputable section

open Filter Topology
namespace HochschildMatrixSystems.MatrixSystem
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (E : MatrixSystem M n)

def entrySpan : Submodule ℂ M := Submodule.span ℂ (Set.range (fun p : Fin n × Fin n => E.entry p.1 p.2))

lemma entry_mem_span {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    {n : ℕ} (E : MatrixSystem M n) (i j : Fin n) : E.entry i j ∈ E.entrySpan :=
  Submodule.subset_span ⟨(i,j),rfl⟩

lemma one_mem_entrySpan : (1:M) ∈ E.entrySpan := by
  rw [← E.sum_diagonal]
  exact (E.entrySpan).sum_mem (fun i _ => E.entry_mem_span i i)

lemma mul_mem_entrySpan {x y : M} (hx : x ∈ E.entrySpan) (hy : y ∈ E.entrySpan) :
    x*y ∈ E.entrySpan := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨⟨i,j⟩,rfl⟩ := ha
      induction hy using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨⟨k,l⟩,rfl⟩ := hb
          rw [E.entry_mul]
          split
          · exact E.entry_mem_span _ _
          · exact (E.entrySpan).zero_mem
      | zero => simp
      | add a b ha hb iha ihb => simpa [mul_add] using (E.entrySpan).add_mem iha ihb
      | smul c a ha ih => simpa [mul_smul_comm] using (E.entrySpan).smul_mem c ih
  | zero => simp
  | add a b ha hb iha ihb => simpa [add_mul] using (E.entrySpan).add_mem iha ihb
  | smul c a ha ih => simpa [smul_mul_assoc] using (E.entrySpan).smul_mem c ih

lemma star_mem_entrySpan {x : M} (hx : x ∈ E.entrySpan) : star x ∈ E.entrySpan := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨⟨i,j⟩,rfl⟩ := ha
      rw [E.star_entry]
      exact E.entry_mem_span _ _
  | zero => simp
  | add a b ha hb iha ihb => simpa [star_add] using (E.entrySpan).add_mem iha ihb
  | smul c a ha ih => simpa [star_smul] using (E.entrySpan).smul_mem (star c) ih

def matrixAlgebra : StarSubalgebra ℂ M where
  carrier := E.entrySpan
  zero_mem' := (E.entrySpan).zero_mem
  one_mem' := E.one_mem_entrySpan
  add_mem' := (E.entrySpan).add_mem
  mul_mem' := E.mul_mem_entrySpan
  algebraMap_mem' c := by
    change algebraMap ℂ M c ∈ E.entrySpan
    rw [Algebra.algebraMap_eq_smul_one]
    exact (E.entrySpan).smul_mem c E.one_mem_entrySpan
  star_mem' := E.star_mem_entrySpan

instance matrixAlgebra_finiteDimensional : FiniteDimensional ℂ E.matrixAlgebra :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

instance matrixAlgebra_closed : IsClosed (E.matrixAlgebra : Set M) := by
  let : FiniteDimensional ℂ E.entrySpan := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact (E.entrySpan).closed_of_finiteDimensional

lemma commutant_commutes_matrix (x : E.commutant) (y : E.matrixAlgebra) :
    Commute (x:M) (y:M) := by
  suffices h : ∀ a ∈ E.entrySpan, Commute (x:M) a from h y y.property
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨⟨i,j⟩,rfl⟩ := ha
      exact x.property i j
  | zero => exact Commute.zero_right _
  | add a b ha hb iha ihb => exact iha.add_right ihb
  | smul c a ha ih => exact ih.smul_right c

instance matrixUnitary_compactSpace : CompactSpace (unitary E.matrixAlgebra) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0:E.matrixAlgebra) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall,dist_zero_right]
  calc
    ‖u‖ = ‖(1:E.matrixAlgebra)‖ := by
      simpa only [one_mul] using CStarRing.norm_mul_coe_unitary (1:E.matrixAlgebra) ⟨u,hu⟩
    _ ≤ 1 := by
      rcases subsingleton_or_nontrivial E.matrixAlgebra with h | h
      · have : (1:E.matrixAlgebra)=0 := Subsingleton.elim _ _
        simp [this]
      · simp

end HochschildMatrixSystems.MatrixSystem

end

end OAI
