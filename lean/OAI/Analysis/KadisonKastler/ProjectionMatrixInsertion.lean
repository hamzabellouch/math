import OAI.Analysis.KadisonKastler.TypeIIISpectralMatrix
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! # Inserting a projection into a finite matrix stage of a type III factor

For a nontrivial projection, its two nonzero sides are equivalent and
give a two-by-two system of matrix units. The scalar projections already
belong to the initial scalar stage. No state approximation is asserted.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_matrixStage_containing_projection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) :
    ∃ E : FiniteMatrixStage M, p.val.val ∈ E.units.concreteAlgebra := by
  classical
  by_cases hp0 : p.val = 0
  · refine ⟨FiniteMatrixStage.scalarStage M,?_⟩
    rw [hp0]
    exact (FiniteMatrixStage.scalarStage M).units.concreteAlgebra.zero_mem
  by_cases hp1 : p.val = 1
  · refine ⟨FiniteMatrixStage.scalarStage M,?_⟩
    rw [hp1]
    exact (FiniteMatrixStage.scalarStage M).units.concreteAlgebra.one_mem
  let P : Fin 2 → AlgebraProjection M := fun i =>
    if i = 0 then p else ⟨1-p.val,p.property.one_sub⟩
  have hn (i : Fin 2) : (P i).val ≠ 0 := by
    fin_cases i
    · simpa [P] using hp0
    · change 1-p.val ≠ 0
      intro hz
      exact hp1 (sub_eq_zero.mp hz).symm
  have ho (i j : Fin 2) (hij : i ≠ j) : (P i).val * (P j).val = 0 := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change p.val * (1-p.val) = 0
      rw [mul_sub,mul_one,p.property.isIdempotentElem.eq,sub_self]
    · change (1-p.val) * p.val = 0
      rw [sub_mul,one_mul,p.property.isIdempotentElem.eq,sub_self]
    · exact (hij rfl).elim
  have ht : (∑ i, (P i).val) = 1 := by
    rw [Fin.sum_univ_two]
    change p.val+(1-p.val) = 1
    abel
  obtain ⟨E,hE⟩ := hM.exists_matrixUnits_of_partition P hn ho ht
  let F : FiniteMatrixStage M := ⟨2,by decide,E⟩
  refine ⟨F,?_⟩
  have he : E.entry 0 0 = p.val := hE 0
  have hm : p.val ∈ E.algebra := by rw [← he]; exact E.entry_mem 0 0
  exact (E.mem_concreteAlgebra p.val).mpr hm

end

end KadisonKastler

end OAI
