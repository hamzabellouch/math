import OAI.Analysis.GroupDeterminants.ProjectionLog

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section GroupAlgebraClosure
variable {G : Type} [Group G] {n : ℕ}

theorem complexOperator_single (i j : Fin n) (g : G) (z : ℂ) :
    complexOperator (Matrix.single i j (MonoidAlgebra.single g z)) =
      z • elementaryOperator i j g := by
  classical
  unfold complexOperator
  simp only [Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index
          (h := fun groupElement coefficient => coefficient • elementaryOperator i j groupElement)
          (zero_smul ℂ (elementaryOperator i j g))]
    · intro b _ hbj
      simp [Ne.symm hbj]
    · simp
  · intro a _ hai
    simp [Ne.symm hai]
  · simp

def finiteGroupAlgebra : Subalgebra ℂ (Hilbert G n →L[ℂ] Hilbert G n) :=
  complexAlgebraRepresentation.range

theorem elementaryOperator_mem (i j : Fin n) (g : G) :
    elementaryOperator i j g ∈ finiteGroupAlgebra := by
  refine ⟨Matrix.single i j (MonoidAlgebra.single g 1), ?_⟩
  exact (complexOperator_single i j g 1).trans (one_smul _ _)

theorem finiteGroupAlgebra_star {T : Hilbert G n →L[ℂ] Hilbert G n}
    (hT : T ∈ finiteGroupAlgebra) : star T ∈ finiteGroupAlgebra := by
  classical
  obtain ⟨A, rfl⟩ := hT
  change star (complexOperator A) ∈ finiteGroupAlgebra
  rw [complexOperator, star_sum (R := Hilbert G n →L[ℂ] Hilbert G n)]
  apply Subalgebra.sum_mem
  intro i _
  rw [star_sum (R := Hilbert G n →L[ℂ] Hilbert G n)]
  apply Subalgebra.sum_mem
  intro j _
  rw [Finsupp.sum, star_sum (R := Hilbert G n →L[ℂ] Hilbert G n)]
  apply Subalgebra.sum_mem
  intro g _
  rw [star_smul, elementaryOperator_star]
  exact Subalgebra.smul_mem _ (elementaryOperator_mem j i g⁻¹) _

def finiteGroupStarAlgebra : StarSubalgebra ℂ (Hilbert G n →L[ℂ] Hilbert G n) :=
  { finiteGroupAlgebra with star_mem' := finiteGroupAlgebra_star }

def closedGroupAlgebra : StarSubalgebra ℂ (Hilbert G n →L[ℂ] Hilbert G n) :=
  finiteGroupStarAlgebra.topologicalClosure

theorem continuous_groupTrace : Continuous (groupTrace (G := G) (n := n)) := by
  have he : (fun T => groupTraceCLM (G := G) (n := n) T) = groupTrace :=
    funext groupTraceCLM_apply
  rw [← he]
  exact groupTraceCLM.continuous

theorem groupTrace_closed_mul_comm {S T : Hilbert G n →L[ℂ] Hilbert G n}
    (hS : S ∈ closedGroupAlgebra) (hT : T ∈ closedGroupAlgebra) :
    groupTrace (S * T) = groupTrace (T * S) := by
  have hfinite {X Y : Hilbert G n →L[ℂ] Hilbert G n}
      (hX : X ∈ finiteGroupStarAlgebra) (hY : Y ∈ finiteGroupStarAlgebra) :
      groupTrace (X * Y) = groupTrace (Y * X) := by
    obtain ⟨A, rfl⟩ := hX
    obtain ⟨B, rfl⟩ := hY
    exact groupTrace_complex_mul_comm A B
  have hleft {X Y : Hilbert G n →L[ℂ] Hilbert G n}
      (hX : X ∈ finiteGroupStarAlgebra) (hY : Y ∈ closedGroupAlgebra) :
      groupTrace (X * Y) = groupTrace (Y * X) := by
    apply closure_minimal (fun Z hZ => hfinite hX hZ)
      (isClosed_eq (continuous_groupTrace.comp (continuous_const.mul continuous_id))
        (continuous_groupTrace.comp (continuous_id.mul continuous_const))) hY
  exact closure_minimal (fun X hX => hleft hX hT)
    (isClosed_eq (continuous_groupTrace.comp (continuous_id.mul continuous_const))
      (continuous_groupTrace.comp (continuous_const.mul continuous_id))) hS

theorem groupTrace_one : groupTrace (1 : Hilbert G n →L[ℂ] Hilbert G n) = n := by
  rw [← complexOperator_one, groupTrace_complex]
  simp

end GroupAlgebraClosure

end GroupRingDeterminant

end

end OAI
