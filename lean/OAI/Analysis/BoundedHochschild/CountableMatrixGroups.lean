import OAI.Analysis.BoundedHochschild.FiniteCornerGroups
import OAI.Analysis.BoundedHochschild.CountableMatrixSubalgebra

namespace OAI

/-! Finite unitary groups inside the constructed matrix subalgebra whose
linear spans contain any prescribed finite section of its matrix units. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
theorem finite_group_spans_matrix_section (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (n : ℕ) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (ρ : G →* unitary M),
      (∀ g, (ρ g : M) ∈ countableMatrixClosure e c) ∧
      ∀ i j : Fin n, (c i.val : M) * star (c j.val : M) ∈
        Submodule.span ℂ (Set.range (fun g => (ρ g : M))) := by
  let d : Fin n → PartialIso M := fun i => c i.val
  have hd : ∀ i, (d i).initial = 1 := fun i => hi i.val
  have hdo : ∀ i j, i ≠ j → (d i).final * (d j).final = 0 := by
    intro i j hij
    exact ho i.val j.val (fun h => hij (Fin.ext h))
  let hp := finiteColumnProjection_isProjection d hdo
  let E := finiteColumnMatrixSystem d hd hdo
  refine ⟨E.signedPermutationGroup, inferInstance, inferInstance, finiteCornerGroupHom hp E, ?_, ?_⟩
  · apply finiteCornerGroupHom_mem
    intro i j
    change (c i.val : M) * star (c j.val : M) ∈ countableMatrixClosure e c
    exact countableMatrixClosure_transition e c i.val j.val
  · intro i j
    exact corner_matrixUnit_mem_group_span hp E i j

omit [PartialOrder M] [StarOrderedRing M] in
theorem finite_group_spans_matrix_subset (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (s : Finset ℕ) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (ρ : G →* unitary M),
      (∀ g, (ρ g : M) ∈ countableMatrixClosure e c) ∧
      ∀ i ∈ s, ∀ j ∈ s, (c i : M) * star (c j : M) ∈
        Submodule.span ℂ (Set.range (fun g => (ρ g : M))) := by
  obtain ⟨G, hG, hGF, ρ, hρ, hspan⟩ := finite_group_spans_matrix_section e c hi ho (s.sup id + 1)
  let := hG
  let := hGF
  refine ⟨G, hG, hGF, ρ, hρ, ?_⟩
  intro i hiS j hjS
  have hiN : i < s.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hiS)
  have hjN : j < s.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hjS)
  exact hspan ⟨i, hiN⟩ ⟨j, hjN⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
