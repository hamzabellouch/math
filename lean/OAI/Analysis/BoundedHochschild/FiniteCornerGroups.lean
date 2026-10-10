import OAI.Analysis.BoundedHochschild.FiniteColumnCorners
import OAI.Analysis.BoundedHochschild.CornerUnitaryExtension

namespace OAI

/-! Finite signed-permutation groups in proper corners, extended by the
identity on the complement. Their spans contain every corner matrix unit. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {p : M} (hp : IsStarProjection p) {n : ℕ} (E : MatrixSystem (Corner p hp) n)

def finiteCornerGroupHom : E.signedPermutationGroup →* unitary M :=
  (cornerUnitaryExtension hp).comp E.signedPermutationGroup.subtype

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_matrixUnit_mem_group_span (i j : Fin n) :
    (E.entry i j : M) ∈ Submodule.span ℂ
      (Set.range (fun g : E.signedPermutationGroup => (finiteCornerGroupHom hp E g : M))) := by
  classical
  let P := Submodule.span ℂ
    (Set.range (fun g : E.signedPermutationGroup => (finiteCornerGroupHom hp E g : M)))
  let σ := Equiv.swap j i
  let g₀ : E.signedPermutationGroup :=
    ⟨E.signedPermutationUnitary σ (fun _ => false), ⟨(σ, fun _ => false), rfl⟩⟩
  let g₁ : E.signedPermutationGroup :=
    ⟨E.signedPermutationUnitary σ (fun k => decide (k = j)),
      ⟨(σ, fun k => decide (k = j)), rfl⟩⟩
  have hm (g : E.signedPermutationGroup) : (finiteCornerGroupHom hp E g : M) ∈ P :=
    Submodule.subset_span ⟨g, rfl⟩
  have hdiff : (finiteCornerGroupHom hp E g₀ : M) - (finiteCornerGroupHom hp E g₁ : M) =
      (2 : ℂ) • (E.entry i j : M) := by
    change ((E.signedPermutation σ (fun _ => false) : M) + (1 - p)) -
      ((E.signedPermutation σ (fun k => decide (k = j)) : M) + (1 - p)) = _
    calc
      _ = ((E.signedPermutation σ (fun _ => false) -
          E.signedPermutation σ (fun k => decide (k = j)) : Corner p hp) : M) := by
        change (_ + (1 - p)) - (_ + (1 - p)) = _ - _
        abel
      _ = _ := by rw [E.signedPermutation_flip]; simp [σ]
  have hh := P.smul_mem (2⁻¹ : ℂ) (P.sub_mem (hm g₀) (hm g₁))
  rw [hdiff, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul] at hh
  exact hh

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCornerGroupHom_mem (R : StarSubalgebra ℂ M)
    (hE : ∀ i j, (E.entry i j : M) ∈ R) (g : E.signedPermutationGroup) :
    (finiteCornerGroupHom hp E g : M) ∈ R := by
  classical
  have hpR : p ∈ R := by
    have he := congrArg (fun a : Corner p hp => (a : M)) E.sum_diagonal
    have hm := R.sum_mem (fun i (_ : i ∈ Finset.univ) => hE i i)
    rw [AddSubmonoidClass.coe_finsetSum, corner_coe_one] at he
    rwa [← he]
  rcases g with ⟨u, ⟨⟨σ, s⟩, rfl⟩⟩
  change (E.signedPermutation σ s : M) + (1 - p) ∈ R
  apply R.add_mem _ (R.sub_mem R.one_mem hpR)
  change ((∑ i, MatrixSystem.signScalar (s i) • E.entry (σ i) i : Corner p hp) : M) ∈ R
  simpa using R.sum_mem (fun i (_ : i ∈ Finset.univ) => R.smul_mem (hE (σ i) i) _)

end BoundedHochschild.KadisonRingrose

end

end OAI
