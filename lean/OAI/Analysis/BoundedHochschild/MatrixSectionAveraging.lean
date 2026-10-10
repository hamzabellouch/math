import OAI.Analysis.BoundedHochschild.FiniteGroupMultimodularity
import OAI.Analysis.BoundedHochschild.CountableMatrixGroups
import OAI.Analysis.BoundedHochschild.FiniteGroupCochainChainMap

namespace OAI

/-! A fixed finite unitary group for each matrix section. The choices are
independent of the cochain and its degree, so their averages form maps of
the Hochschild complex. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M : Type u} [CStarAlgebra M]

structure MatrixSectionGroup (c : ℕ → PartialIso M) (k : ℕ) where
  carrier : Type u
  [group : Group carrier]
  [finite : Fintype carrier]
  representation : carrier →* unitary M
  mem : ∀ g, (representation g : M) ∈ countableMatrixAlgebra c
  spans : ∀ i j : Fin k, countableMatrixUnit c i.val j.val ∈
    Submodule.span ℂ (Set.range (fun g => (representation g : M)))

attribute [instance] MatrixSectionGroup.group MatrixSectionGroup.finite

lemma matrixSectionGroup_nonempty (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (k : ℕ) :
    Nonempty (MatrixSectionGroup c k) := by
  let d : Fin k → PartialIso M := fun i => c i.val
  have hd : ∀ i, (d i).initial = 1 := fun i => hi i.val
  have hdo : ∀ i j, i ≠ j → (d i).final * (d j).final = 0 := by
    intro i j hij
    exact ho i.val j.val (fun h => hij (Fin.ext h))
  let hp := finiteColumnProjection_isProjection d hdo
  let E := finiteColumnMatrixSystem d hd hdo
  let : Fintype E.signedPermutationGroup := Fintype.ofFinite _
  refine ⟨{ carrier := E.signedPermutationGroup
            representation := finiteCornerGroupHom hp E
            mem := ?_
            spans := ?_ }⟩
  · apply finiteCornerGroupHom_mem
    intro i j
    change (c i.val : M) * star (c j.val : M) ∈ countableMatrixAlgebra c
    exact StarAlgebra.subset_adjoin ℂ _ ⟨(i.val, j.val), rfl⟩
  · intro i j
    exact corner_matrixUnit_mem_group_span hp E i j

def matrixSectionGroup (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (k : ℕ) : MatrixSectionGroup c k :=
  Classical.choice (matrixSectionGroup_nonempty c hi ho k)

def matrixSectionAverage (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M n) (k : ℕ) : Cochain M n :=
  finiteGroupCochainAverage (matrixSectionGroup c hi ho k).representation f

lemma matrixSectionAverage_norm (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M n) (k : ℕ) : ‖matrixSectionAverage c hi ho f k‖ ≤ ‖f‖ :=
  finiteGroupCochainAverage_norm _ f

lemma matrixSectionAverage_module (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M (n + 1)) (k : ℕ) (i j : Fin k) :
    MultimodularAt (matrixSectionAverage c hi ho f k) (countableMatrixUnit c i.val j.val) :=
  finiteGroupCochainAverage_span _ f ((matrixSectionGroup c hi ho k).spans i j)

lemma matrixSectionAverage_add (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f g : Cochain M n) (k : ℕ) :
    matrixSectionAverage c hi ho (f + g) k = matrixSectionAverage c hi ho f k + matrixSectionAverage c hi ho g k :=
  finiteGroupCochainAverage_add _ f g

lemma matrixSectionAverage_smul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (z : ℂ) (f : Cochain M n) (k : ℕ) :
    matrixSectionAverage c hi ho (z • f) k = z • matrixSectionAverage c hi ho f k :=
  finiteGroupCochainAverage_smul _ z f

lemma matrixSectionAverage_differential (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M (n + 1)) (k : ℕ) :
    matrixSectionAverage c hi ho (differential f) k = differential (matrixSectionAverage c hi ho f k) :=
  finiteGroupCochainAverage_differential _ f

lemma matrixSectionAverage_cocycle (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) (k : ℕ) :
    ∀ x, differentialValue (matrixSectionAverage c hi ho f k) x = 0 :=
  finiteGroupCochainAverage_cocycle _ f hf

end BoundedHochschild.KadisonRingrose

end

end OAI
