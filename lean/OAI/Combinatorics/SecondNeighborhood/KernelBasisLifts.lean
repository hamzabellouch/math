import OAI.Combinatorics.SecondNeighborhood.GenericRankColumns

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped BigOperators Matrix

variable {I J F κ E : Type*}
variable [Fintype J] [Fintype κ] [DecidableEq J] [Field F]

def extendSelected (col : κ → J) (y : κ → F) : J → F :=
  ∑ k, Pi.single (col k) (y k)

omit [Fintype J] in
theorem extendSelected_apply_of_ne (col : κ → J) (y : κ → F) (j : J)
    (hj : ∀ k, j ≠ col k) : extendSelected col y j = 0 := by
  simp only [extendSelected, Finset.sum_apply]
  exact Finset.sum_eq_zero fun k _ =>
    Pi.single_eq_of_ne (M := fun _ : J => F) (hj k) (y k)

omit [Fintype J] in
theorem extendSelected_apply_selected (col : κ → J) (hcol : Function.Injective col)
    (y : κ → F) (k : κ) : extendSelected col y (col k) = y k := by
  classical
  simp only [extendSelected, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    exact Pi.single_eq_of_ne (M := fun _ : J => F) (fun h => hk' (hcol h).symm) (y k')
  · simp

theorem mulVec_extendSelected (M : Matrix I J F) (col : κ → J) (y : κ → F) :
    M *ᵥ extendSelected col y = (M.submatrix id col) *ᵥ y := by
  funext i
  change (M i) ⬝ᵥ (∑ k, Pi.single (col k) (y k)) =
    ∑ k, M i (col k) * y k
  simp only [dotProduct_sum, dotProduct_single]

noncomputable def liftCoefficients (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) : κ → F :=
  Classical.choose (cover (Pi.single j 1))

theorem liftCoefficients_spec (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) :
    M *ᵥ Pi.single j 1 = (M.submatrix id col) *ᵥ liftCoefficients M col cover j :=
  Classical.choose_spec (cover (Pi.single j 1))

noncomputable def kernelLift (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) : J → F :=
  Pi.single j 1 - extendSelected col (liftCoefficients M col cover j)

theorem kernelLift_eq (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) :
    kernelLift M col cover j =
      Pi.single j 1 - ∑ k, Pi.single (col k) (liftCoefficients M col cover j k) :=
  rfl

theorem mulVec_kernelLift (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j : J) :
    M *ᵥ kernelLift M col cover j = 0 := by
  rw [kernelLift, Matrix.mulVec_sub, mulVec_extendSelected,
    liftCoefficients_spec M col cover j, sub_self]

theorem kernelLift_apply_of_ne (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y) (j j' : J)
    (hj' : ∀ k, j' ≠ col k) :
    kernelLift M col cover j j' = (Pi.single j 1 : J → F) j' := by
  change (Pi.single j 1 : J → F) j' -
    extendSelected col (liftCoefficients M col cover j) j' = _
  rw [extendSelected_apply_of_ne col _ j' hj', sub_zero]

theorem kernelLift_normalized [DecidableEq E]
    (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y)
    (left : E → J) (hleft : Function.Injective left)
    (hdisjoint : ∀ e k, left e ≠ col k) (e f : E) :
    kernelLift M col cover (left e) (left f) = if e = f then 1 else 0 := by
  rw [kernelLift_apply_of_ne M col cover (left e) (left f) (hdisjoint f)]
  by_cases h : e = f
  · subst f
    simp
  · have hcoord : left f ≠ left e := fun hcoord => h (hleft hcoord).symm
    rw [Pi.single_eq_of_ne hcoord, ite_eq_right h]

theorem exists_normalized_kernelLifts [DecidableEq E]
    (M : Matrix I J F) (col : κ → J)
    (cover : ∀ x : J → F, ∃ y : κ → F,
      M *ᵥ x = (M.submatrix id col) *ᵥ y)
    (left : E → J) (hleft : Function.Injective left)
    (hdisjoint : ∀ e k, left e ≠ col k) :
    ∃ U : E → J → F, (∀ e, M *ᵥ U e = 0) ∧
      (∀ e f, U e (left f) = if e = f then 1 else 0) := by
  refine ⟨fun e => kernelLift M col cover (left e), ?_, ?_⟩
  · intro e
    exact mulVec_kernelLift M col cover (left e)
  · intro e f
    exact kernelLift_normalized M col cover left hleft hdisjoint e f

theorem exists_normalized_kernelLifts_of_det_ne_zero
    [Fintype I] [DecidableEq κ] [DecidableEq E]
    (M : Matrix I J F) (row : κ → I) (col : κ → J)
    (hdet : (M.submatrix row col).det ≠ 0) (hrank : M.rank ≤ Fintype.card κ)
    (left : E → J) (hleft : Function.Injective left)
    (hdisjoint : ∀ e k, left e ≠ col k) :
    ∃ U : E → J → F, (∀ e, M *ᵥ U e = 0) ∧
      (∀ e f, U e (left f) = if e = f then 1 else 0) := by
  exact exists_normalized_kernelLifts M col
    (fun x => exists_selectedColumns_mulVec M row col hdet hrank x)
    left hleft hdisjoint

end SeymourSecondNeighborhood.Pruning

end OAI
