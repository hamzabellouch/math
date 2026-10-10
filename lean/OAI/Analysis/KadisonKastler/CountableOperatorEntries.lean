import OAI.Analysis.KadisonKastler.CountableSpatialTensor

namespace OAI

/-! # Entries of operators on a countable Hilbert sum

Entrywise identities detect equality and diagonal commutation. Under the
countable tensor unitary, tensoring an operator on the sum tensors each
of its entries. No summability of the operator's matrix is assumed.
-/

namespace KadisonKastler

open UnitalTomsWinter Filter
open scoped TensorProduct Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def countableOperatorEntry (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H)
    (i j : ℕ) : H →L[ℂ] H :=
  (canonicalCoordinate H i).comp (S.comp (canonicalSingle H j))

@[simp] theorem countableOperatorEntry_apply
    (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) (x : H) :
    countableOperatorEntry S i j x = S (lp.single 2 j x) i := rfl

theorem countableOperator_ext
    {S T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H}
    (h : ∀ i j, countableOperatorEntry S i j = countableOperatorEntry T i j) : S = T := by
  have hs (j : ℕ) (x : H) : S (lp.single 2 j x) = T (lp.single 2 j x) := by
    ext i
    exact DFunLike.congr_fun (h i j) x
  apply ContinuousLinearMap.ext
  intro x
  have h₁ := S.continuous.continuousAt.tendsto.comp (lp.hasSum_single (by norm_num) x)
  have h₂ := T.continuous.continuousAt.tendsto.comp (lp.hasSum_single (by norm_num) x)
  change Tendsto (fun s : Finset ℕ => S (∑ i ∈ s, lp.single 2 i (x i)))
    atTop (𝓝 (S x)) at h₁
  change Tendsto (fun s : Finset ℕ => T (∑ i ∈ s, lp.single 2 i (x i)))
    atTop (𝓝 (T x)) at h₂
  have he : (fun s : Finset ℕ => S (∑ i ∈ s, lp.single 2 i (x i))) =
      (fun s : Finset ℕ => T (∑ i ∈ s, lp.single 2 i (x i))) := by
    funext s
    simp only [map_sum, hs]
  rw [he] at h₁
  exact tendsto_nhds_unique h₁ h₂

@[simp] theorem countableOperatorEntry_diagonal_mul
    (a : H →L[ℂ] H) (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) :
    countableOperatorEntry (l2Diagonal a * S) i j = a * countableOperatorEntry S i j := by
  ext x
  rfl

@[simp] theorem countableOperatorEntry_mul_diagonal
    (a : H →L[ℂ] H) (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) :
    countableOperatorEntry (S * l2Diagonal a) i j = countableOperatorEntry S i j * a := by
  ext x
  simp only [countableOperatorEntry_apply, mul_apply_eq_comp, l2Diagonal_single]

theorem countableOperator_commutes_diagonal_iff
    (a : H →L[ℂ] H) (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) :
    l2Diagonal a * S = S * l2Diagonal a ↔
      ∀ i j, a * countableOperatorEntry S i j = countableOperatorEntry S i j * a := by
  constructor
  · intro h i j
    simpa only [countableOperatorEntry_diagonal_mul, countableOperatorEntry_mul_diagonal]
      using congrArg (fun T => countableOperatorEntry T i j) h
  · intro h
    apply countableOperator_ext
    intro i j
    simpa only [countableOperatorEntry_diagonal_mul, countableOperatorEntry_mul_diagonal]
      using h i j

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

@[simp] theorem countableTensorVector_single (i : ℕ) (x : H) (y : K) :
    countableTensorVector (lp.single 2 i x) y =
      lp.single 2 i ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) := by
  classical
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [lp.single_apply, h]

@[simp] theorem countableTensorEquiv_symm_single (i : ℕ) (x : H) (y : K) :
    (countableTensorEquiv (H := H) (K := K)).symm
      (lp.single 2 i ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)) =
      ((lp.single 2 i x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K) := by
  apply countableTensorEquiv.injective
  simp

variable [CompleteSpace H] [CompleteSpace K]

theorem countableOperatorEntry_spatialLeft
    (S : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) (i j : ℕ) :
    countableOperatorEntry
      ((countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv (spatialLeft S)) i j =
      spatialLeft (K := K) (countableOperatorEntry S i j) := by
  apply spatialTensorOp_ext
  intro x y
  simp only [countableOperatorEntry_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    countableTensorEquiv_symm_single]
  change countableTensorEquiv
      (spatialTensorOp S 1 ((lp.single 2 j x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K)) i = _
  simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self,
    countableTensorEquiv_tmul, countableTensorVector_apply]
  change _ = spatialTensorOp (countableOperatorEntry S i j) 1 _
  simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self,
    countableOperatorEntry_apply]

end

end KadisonKastler

end OAI
