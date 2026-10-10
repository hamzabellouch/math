import Mathlib
import OAI.Analysis.LaughlinFock.Flow

namespace OAI

/-! Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory Topology

private theorem matrix_unitary_isClosed {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) :=
  isClosed_unitary

section UnitaryCompact
open scoped Matrix.Norms.Elementwise

 
theorem unitaryMatrix_compactSpace {ι : Type*} [Fintype ι] [DecidableEq ι] :
    CompactSpace (Matrix.unitaryGroup ι ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Matrix ι ι ℂ) 1).of_isClosed_subset
    matrix_unitary_isClosed
  intro U hU
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact entrywise_sup_norm_bound_of_unitary hU

end UnitaryCompact

 
def unitaryConjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  U.val * M * U.valᴴ

theorem unitaryConjugation_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : unitaryConjugation 1 M = M := by
  simp [unitaryConjugation]

theorem unitaryConjugation_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) :
    unitaryConjugation (U*V) M = unitaryConjugation U (unitaryConjugation V M) := by
  simp [unitaryConjugation, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem unitaryConjugation_inv_cancel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) :
    unitaryConjugation U⁻¹ (unitaryConjugation U M) = M := by
  rw [← unitaryConjugation_mul, inv_mul_cancel, unitaryConjugation_one]

section Simultaneous
variable {J : Type*} (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]

 

abbrev UnitaryFamily := ∀ j, Matrix.unitaryGroup (I j) ℂ

 

def covarianceSubgroup {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ) :
    Subgroup (UnitaryFamily I) where
  carrier := {g | ∀ M, L (unitaryConjugation (g i) M) = unitaryConjugation (g j) (L M)}
  one_mem' := by intro M; simp only [Pi.one_apply, unitaryConjugation_one]
  mul_mem' := by
    intro g h hg hh M
    change ∀ M, L (unitaryConjugation (g i) M) = unitaryConjugation (g j) (L M) at hg
    change ∀ M, L (unitaryConjugation (h i) M) = unitaryConjugation (h j) (L M) at hh
    simp only [Pi.mul_apply, unitaryConjugation_mul, hg, hh]
  inv_mem' := by
    intro g hg M
    have h := congrArg (unitaryConjugation (g j)⁻¹)
      (hg (unitaryConjugation (g i)⁻¹ M))
    simpa only [Pi.inv_apply, ← unitaryConjugation_mul, mul_inv_cancel, inv_mul_cancel,
      unitaryConjugation_one] using h.symm

section Closed
open scoped Matrix.Norms.Elementwise

 

theorem covarianceSubgroup_isClosed {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ) :
    IsClosed (covarianceSubgroup I L : Set (UnitaryFamily I)) := by
  have hL : Continuous L := L.toContinuousLinearMap.continuous
  change IsClosed {g : UnitaryFamily I | ∀ M,
    L (unitaryConjugation (g i) M) = unitaryConjugation (g j) (L M)}
  simp_rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro M
  apply isClosed_eq
  · apply hL.comp
    unfold unitaryConjugation
    fun_prop
  · unfold unitaryConjugation
    fun_prop

end Closed

end Simultaneous

section Flows
open scoped Matrix.Norms.Operator
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]

 
private theorem rotation_exp_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) (t : ℝ) :
    exp ((t : ℂ) • A) ∈ Matrix.unitaryGroup ι ℂ := by
  let B : Matrix ι ι ℂ := (t : ℂ) • A
  have hB : Bᴴ = -B := by
    dsimp only [B]
    rw [Matrix.conjTranspose_smul, hA]
    simp
  have hstar : (exp B)ᴴ = exp (-B) := by
    rw [← Matrix.exp_conjTranspose, hB]
  change (exp B) ∈ unitary (Matrix ι ι ℂ)
  rw [Unitary.mem_iff]
  change (exp B)ᴴ * exp B = 1 ∧ exp B * (exp B)ᴴ = 1
  rw [hstar]
  constructor
  · simpa only [neg_add_cancel, exp_zero] using!
      (exp_add_of_commute (Commute.refl B).neg_left).symm
  · simpa only [add_neg_cancel, exp_zero] using!
      (exp_add_of_commute (Commute.refl B).neg_right).symm

def rotationFlow (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) (s : σ) (t : ℝ) : UnitaryFamily I :=
  fun j => ⟨exp ((t : ℂ) • X s j), rotation_exp_unitary (X s j) (hX s j) t⟩

theorem rotationFlow_conjugation
    (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) (s : σ) (t : ℝ) (j : J)
    (M : Matrix (I j) (I j) ℂ) :
    unitaryConjugation (rotationFlow X hX s t j) M =
      exp ((t : ℂ) • X s j) * M * exp ((t : ℂ) • (-X s j)) := by
  unfold unitaryConjugation rotationFlow
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hX]
  simp

 

def rotationGroup (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) : Subgroup (UnitaryFamily I) :=
  (Subgroup.closure (Set.range (fun p : σ × ℝ => rotationFlow X hX p.1 p.2))).topologicalClosure

theorem rotationFlow_mem_group (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) (s : σ) (t : ℝ) :
    rotationFlow X hX s t ∈ rotationGroup X hX :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨(s,t), rfl⟩)

 

theorem rotationGroup_covariance (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ)
    (hL : ∀ s M, L (X s i * M - M * X s i) = X s j * L M - L M * X s j)
    (g : rotationGroup X hX) (M : Matrix (I i) (I i) ℂ) :
    L (unitaryConjugation (g.val i) M) = unitaryConjugation (g.val j) (L M) := by
  have hle : rotationGroup X hX ≤ covarianceSubgroup I L := by
    apply Subgroup.topologicalClosure_minimal
    · apply (Subgroup.closure_le _).2
      rintro _ ⟨⟨s,t⟩,rfl⟩ M
      simp only [rotationFlow_conjugation]
      exact matrixExp_conjugation_naturality _ _ L (hL s) M t
    · exact covarianceSubgroup_isClosed I L
  exact hle g.property M

instance rotationGroup_compactSpace (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) : CompactSpace (rotationGroup X hX) := by
  let (j : J) : CompactSpace (Matrix.unitaryGroup (I j) ℂ) := unitaryMatrix_compactSpace
  apply isCompact_iff_compactSpace.mp
  exact (Subgroup.isClosed_topologicalClosure _).isCompact

end Flows
end LaughlinFock
end

end OAI
