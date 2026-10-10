import Mathlib.Analysis.InnerProductSpace.JointEigenspace

namespace OAI

/-!
# An orthonormal eigenbasis for a commuting symmetric family

This is the finite-dimensional simultaneous spectral step in the completion
argument. It specializes mathlib's joint-eigenspace decomposition and retains
an explicit common eigenvalue for each basis vector and each operator.
-/

namespace MUB6.Weiner

open Module
open scoped Function

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Finite tuples of actual eigenvalues, excluding irrelevant scalar tuples. -/
abbrev JointIndex (T : ι → End ℂ E) := ∀ i, (T i).Eigenvalues

noncomputable def jointSubspace (T : ι → End ℂ E) (χ : JointIndex T) : Submodule ℂ E :=
  ⨅ i, (T i).eigenspace (χ i : ℂ)

omit [Fintype ι] in
lemma jointSubspace_span (T : ι → End ℂ E) (hsym : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise (Commute on T)) : (⨆ χ, jointSubspace T χ) = ⊤ := by
  apply top_unique
  rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm]
  apply iSup_le
  intro γ
  by_cases hγ : (⨅ i, (T i).eigenspace (γ i)) = ⊥
  · rw [hγ]
    exact bot_le
  · let χ : JointIndex T := fun i =>
      ⟨γ i, fun hi => hγ (eq_bot_iff.mpr ((iInf_le _ i).trans (le_of_eq hi)))⟩
    exact le_iSup_of_le χ le_rfl

omit [Fintype ι] [FiniteDimensional ℂ E] in
lemma jointSubspace_orthogonal (T : ι → End ℂ E) (hsym : ∀ i, (T i).IsSymmetric) :
    OrthogonalFamily ℂ (fun χ => jointSubspace T χ)
      (fun χ => (jointSubspace T χ).subtypeₗᵢ) := by
  have hinj : Function.Injective (fun χ : JointIndex T => fun i => (χ i : ℂ)) := by
    intro χ ψ h
    funext i
    exact Subtype.ext (congrFun h i)
  exact (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym).comp hinj

/-- A finite commuting family of symmetric complex linear operators admits a
single orthonormal basis of simultaneous eigenvectors. -/
theorem exists_joint_eigenbasis (T : ι → End ℂ E)
    (hsym : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T)) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E)
      (ev : Fin (finrank ℂ E) → ι → ℂ),
      ∀ j i, T i (b j) = ev j i • b j := by
  classical
  have hortho := jointSubspace_orthogonal T hsym
  have hinternal : DirectSum.IsInternal (jointSubspace T) :=
    hortho.isInternal_iff.mpr (by simp [jointSubspace_span T hsym hcomm])
  let b := hinternal.subordinateOrthonormalBasis rfl hortho
  let ev : Fin (finrank ℂ E) → ι → ℂ := fun j i =>
    (hinternal.subordinateOrthonormalBasisIndex rfl j hortho i : ℂ)
  refine ⟨b, ev, ?_⟩
  intro j i
  have hj := hinternal.subordinateOrthonormalBasis_subordinate rfl j hortho
  exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hj i)

omit [FiniteDimensional ℂ E] in
/-- Every coordinate projection of an eigenbasis commutes with the operator.
This argument only uses the basis expansions, so no separate claim about the
reality of the eigenvalues is needed. -/
theorem commute_rankOne_of_eigenbasis {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis κ ℂ E) (T : End ℂ E) (ev : κ → ℂ)
    (heig : ∀ j, T (b j) = ev j • b j) (i : κ) :
    Commute T (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap := by
  classical
  change T.comp (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap =
    (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap.comp T
  apply b.toBasis.ext
  intro j
  by_cases hij : i = j
  · subst j
    simp [InnerProductSpace.rankOne_apply, heig]
  · simp [InnerProductSpace.rankOne_apply, heig,
      orthonormal_iff_ite.mp b.orthonormal i j, hij]

/-- The simultaneous eigenbasis can equivalently be characterized by its
commuting rank-one coordinate projections. -/
theorem exists_joint_projection_basis (T : ι → End ℂ E)
    (hsym : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T)) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      ∀ i j, Commute (T i) (InnerProductSpace.rankOne ℂ (b j) (b j)).toLinearMap := by
  obtain ⟨b, ev, heig⟩ := exists_joint_eigenbasis T hsym hcomm
  exact ⟨b, fun i j => commute_rankOne_of_eigenbasis b (T i) (fun j => ev j i)
    (fun j => heig j i) j⟩

end MUB6.Weiner

end OAI
