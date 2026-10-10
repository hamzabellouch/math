import Mathlib
import OAI.Probability.BinarySweep.Representations.MatrixIsotypicWhitening
import OAI.Probability.BinarySweep.Representations.IsotypicOrthogonal

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Irrep
open Representation Density

variable {G V W I : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [Fintype I] [DecidableEq I]

lemma projection_commutes_of_adjoint_invariant (S : Submodule ℂ W) (T : Module.End ℂ W)
    (hT : ∀ w ∈ S, T w ∈ S) (hTadj : ∀ w ∈ S, T.adjoint w ∈ S) (w : W) :
    T (S.starProjection w)=S.starProjection (T w) := by
  symm
  apply S.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (S.starProjection_apply_mem w))
  intro u hu
  rw [← map_sub,← LinearMap.adjoint_inner_right]
  exact S.starProjection_inner_eq_zero w (T.adjoint u) (hTadj u hu)

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem isotypicProjection_central (ρ : Representation ℂ G V)
    (σ : Representation ℂ G (EuclideanSpace ℂ I))
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) (M : Matrix I I ℂ)
    (hc : ∀ g v, M.toEuclideanLin (σ g v)=σ g (M.toEuclideanLin v)) :
    M*projectionMatrix (isotypicSpan ρ σ)=projectionMatrix (isotypicSpan ρ σ)*M := by
  let f : IntertwiningMap σ σ :=
    ⟨M.toEuclideanLin,fun g => LinearMap.ext (hc g)⟩
  have hf : ∀ w ∈ isotypicSpan ρ σ, M.toEuclideanLin.adjoint w ∈ isotypicSpan ρ σ := by
    intro w hw
    exact map_isotypic_le ρ σ σ (adjointIntertwiner σ σ hσ hσ f) ⟨w,hw,rfl⟩
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same,projectionMatrix_linear]
  apply LinearMap.ext
  intro v
  exact projection_commutes_of_adjoint_invariant (isotypicSpan ρ σ) M.toEuclideanLin
    (commuting_isotypic_invariant ρ σ M.toEuclideanLin hc) hf v

end BinaryCoordinateSweeps.Irrep

end

end OAI
