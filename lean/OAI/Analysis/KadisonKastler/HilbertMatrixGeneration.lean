import OAI.Analysis.KadisonKastler.FullCornerEmbedding
import OAI.Analysis.KadisonKastler.OrthonormalMatrixUnits
import Mathlib.Basic.Denumerable

namespace OAI

/-! # Finite or countable matrix coordinates on separable Hilbert spaces -/

namespace KadisonKastler

open Generator
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A separable Hilbert space has either finite or natural-number matrix coordinates. -/
theorem separable_hilbertBasis_dichotomy [TopologicalSpace.SeparableSpace H] :
    (∃ n : ℕ, Nonempty (OrthonormalBasis (Fin n) ℂ H)) ∨
      Nonempty (HilbertBasis ℕ ℂ H) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hcount : Countable w := by
    have hd : Pairwise (fun i j : w => Disjoint (Metric.ball (b i) (1 / 2 : ℝ))
        (Metric.ball (b j) (1 / 2 : ℝ))) := by
      intro i j hij
      apply Metric.ball_disjoint_ball
      have hs : ‖b i - b j‖ ^ 2 = 2 := by
        rw [norm_sub_sq (𝕜 := ℂ), b.orthonormal.norm_eq_one i,
          b.orthonormal.norm_eq_one j, b.orthonormal.inner_eq_zero hij]
        norm_num
      rw [dist_eq_norm]
      norm_num only
      nlinarith [norm_nonneg (b i - b j)]
    exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
      (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
  let : Countable w := hcount
  rcases finite_or_infinite w with hfin | hinf
  · let : Fintype w := Fintype.ofFinite w
    exact Or.inl ⟨Fintype.card w, ⟨b.toOrthonormalBasis.reindex (Fintype.equivFin w)⟩⟩
  · let : Encodable w := Encodable.ofCountable w
    let : Denumerable w := Denumerable.ofEncodableOfInfinite w
    let e : ℕ ≃ w := (Denumerable.eqv w).symm
    refine Or.inr ⟨HilbertBasis.mk (b.orthonormal.comp e e.injective) ?_⟩
    have hr : Set.range (b ∘ e) = Set.range b := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp⟩
    rw [hr, b.dense_span]

/-- Rank-one entries of a Hilbert basis generate all ambient operators. -/
theorem mem_of_hilbertMatrixUnits {ι : Type*} [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (Q : VonNeumannAlgebra H)
    (hQ : ∀ i j, InnerProductSpace.rankOne ℂ (b i) (b j) ∈ Q)
    (T : H →L[ℂ] H) : T ∈ Q := by
  classical
  change T ∈ (Q : Set (H →L[ℂ] H))
  rw [← Q.centralizer_centralizer]
  intro S hS
  let o : ι := Classical.choice inferInstance
  let z : ℂ := inner ℂ (b o) (S (b o))
  have hcol (i : ι) : S (b i) = z • b i := by
    have h := congrArg (fun R : H →L[ℂ] H => R (b o)) (hS _ (hQ i o))
    have hoo : inner ℂ (b o) (b o) = 1 := by
      simpa using orthonormal_iff_ite.mp b.orthonormal o o
    simpa only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      hoo, one_smul] using h.symm
  have heq : S = z • (1 : H →L[ℂ] H) := by
    ext x
    have h₁ := (b.hasSum_repr x).mapL S
    have h₂ := (b.hasSum_repr x).mapL (z • (1 : H →L[ℂ] H))
    have hh : (fun i => S (b.repr x i • b i)) =
        (fun i => (z • (1 : H →L[ℂ] H)) (b.repr x i • b i)) := by
      funext i
      simp only [map_smul, hcol, smul_apply,
        one_apply_eq_self, smul_smul]
    rw [hh] at h₁
    exact h₁.unique h₂
  rw [heq]
  simp

/-- The initial rank-one corner of a natural-number Hilbert basis. -/
def hilbertBasisInitialSpace (b : HilbertBasis ℕ ℂ H) : Submodule ℂ H :=
  (InnerProductSpace.rankOne ℂ (b 0) (b 0)).range

instance (b : HilbertBasis ℕ ℂ H) : CompleteSpace (hilbertBasisInitialSpace b) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (InnerProductSpace.isIdempotentElem_rankOne_self (b.orthonormal.norm_eq_one 0))).completeSpace_coe

/-- Concrete full countable matrix units on the original Hilbert space. -/
def hilbertBasisFullCorner (b : HilbertBasis ℕ ℂ H) :
    FullMatrixCorner (hilbertBasisInitialSpace b) where
  entry i j := InnerProductSpace.rankOne ℂ (b i) (b j)
  star_entry i j := by
    rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
  mul_entry i j k l := by
    change (InnerProductSpace.rankOne ℂ (b i) (b j)).comp
      (InnerProductSpace.rankOne ℂ (b k) (b l)) = _
    rw [InnerProductSpace.rankOne_comp_rankOne,
      orthonormal_iff_ite.mp b.orthonormal]
    split_ifs <;> simp_all
  zero_zero := by
    obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp
      (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) (b.orthonormal.norm_eq_one 0))
    exact h
  total x := by
    simpa only [InnerProductSpace.rankOne_apply, ← b.repr_apply_apply] using b.hasSum_repr x

theorem hilbertBasisFullCorner_mem_scalar (b : HilbertBasis ℕ ℂ H)
    (T : H →L[ℂ] H) : T ∈ (hilbertBasisFullCorner b).scalarMatrixAlgebra :=
  mem_of_hilbertMatrixUnits b _ (hilbertBasisFullCorner b).entry_mem_scalarMatrixAlgebra T

end

end KadisonKastler

end OAI
