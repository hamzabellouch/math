import OAI.Analysis.KadisonSimilarity.Representation.ProperlyInfiniteEstimate

namespace OAI

/-! The adjoint homomorphism and the exact row-to-column transfer. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Taking adjoints in both source and target preserves the algebra map. -/
def sharpHom (π : BoundedUnitalHom A H) : BoundedUnitalHom A H :=
  ⟨{
    toFun := fun a => star (π.1 (star a))
    map_one' := by simp
    map_mul' := by intro a b; simp only [star_mul, map_mul]
    map_zero' := by simp
    map_add' := by intro a b; simp only [star_add, map_add]
    commutes' := by
      intro z
      change star (π.1 (star (algebraMap ℂ A z))) = algebraMap ℂ (H →L[ℂ] H) z
      simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one,
        star_star] },
    continuous_star.comp (π.2.comp continuous_star)⟩

@[simp] theorem sharpHom_apply (π : BoundedUnitalHom A H) (a : A) :
    (sharpHom π).1 a = star (π.1 (star a)) := rfl

/-- Every pointwise operator bound is preserved by the sharp operation. -/
theorem sharpHom_bound (π : BoundedUnitalHom A H) {C : ℝ}
    (hπ : ∀ a, ‖π.1 a‖ ≤ C * ‖a‖) (a : A) :
    ‖(sharpHom π).1 a‖ ≤ C * ‖a‖ := by
  simpa only [sharpHom_apply, norm_star] using hπ (star a)

/-- The concrete finite rectangular adjoint is entrywise adjoint and transpose. -/
theorem rectangularMatrixOperator_adjoint {F K : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {p q : ℕ} (X : Matrix (Fin p) (Fin q) (K →L[ℂ] F)) :
    (rectangularMatrixOperator X).adjoint =
      rectangularMatrixOperator (fun i j => (X j i).adjoint) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, rectangularMatrixOperator_apply]
  have hleft (i : Fin q) := rectangularMatrixOperator_apply (F := K) (K := F)
    (show Matrix (Fin q) (Fin p) (F →L[ℂ] K) from fun i j => (X j i).adjoint) x i
  simp_rw [hleft]
  change (∑ i : Fin q, inner ℂ (∑ j : Fin p, (X j i).adjoint (x j)) (y i)) =
    ∑ j : Fin p, inner ℂ (x j) (∑ i : Fin q, X j i (y i))
  simp only [sum_inner, inner_sum, ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

variable [PartialOrder A] [StarOrderedRing A]

/-- A row estimate for the sharp map is the same column estimate for the
original homomorphism, with the native rectangular C-star matrix norm. -/
theorem columnBound_of_sharp_rowBound (π : BoundedUnitalHom A H) {C : ℝ}
    (hrow : RowBound (sharpHom π).1 C) : ColumnBound π.1 C := by
  intro n X
  have h := hrow n (fun i j => star (X j i))
  have hm : rectangularMatrixOperator
      (Matrix.map (fun i j => star (X j i)) (sharpHom π).1) =
      (rectangularMatrixOperator (X.map π.1)).adjoint := by
    rw [rectangularMatrixOperator_adjoint]
    congr 1
    funext i j
    change star (π.1 (star (star (X j i)))) = (π.1 (X j i)).adjoint
    rw [star_star, ContinuousLinearMap.star_eq_adjoint]
  rw [hm, ContinuousLinearMap.adjoint.norm_map] at h
  have hn : ‖CStarMatrix.ofMatrix (fun i j => star (X j i))‖ =
      ‖CStarMatrix.ofMatrix X‖ :=
    norm_cstarMatrix_conjTranspose (CStarMatrix.ofMatrix X)
  rwa [hn] at h

/-- Only the row half of Dickson's estimate needs an analytic proof. -/
theorem dicksonTwoBound_of_row
    (hrow : ∀ π : BoundedUnitalHom A H, (∀ a, ‖π.1 a‖ ≤ 2 * ‖a‖) →
      RowBound π.1 (4 * Real.sqrt 2)) : DicksonTwoBound (A := A) H := by
  intro π hπ
  exact ⟨hrow π hπ, columnBound_of_sharp_rowBound π
    (hrow (sharpHom π) (sharpHom_bound π hπ))⟩

end KadisonSimilarity

end

end OAI
