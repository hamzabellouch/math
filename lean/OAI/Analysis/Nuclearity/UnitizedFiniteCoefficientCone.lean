import OAI.Analysis.PureInfiniteness.FiniteAbelianMerge
import OAI.Analysis.Nuclearity.UnitizedCoefficientOneStep

namespace OAI

/-! Finite sums in the coefficient cone, allowing output coefficients in the
unitization. The local relative copies still give implementing elements in
the original algebra. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D I J : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [Fintype I] [Fintype J] [DecidableEq J]

lemma merged_unitized_coefficient_identity (R : B → D) (T : J → B → D) (r : J → D)
    (a : J × I → Unitization ℂ D) (c : J × I → B) (b : B)
    (hrel : ∀ p q : J × I,
      star (r p.1) * R (star (c p) * b * c q) * r q.1 =
        if p.1 = q.1 then T p.1 (star (c p) * b * c q) else 0) :
    relativeCoefficientEnlargement R (fun p => unitizedRightMul (r p.1) (a p)) c b =
      ∑ j, unitizedCoefficientEnlargement (T j) (fun i => a (j, i))
        (fun i => c (j, i)) b := by
  have ht (p q : J × I) :
      star (unitizedRightMul (r p.1) (a p)) * R (star (c p) * b * c q) *
          unitizedRightMul (r q.1) (a q) =
      if p.1 = q.1 then unitizedSandwich (a p)
          (T p.1 (star (c p) * b * c q)) (a q) else 0 := by
    have he : star (unitizedRightMul (r p.1) (a p)) *
        R (star (c p) * b * c q) * unitizedRightMul (r q.1) (a q) =
        unitizedSandwich (a p)
          (star (r p.1) * R (star (c p) * b * c q) * r q.1) (a q) := by
      apply Unitization.inr_injective (R := ℂ)
      simp only [Unitization.inr_mul, Unitization.inr_star, inr_unitizedRightMul,
        inr_unitizedSandwich, star_mul, mul_assoc]
    rw [he, hrel]
    split_ifs
    · rfl
    · simp [unitizedSandwich, unitizedLeftMul, unitizedRightMul]
  simp only [relativeCoefficientEnlargement, ht, Fintype.sum_prod_type,
    unitizedCoefficientEnlargement]
  simp

variable {A : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem approximately_oneStepAlong_unitized_finite_coefficient_sum
    (hP : MainGap.PropertyP A) (β : B →⋆ₙₐ[ℂ] N) (T : J → B →L[ℂ] N)
    (hinner : ∀ j, ApproximatelyInnerAlong β (T j))
    (hpos : ∀ j b, 0 ≤ b → 0 ≤ T j b)
    (hcomm : ∀ j b c, Commute (T j b) (T j c))
    (a : J × I → Unitization ℂ N) (c : J × I → B) :
    ApproximatelyOneStepAlong β (fun b => ∑ j,
      unitizedCoefficientEnlargement (T j) (fun i => a (j, i)) (fun i => c (j, i)) b) := by
  classical
  intro F ε hε
  let G : Finset B := F.biUnion fun b => Finset.univ.biUnion fun p : J × I =>
    Finset.univ.image fun q : J × I => star (c p) * b * c q
  obtain ⟨R, r, hRinner, hRpos, hRcomm, hrecover⟩ :=
    finite_abelian_merge U hP β T hinner hpos hcomm G
  have hRone := approximately_oneStepAlong_of_abelian_range U hP β R hRinner hRpos hRcomm
  have hE := hRone.coefficientEnlargement β
    (fun p : J × I => unitizedRightMul (r p.1) (a p)) c
  obtain ⟨d, hd⟩ := hE F ε hε
  refine ⟨d, ?_⟩
  intro b hb
  have he := merged_unitized_coefficient_identity R (fun j => T j) r a c b (fun p q =>
    hrecover _ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_univ _, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩⟩) p.1 q.1)
  dsimp only
  rw [← he]
  exact hd b hb

end WeakPureInfiniteness

end

end OAI
