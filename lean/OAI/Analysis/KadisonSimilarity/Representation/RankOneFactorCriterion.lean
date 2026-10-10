import OAI.Analysis.KadisonSimilarity.Representation.ProjectionFieldReduction

namespace OAI

/-! Rank-one tests for scalarity. A countable dense family suffices, including
on a variable projection range. These are the tests used to prove that the
central-decomposition fibers are factors. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Commuting with all rank-one operators forces an operator to be scalar. -/
theorem scalar_of_commutes_rankOne (T : H →L[ℂ] H)
    (hT : ∀ v w : H, T * InnerProductSpace.rankOne ℂ v w =
      InnerProductSpace.rankOne ℂ v w * T) :
    ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · let := hs
    exact ⟨0, Subsingleton.elim _ _⟩
  · let := hn
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    have hvv : inner ℂ v v ≠ 0 := (inner_self_ne_zero (𝕜 := ℂ)).2 hv
    have h (x : H) : inner ℂ v v • T x = inner ℂ v (T v) • x := by
      have hx := congrArg (fun S : H →L[ℂ] H => S v) (hT x v)
      simpa only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply, map_smul] using hx
    refine ⟨(inner ℂ v v)⁻¹ * inner ℂ v (T v), ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    change T x = ((inner ℂ v v)⁻¹ * inner ℂ v (T v)) • x
    calc
      T x = (inner ℂ v v)⁻¹ • (inner ℂ v v • T x) := by
        rw [smul_smul, inv_mul_cancel₀ hvv, one_smul]
      _ = (inner ℂ v v)⁻¹ • (inner ℂ v (T v) • x) := congrArg (fun z : H => (inner ℂ v v)⁻¹ • z) (h x)
      _ = _ := by rw [smul_smul]

/-- It suffices to test rank-one operators on a dense family of vectors. -/
theorem scalar_of_commutes_dense_rankOne {ι : Type*} (d : ι → H)
    (hd : DenseRange d) (T : H →L[ℂ] H)
    (hT : ∀ i j, T * InnerProductSpace.rankOne ℂ (d i) (d j) =
      InnerProductSpace.rankOne ℂ (d i) (d j) * T) :
    ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  apply scalar_of_commutes_rankOne T
  have hr : Continuous (fun q : H × H => InnerProductSpace.rankOne ℂ q.1 q.2) := by
    change Continuous (fun q : H × H =>
      (ContinuousLinearMap.smulRightL ℂ H H (innerSL ℂ q.2)) q.1)
    exact ((ContinuousLinearMap.smulRightL ℂ H H).continuous.comp
      ((innerSL ℂ).continuous.comp continuous_snd)).clm_apply continuous_fst
  have hc : IsClosed {q : H × H |
      T * InnerProductSpace.rankOne ℂ q.1 q.2 =
        InnerProductSpace.rankOne ℂ q.1 q.2 * T} := by
    exact isClosed_eq (continuous_const.mul hr) (hr.mul continuous_const)
  exact hd.induction_on₂ hc hT

/-- Projecting a dense family gives a dense family in the actual range. -/
theorem projectionFiber_denseRange {ι : Type*} (d : ι → H) (hd : DenseRange d)
    (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    DenseRange (fun i => projectionFiberRetraction p hp (d i)) := by
  have hr : Function.Surjective (projectionFiberRetraction p hp) := by
    intro x
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact projectionFiber_fixed p hp x
  exact hr.denseRange.comp hd (projectionFiberRetraction p hp).continuous

/-- Countably many compressed rank-one commutation identities suffice for
scalarity on the projection fiber. -/
theorem scalar_of_commutes_projection_rankOne {ι : Type*} (d : ι → H)
    (hd : DenseRange d) (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : projectionFiber p hp →L[ℂ] projectionFiber p hp)
    (hT : ∀ i j,
      T * InnerProductSpace.rankOne ℂ
        (projectionFiberRetraction p hp (d i)) (projectionFiberRetraction p hp (d j)) =
      InnerProductSpace.rankOne ℂ
        (projectionFiberRetraction p hp (d i)) (projectionFiberRetraction p hp (d j)) * T) :
    ∃ c : ℂ, T = c • (1 : projectionFiber p hp →L[ℂ] projectionFiber p hp) :=
  scalar_of_commutes_dense_rankOne _ (projectionFiber_denseRange d hd p hp) T hT

end KadisonSimilarity

end

end OAI
