import OAI.Analysis.KadisonKastler.StandardTracialPosition
import OAI.Analysis.KadisonKastler.Amenable
import OAI.Analysis.KadisonKastler.NearInclusionDistance
import OAI.Analysis.KadisonKastler.CommonPositionConjugationBound
import OAI.Analysis.FactorGeneration.TracialInclusion
import OAI.Analysis.FactorGeneration.HilbertLimits
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # The published common tracial position input

This is the application-specific part of Cameron--Christensen--Sinclair--
Smith--White--Wiggins, *Kadison--Kastler stable factors*, Duke Math. J. 163
(2014), Lemma 4.10(i)--(iv),(vii), printed pp. 20--21,
arXiv:1209.4116v3. The constant is `50948 * sqrt g` and the hypothesis is
`g < 1.74 * 10^(-13)`.

We specialize their amenable subalgebra hypothesis to a scalar relative
commutant, which is the only case used here. The output records algebraic
equivalences onto the represented images and their actual vector traces.
No isomorphism between the two nearby factors is assumed.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Common-position data retaining only the conclusions used in the
finite-factor application. -/
structure CommonTracialPositionData
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N) (g : ℝ)
    (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  left : VonNeumannAlgebra K
  right : VonNeumannAlgebra K
  common : VonNeumannAlgebra K
  common_le_left : common ≤ left
  common_le_right : common ≤ right
  leftEquiv : Algebra M ≃⋆ₐ[ℂ] Algebra left
  rightEquiv : Algebra N ≃⋆ₐ[ℂ] Algebra right
  commonEquiv : Algebra R ≃⋆ₐ[ℂ] Algebra common
  left_restrict : ∀ r : Algebra R,
    leftEquiv (coordinateInclusion hRM r) =
      coordinateInclusion common_le_left (commonEquiv r)
  right_restrict : ∀ r : Algebra R,
    rightEquiv (coordinateInclusion hRN r) =
      coordinateInclusion common_le_right (commonEquiv r)
  leftPosition : StandardTracialPosition left
  rightPosition : StandardTracialPosition right
  same_vector : leftPosition.vector = rightPosition.vector
  tolerance : ℝ
  tolerance_nonneg : 0 ≤ tolerance
  tolerance_lt : tolerance < 50948 * Real.sqrt g
  near_left : NearInclusion left right tolerance
  near_right : NearInclusion right left tolerance
  comparison : ∀ (x : Algebra M) (y : Algebra N), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
    ‖(leftEquiv x : K →L[ℂ] K) - (rightEquiv y : K →L[ℂ] K)‖ ≤
      tolerance + ‖(x : H →L[ℂ] H) - (y : H →L[ℂ] H)‖
  same_basicConstruction :
    Set.centralizer (Set.centralizer ((left : Set (K →L[ℂ] K)) ∪
      {(Generator.vectorOrbitClosure common.toStarSubalgebra leftPosition.vector).starProjection})) =
    Set.centralizer (Set.centralizer ((right : Set (K →L[ℂ] K)) ∪
      {(Generator.vectorOrbitClosure common.toStarSubalgebra leftPosition.vector).starProjection}))

/-- Precise published input, specialized to the common irreducible
amenable subalgebra needed by the finite-factor argument. -/
def PublishedCommonTracialPosition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N),
    Generator.IsII1Factor M.toStarSubalgebra →
    Generator.IsII1Factor N.toStarSubalgebra → IsInjective R →
    (∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M)) →
    ∀ g : ℝ, 0 < g → g < 174 / 1000000000000000 →
    NearInclusion M N g → NearInclusion N M g →
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (_ : TopologicalSpace.SeparableSpace K),
      Nonempty (CommonTracialPositionData M N R hRM hRN g K)

namespace CommonTracialPositionData

variable {M N R : VonNeumannAlgebra H} {hRM : R ≤ M} {hRN : R ≤ N} {g : ℝ}
  {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (d : CommonTracialPositionData M N R hRM hRN g K)

theorem left_isII1 (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    Generator.IsII1Factor d.left.toStarSubalgebra :=
  Generator.isII1Factor_of_starAlgEquiv d.leftEquiv hM
    (Generator.Tracial.traceHilbertVonNeumann_wotClosed d.left)

theorem right_isII1 (hN : Generator.IsII1Factor N.toStarSubalgebra) :
    Generator.IsII1Factor d.right.toStarSubalgebra :=
  Generator.isII1Factor_of_starAlgEquiv d.rightEquiv hN
    (Generator.Tracial.traceHilbertVonNeumann_wotClosed d.right)

/-- The original relative commutant transfers through the faithful
representations and the common restriction. -/
theorem irreducible_left
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (x : Algebra d.left)
    (hx : ∀ r : Algebra d.common,
      coordinateInclusion d.common_le_left r * x = x * coordinateInclusion d.common_le_left r) :
    ∃ c : ℂ, x = c • (1 : Algebra d.left) := by
  have hcomm (r : Algebra R) :
      coordinateInclusion hRM r * d.leftEquiv.symm x =
        d.leftEquiv.symm x * coordinateInclusion hRM r := by
    apply d.leftEquiv.injective
    rw [map_mul, map_mul]
    change d.leftEquiv (coordinateInclusion hRM r) * d.leftEquiv (d.leftEquiv.symm x) =
      d.leftEquiv (d.leftEquiv.symm x) * d.leftEquiv (coordinateInclusion hRM r)
    rw [d.left_restrict, d.leftEquiv.apply_symm_apply]
    exact hx (d.commonEquiv r)
  obtain ⟨c, hc⟩ := hirr (d.leftEquiv.symm x) hcomm
  refine ⟨c, ?_⟩
  calc
    x = d.leftEquiv (d.leftEquiv.symm x) := (d.leftEquiv.apply_symm_apply x).symm
    _ = d.leftEquiv (c • (1 : Algebra M)) := congrArg d.leftEquiv hc
    _ = c • (1 : Algebra d.left) := by
      change d.leftEquiv.toAlgEquiv.toLinearMap (c • 1) = _
      rw [d.leftEquiv.toAlgEquiv.toLinearMap.map_smul]
      congr 1
      exact d.leftEquiv.map_one

theorem distance_le : kkDistance d.left d.right ≤ 2 * d.tolerance :=
  kkDistance_le_two_mul_of_nearInclusions d.tolerance_nonneg d.near_left d.near_right

/-- The common-position output supplies the full tracial-conjugation
estimate and its module structure. -/
theorem conjugations_sub_le
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {b : ℝ} (hb : 2 * d.tolerance < b) :
    ‖(d.leftPosition.conjugation : K →L⋆[ℂ] K) -
      (d.rightPosition.conjugation : K →L⋆[ℂ] K)‖ ≤ 768 * b := by
  apply norm_tracialConjugations_sub_le_of_commonPosition
    d.common_le_left d.common_le_right d.leftPosition.trace d.leftPosition.finiteVectorTrace
    d.leftPosition.vector d.leftPosition.vector_norm d.leftPosition.vectorMap_norm
    d.leftPosition.cyclic
    (by
      change DenseRange (algebraVectorMap d.right d.leftPosition.vector)
      rw [d.same_vector]
      exact d.rightPosition.cyclic)
    d.leftPosition.conjugation d.rightPosition.conjugation
    d.leftPosition.conjugation_involutive d.rightPosition.conjugation_involutive
    d.leftPosition.conjugation_algebraVector
    (by simpa only [d.same_vector] using d.rightPosition.conjugation_algebraVector)
    (d.irreducible_left hirr) d.same_basicConstruction (d.distance_le.trans_lt hb)

end CommonTracialPositionData

end

end KadisonKastler

end OAI
