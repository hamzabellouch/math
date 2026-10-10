import OAI.Analysis.OperatorAlgebra.ScalarVectorDensity
import OAI.Analysis.ModularTheory.CommutantExpectation

namespace OAI

/-! Scalar L² slices characterize commutation in the amplification. In
particular, commutation with the represented C*-algebra automatically extends
to its concrete bicommutant, without assuming normality of any expectation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness
open KirchbergRordam.GenericRW.GroupedFactors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ)

def scalarOperatorSlice (R : Lp H 2 μ →L[ℂ] Lp H 2 μ) (f g : Lp ℂ 2 μ) : H →L[ℂ] H :=
  (scalarVectorLpCLM (H := H) μ f).adjoint.comp (R.comp (scalarVectorLpCLM (H := H) μ g))

lemma scalarOperatorSlice_inner (R : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (f g : Lp ℂ 2 μ) (x y : H) :
    inner ℂ (scalarOperatorSlice μ R f g x) y =
      inner ℂ (R (scalarVectorLp μ g x)) (scalarVectorLp μ f y) := by
  change inner ℂ ((scalarVectorLpCLM μ f).adjoint
    (R (scalarVectorLpCLM μ g x))) y = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

lemma scalarOperatorSlice_mul_pointwise (R : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (T : H →L[ℂ] H) (f g : Lp ℂ 2 μ) :
    scalarOperatorSlice μ (R * pointwiseLpRepresentation μ T) f g =
      scalarOperatorSlice μ R f g * T := by
  apply ContinuousLinearMap.ext
  intro x
  change (scalarVectorLpCLM μ f).adjoint
    (R (pointwiseLpRepresentation μ T (scalarVectorLp μ g x))) =
    (scalarVectorLpCLM μ f).adjoint (R (scalarVectorLp μ g (T x)))
  rw [scalarVectorLp_pointwise]

lemma scalarOperatorSlice_pointwise_mul (R : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (T : H →L[ℂ] H) (f g : Lp ℂ 2 μ) :
    scalarOperatorSlice μ (pointwiseLpRepresentation μ T * R) f g =
      T * scalarOperatorSlice μ R f g := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [scalarOperatorSlice_inner]
  change inner ℂ (pointwiseLpRepresentation μ T (R (scalarVectorLp μ g x)))
    (scalarVectorLp μ f y) = inner ℂ (T (scalarOperatorSlice μ R f g x)) y
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have ht : (pointwiseLpRepresentation μ T).adjoint = pointwiseLpRepresentation μ (star T) :=
    (map_star (pointwiseLpRepresentation μ) T).symm
  rw [ht, scalarVectorLp_pointwise, ← scalarOperatorSlice_inner]
  exact ContinuousLinearMap.adjoint_inner_right T _ _

theorem pointwise_commute_iff_slices (R : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (T : H →L[ℂ] H) :
    Commute (pointwiseLpRepresentation μ T) R ↔
      ∀ f g, Commute T (scalarOperatorSlice μ R f g) := by
  constructor
  · intro h f g
    have he := congrArg (fun X => scalarOperatorSlice μ X f g) h.eq
    rw [scalarOperatorSlice_pointwise_mul, scalarOperatorSlice_mul_pointwise] at he
    exact he
  · intro h
    apply scalarVectorLp_operator_ext μ
    intro f x g y
    have he := (h g f).eq
    rw [← scalarOperatorSlice_pointwise_mul, ← scalarOperatorSlice_mul_pointwise] at he
    exact (scalarOperatorSlice_inner μ _ g f x y).symm.trans
      ((congrArg (fun A : H →L[ℂ] H => inner ℂ (A x) y) he).trans
        (scalarOperatorSlice_inner μ _ g f x y))

theorem pointwise_commutation_extends_bicommutant {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (R : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hR : ∀ a, Commute (pointwiseLpRepresentation μ (π a)) R)
    (T : H →L[ℂ] H) (hT : T ∈ bicommutant π.range) :
    Commute (pointwiseLpRepresentation μ T) R := by
  apply (pointwise_commute_iff_slices μ R T).mpr
  intro f g
  have hs : scalarOperatorSlice μ R f g ∈ representationCommutant π := by
    apply mem_representationCommutant π
    intro a
    exact ((pointwise_commute_iff_slices μ R (π a)).mp (hR a) f g).symm
  have hc : scalarOperatorSlice μ R f g ∈ (bicommutant π.range).commutant :=
    (representation_bicommutant_commutant π _).mpr hs
  exact VonNeumannAlgebra.mem_commutant_iff.mp hc T hT

end WeakPureInfiniteness

end

end OAI
