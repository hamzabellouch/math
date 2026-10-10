import OAI.Probability.InvariantIsing.Fields.FieldFiniteAverageDerivative
import OAI.Probability.InvariantIsing.Fields.FieldFiniteCovariance

namespace OAI

/-! Coordinate form of the differentiated finite-height Gaussian average. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma affine_average_coordinate_derivative (hI : IsOpen I)
    (α B : FieldCovariate n → ℝ → ℝ)
    (A : Fin n → FieldCovariate n → ℝ → ℝ)
    (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {CA CE : ℝ} (hCA : 0 ≤ CA) (hCE : 0 ≤ CE)
    (hα : ∀ q, Measurable (α q)) (hA : ∀ i q, Measurable (A i q))
    (hB : ∀ q, Measurable (B q))
    (bα : ∀ q, q.1 ∈ I → ∀ u, |α q u| ≤ CA * (1 + |u|))
    (bA : ∀ i q, q.1 ∈ I → ∀ u, |A i q u| ≤ CE * (1 + |u|) ^ 2)
    (bB : ∀ q, q.1 ∈ I → ∀ u, |B q u| ≤ CE * (1 + |u|) ^ 2)
    (dα : ∀ q, q.1 ∈ I → ∀ u,
      HasFDerivAt (fun r => α r u) (fieldFiniteLinear (fun i => A i q u) (B q u)) q)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q => ∫ u, α q u ∂F.affineLaw a v ζ q)
      (fieldFiniteLinear
        (fun i => (∫ u, A i p u ∂F.affineLaw a v ζ p) + ζ *
          ((∫ u, α p u * F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p) -
            (∫ u, α p u ∂F.affineLaw a v ζ p) *
              (∫ u, F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p)))
        ((∫ u, B p u ∂F.affineLaw a v ζ p) + ζ *
          ((∫ u, α p u * F.shiftedMean a v u p ∂F.affineLaw a v ζ p) -
            (∫ u, α p u ∂F.affineLaw a v ζ p) *
              (∫ u, F.shiftedMean a v u p ∂F.affineLaw a v ζ p)))) p := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  let DA : FieldCovariate n → ℝ → FieldCovariate n →L[ℝ] ℝ :=
    fun q u => fieldFiniteLinear (fun i => A i q u) (B q u)
  let ν := F.affineLaw a v ζ p
  have hnorm (q : FieldCovariate n) (hq : q.1 ∈ I) (u : ℝ) :
      ‖DA q u‖ ≤ ((n : ℝ) + 1) * CE * (1 + |u|) ^ 2 := by
    refine (norm_fieldFiniteLinear_le _ _).trans ?_
    calc
      _ ≤ (∑ _i : Fin n, CE * (1 + |u|) ^ 2) + CE * (1 + |u|) ^ 2 :=
        add_le_add (Finset.sum_le_sum (fun i _ => bA i q hq u)) (bB q hq u)
      _ = _ := by simp; ring
  have hd := F.affine_average_hasFDerivAt hI α DA a v ζ hR hlo hhi hc
    hCA (show 0 ≤ ((n : ℝ) + 1) * CE by positivity) hα
    (fun q => (measurable_fieldFiniteLinear (fun i => hA i q) (hB q)).aestronglyMeasurable)
    bα hnorm dα hp
  have hq := (F.affineLaw_quadratic_moment a v ζ hp).1
  have hiA (i : Fin n) : Integrable (A i p) ν :=
    field_integrable_of_quadratic_bound ν hq (hA i p) CE (bA i p hp)
  have hiB : Integrable (B p) ν :=
    field_integrable_of_quadratic_bound ν hq (hB p) CE (bB p hp)
  let T := F.KP + F.KX * R
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have bt (i : Fin n) (u : ℝ) : |F.shiftedTangent a v i u p| ≤ T * (1 + |u|) :=
    F.shiftedTangent_bound a v i u hp hR (hc p.1 hp i)
  have hiT (i : Fin n) : Integrable (fun u => F.shiftedTangent a v i u p) ν :=
    F.affineLaw_linear_integrable a v ζ hp (F.measurable_shiftedTangent a v i p) hT (bt i)
  have hiX : Integrable (fun u => F.shiftedMean a v u p) ν :=
    F.affineLaw_bounded_integrable a v ζ hp (F.measurable_shiftedMean a v p) F.KX
      (fun u => F.bX _ hp)
  have hiαT (i : Fin n) : Integrable (fun u => α p u * F.shiftedTangent a v i u p) ν := by
    apply field_integrable_of_quadratic_bound ν hq
      ((hα p).mul (F.measurable_shiftedTangent a v i p)) (CA * T)
    intro u
    change |α p u * F.shiftedTangent a v i u p| ≤ CA * T * (1 + |u|) ^ 2
    rw [abs_mul]
    calc
      _ ≤ (CA * (1 + |u|)) * (T * (1 + |u|)) :=
        mul_le_mul (bα p hp u) (bt i u) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hiαX : Integrable (fun u => α p u * F.shiftedMean a v u p) ν := by
    apply field_integrable_of_quadratic_bound ν hq
      ((hα p).mul (F.measurable_shiftedMean a v p)) (CA * F.KX)
    intro u
    change |α p u * F.shiftedMean a v u p| ≤ CA * F.KX * (1 + |u|) ^ 2
    rw [abs_mul]
    calc
      _ ≤ (CA * (1 + |u|)) * F.KX :=
        mul_le_mul (bα p hp u) (F.bX (F.shiftPoint a v u p) hp) (abs_nonneg _) (by positivity)
      _ = (CA * F.KX) * (1 + |u|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) (by positivity)
  have he := field_finite_covariance ν ζ (α p) (fun i => A i p)
    (fun i u => F.shiftedTangent a v i u p) (B p) (fun u => F.shiftedMean a v u p)
    hiA hiB hiT hiX hiαT hiαX
  change ((∫ u, DA p u + (ζ * α p u) • F.affineDifferential a v p u ∂ν) -
    (∫ u, α p u ∂ν) • (∫ u, ζ • F.affineDifferential a v p u ∂ν)) = _ at he
  change HasFDerivAt _ ((∫ u, DA p u + (ζ * α p u) • F.affineDifferential a v p u ∂ν) -
    (∫ u, α p u ∂ν) • (∫ u, ζ • F.affineDifferential a v p u ∂ν)) p at hd
  rw [he] at hd
  exact hd

end FieldFiniteFamily
end InvariantIsing

end

end OAI
