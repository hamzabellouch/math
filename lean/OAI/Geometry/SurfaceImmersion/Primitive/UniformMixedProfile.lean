import OAI.Geometry.SurfaceImmersion.Primitive.SecondCoefficientProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.HigherLongitudinalProfiles
import OAI.Geometry.SurfaceImmersion.Correction.SurfaceMeanPolynomial

namespace OAI

/-! The mixed derivative estimate is uniform for the actual varying slow
maps and the same finite represented coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_mixed_profile {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G),
      MapsTo (lowJet G) S Q → ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
      ∀ p ∈ S,
        let F := fun q => JetVelocityCoordinates.toEuclidean (G q)
        let f := finiteAnsatz F U ℓ (n+1) z
        ‖PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 0))
            (coordinateVector 1) p-
          (PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap F (coordinateVector 0))
            (coordinateVector 1) p+((U 0).angle.slow (coordinateVector 1)).fastValue ℓ z p)‖ ≤
          D*z/s^loss := by
  obtain ⟨loss,hb⟩ := VectorExpression.compact_coefficient_two_jets (S := S) O.isOpen hQ hQO
    (l.coefficientExpressions n) (n+1) (2*n+2) (by omega)
    (fun i _ => l.coefficientExpressions_smooth n i)
    (fun i hi a => (MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n i a).trans (by omega)) ℓ
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  refine ⟨2*(n+1)*D,mul_nonneg (by positivity) hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hGb U hU hrep p hp
  let W := globalCoefficients U hU
  have hc := hd G s z hz hzs hs1 hG hGQ hGb U (fun i _ => hrep i)
  have hC : 0 ≤ D/s^loss := div_nonneg hD (pow_nonneg (hz.le.trans hzs) _)
  have hss (i : ℕ) (hi : i < n+1) :
      ‖(((W i).slow (coordinateVector 0)).slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖(globalCoefficientDerivative (globalCoefficientDerivative (W i) 0) 1).val p
      ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [global_second_coefficientDerivative_eq_local (W i) (U i) rfl 0 1 hp]
    exact (hc i hi 0 1 p hp).2
  have has (i : ℕ) (hi : i < n+1) :
      ‖((W i).angle.slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖(globalCoefficientDerivative (globalCoefficientDerivative (W i) 2) 1).val p
      ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [global_second_coefficientDerivative_eq_local (W i) (U i) rfl 2 1 hp]
    exact (hc i hi 2 1 p hp).2
  have hout := PeriodicExpansion.mixed_profile_of_coefficients
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG) W ℓ n hx hy hz (hzs.trans hs1) hC hss has
  have he : (2*((n : ℝ)+1))*(D/s^loss)*z = (2*((n : ℝ)+1))*D*z/s^loss := by ring
  rw [he] at hout
  have hlead : ((W 0).angle.slow (coordinateVector 1)).fastValue ℓ z p =
      ((U 0).angle.slow (coordinateVector 1)).fastValue ℓ z p :=
    global_second_coefficientDerivative_eq_local (W 0) (U 0) rfl 2 1 hp _
  rw [hlead] at hout
  simpa only [W,globalCoefficients_finiteAnsatz,Function.comp_def,
    Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using hout

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
