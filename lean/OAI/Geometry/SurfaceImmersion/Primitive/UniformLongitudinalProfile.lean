import OAI.Geometry.SurfaceImmersion.Geometry.CoefficientJetBounds
import OAI.Geometry.SurfaceImmersion.Primitive.LongitudinalCoefficientProfile
import OAI.Geometry.SurfaceImmersion.Correction.SurfaceMeanPolynomial

namespace OAI

/-! The first longitudinal profile is uniform over the compact admissible
jet family, with a fixed loss and the actual represented coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_longitudinal_profile {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (hx : ℓ (coordinateVector 0) = 1) :
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
        ‖PeriodicExpansion.directionalMap f (coordinateVector 0) p-
          (PeriodicExpansion.directionalMap F (coordinateVector 0) p+(U 0).angle.fastValue ℓ z p)‖ ≤
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
  have hfirst (i : ℕ) (hi : i < n+1) :
      ‖((W i).slow (coordinateVector 0)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖((W i).slow (coordinateVector 0)).val p ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [global_slow_eq_local (W i) (U i) rfl (coordinateVector 0) hp]
    exact (hc i hi 0 0 p hp).1
  have hangle (i : ℕ) (hi : i < n+1) :
      ‖(W i).angle.fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖(W i).angle.val p ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [global_angle_eq_local (W i) (U i) rfl hp]
    exact (hc i hi 2 0 p hp).1
  have hout := PeriodicExpansion.longitudinal_profile_of_coefficients
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG) W ℓ n hx hz (hzs.trans hs1) hC hfirst hangle
  have he : (2*((n : ℝ)+1))*(D/s^loss)*z = (2*((n : ℝ)+1))*D*z/s^loss := by ring
  rw [he] at hout
  have hangle0 : (W 0).angle.fastValue ℓ z p = (U 0).angle.fastValue ℓ z p :=
    global_angle_eq_local (W 0) (U 0) rfl hp _
  rw [hangle0] at hout
  simpa only [W,globalCoefficients_finiteAnsatz,Function.comp_def,
    Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using hout

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
