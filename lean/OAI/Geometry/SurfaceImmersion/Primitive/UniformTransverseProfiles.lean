import OAI.Geometry.SurfaceImmersion.Geometry.TransverseCoefficientBounds
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicCoefficientProfiles
import OAI.Geometry.SurfaceImmersion.Correction.SurfaceMeanPolynomial

namespace OAI

/-! The actual primitive's transverse first and second derivatives approach
the slow baseline uniformly over all maps in the fixed compact jet domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_transverse_profiles {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (hy : ℓ (coordinateVector 1) = 0) :
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
        ‖PeriodicExpansion.directionalMap f (coordinateVector 1) p-
          PeriodicExpansion.directionalMap F (coordinateVector 1) p‖ ≤ D*z/s^loss ∧
        ‖PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 1))
            (coordinateVector 1) p-
          PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap F (coordinateVector 1))
            (coordinateVector 1) p‖ ≤ D*z/s^loss := by
  obtain ⟨loss,hb⟩ := VectorExpression.compact_transverse_coefficients (S := S) O.isOpen hQ hQO
    (l.coefficientExpressions n) (n+1) (2*n+2) (by omega)
    (fun i _ => l.coefficientExpressions_smooth n i)
    (fun i hi a => (MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n i a).trans (by omega)) ℓ
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  refine ⟨(n+1)*D,mul_nonneg (by positivity) hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hGb U hU hrep p hp
  let W := globalCoefficients U hU
  have hw1 (i : ℕ) (q : JetPolynomial.Base) (hq : q ∈ S) (t : Period) :
      ((W i).slow (coordinateVector 1)).val q t =
        ((U i).slow (coordinateVector 1)).val q t :=
    global_slow_eq_local (W i) (U i) rfl (coordinateVector 1) hq t
  have hw2 (i : ℕ) (q : JetPolynomial.Base) (hq : q ∈ S) (t : Period) :
      (((W i).slow (coordinateVector 1)).slow (coordinateVector 1)).val q t =
        (((U i).slow (coordinateVector 1)).slow (coordinateVector 1)).val q t :=
    global_slow_eq_local_of_eqOn ((W i).slow (coordinateVector 1))
      ((U i).slow (coordinateVector 1)) (hw1 i) (coordinateVector 1) hq t
  have hc := hd G s z hz hzs hs1 hG hGQ hGb U (fun i _ => hrep i)
  have hC : 0 ≤ D/s^loss := div_nonneg hD (pow_nonneg (hz.le.trans hzs) _)
  have hfirst (i : ℕ) (hi : i < n+1) :
      ‖((W i).slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖((W i).slow (coordinateVector 1)).val p ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [hw1 i p hp]
    exact hc i hi false p hp
  have hsecond (i : ℕ) (hi : i < n+1) :
      ‖(((W i).slow (coordinateVector 1)).slow (coordinateVector 1)).fastValue ℓ z p‖ ≤ D/s^loss := by
    change ‖(((W i).slow (coordinateVector 1)).slow (coordinateVector 1)).val p
      ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [hw2 i p hp]
    exact hc i hi true p hp
  have hout := PeriodicExpansion.transverse_profiles_of_coefficients
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG) W ℓ (n+1) hy hz (hzs.trans hs1) hC hfirst hsecond
  have he : ((n+1 : ℕ) : ℝ)*(D/s^loss)*z = ((n+1 : ℕ) : ℝ)*D*z/s^loss := by ring
  rw [he] at hout
  simpa only [W,globalCoefficients_finiteAnsatz,Function.comp_def,
    Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using hout

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
