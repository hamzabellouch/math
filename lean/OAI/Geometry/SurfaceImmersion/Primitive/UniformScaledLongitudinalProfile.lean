import OAI.Geometry.SurfaceImmersion.Primitive.SecondCoefficientProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.HigherLongitudinalProfiles
import OAI.Geometry.SurfaceImmersion.Correction.SurfaceMeanPolynomial
import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceVelocityIdentities

namespace OAI

/-! Uniform control of the rescaled longitudinal second derivative of
the actual finite primitive. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetVelocityCoordinates
open JetPolynomial

lemma slot_x_derivative {G : Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G) (p : Base) :
    fderiv ℝ (fun q => slot 1 (lowJet G q)) p (coordinateVector 0) = slot 3 (lowJet G p) := by
  funext a
  have hs := (slot_smooth 1).comp (lowJet_smooth hG)
  have he := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector 0))
    (fderiv_apply (hs.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => lowJet G q (.inr (1,a))) p (coordinateVector 0) := he.symm
    _ = lowDerivative G 0 p (.inr (1,a)) := lowJet_coordinate_derivative G 0 _ p
    _ = slot 3 (lowJet G p) a := rfl

lemma euclidean_x_derivative {G : Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G) (p : Base) :
    fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (slot 1 (lowJet G q))) p
      (coordinateVector 0) = JetVelocityCoordinates.toEuclidean (slot 3 (lowJet G p)) := by
  have hs := (slot_smooth 1).comp (lowJet_smooth hG)
  have hd := (JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp p
    (hs.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = JetVelocityCoordinates.toEuclidean
        (fderiv ℝ (fun q => slot 1 (lowJet G q)) p (coordinateVector 0)) :=
      congrArg (fun L : Base →L[ℝ] Euclidean => L (coordinateVector 0)) hd
    _ = _ := congrArg JetVelocityCoordinates.toEuclidean (slot_x_derivative hG p)

lemma norm_slot_le (j : Fin 7) (J : LowJet) : ‖slot j J‖ ≤ ‖J‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg J)).mpr
  intro a
  exact norm_le_pi_norm J (.inr (j,a))

end ClosedSurfaceR4.JetVelocityCoordinates

namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem uniform_scaled_longitudinal_profile {S : TopologicalSpace.Opens JetPolynomial.Base}
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
        ‖z • PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 0))
            (coordinateVector 0) p-(U 0).angle.angle.fastValue ℓ z p‖ ≤ D*z/s^loss := by
  obtain ⟨loss,hb⟩ := VectorExpression.compact_coefficient_two_jets (S := S) O.isOpen hQ hQO
    (l.coefficientExpressions n) (n+1) (2*n+2) (by omega)
    (fun i _ => l.coefficientExpressions_smooth n i)
    (fun i hi a => (MetricPolynomial.coefficients_order _ _ _ _ _ 0 1 n i a).trans (by omega)) ℓ
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  let K := ‖JetVelocityCoordinates.toEuclidean.toContinuousLinearMap‖
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hK : 0 ≤ K := norm_nonneg _
  have hsum : 0 ≤ D+K*B := add_nonneg hD (mul_nonneg hK hB0)
  refine ⟨4*(n+1)*(D+K*B),mul_nonneg (by positivity) hsum,?_⟩
  intro G hG hGQ s z hz hzs hs1 hGb U hU hrep p hp
  let W := globalCoefficients U hU
  have hs : 0 < s := hz.trans_le hzs
  have hc := hd G s z hz hzs hs1 hG hGQ hGb U (fun i _ => hrep i)
  have hC : 0 ≤ (D+K*B)/s^loss := div_nonneg hsum (pow_nonneg hs.le _)
  have hCD : D/s^loss ≤ (D+K*B)/s^loss := div_le_div_of_nonneg_right
    (le_add_of_nonneg_right (mul_nonneg hK hB0)) (pow_nonneg hs.le _)
  have hb2 (i : ℕ) (hi : i < n+1) (k j : Fin 3) :
      ‖(globalCoefficientDerivative (globalCoefficientDerivative (W i) k) j).fastValue ℓ z p‖ ≤
        (D+K*B)/s^loss := by
    change ‖(globalCoefficientDerivative (globalCoefficientDerivative (W i) k) j).val p
      ((ℓ p/z : ℝ) : Period)‖ ≤ _
    rw [global_second_coefficientDerivative_eq_local (W i) (U i) rfl k j hp]
    exact (hc i hi k j p hp).2.trans hCD
  have hfirst : PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (G q))
      (coordinateVector 0) = fun q => JetVelocityCoordinates.toEuclidean (slot 1 (lowJet G q)) :=
    funext (euclidean_first_derivative hG 0)
  have hFxx : ‖PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (G q))
        (coordinateVector 0)) (coordinateVector 0) p‖ ≤ (D+K*B)/s^loss := by
    rw [hfirst]
    change ‖fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (slot 1 (lowJet G q))) p
      (coordinateVector 0)‖ ≤ _
    rw [euclidean_x_derivative hG]
    have hv : ‖JetVelocityCoordinates.toEuclidean (slot 3 (lowJet G p))‖ ≤ K*B :=
      (JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((norm_slot_le 3 _).trans (hGb.norm_le hp)) hK)
    apply hv.trans
    apply (le_div_iff₀ (pow_pos hs _)).mpr
    exact (mul_le_of_le_one_right (mul_nonneg hK hB0) (pow_le_one₀ hs.le hs1)).trans
      (le_add_of_nonneg_left hD)
  have hout := PeriodicExpansion.scaled_longitudinal_profile_of_coefficients
    (JetVelocityCoordinates.toEuclidean.contDiff.comp hG) W ℓ n hx hz (hzs.trans hs1) hC hFxx
    (fun i hi => hb2 i hi 0 0) (fun i hi => hb2 i hi 0 2)
    (fun i hi => hb2 i hi 2 0) (fun i hi => hb2 i hi 2 2)
  have he : (4*((n : ℝ)+1))*((D+K*B)/s^loss)*z = (4*((n : ℝ)+1))*(D+K*B)*z/s^loss := by ring
  rw [he] at hout
  have hlead : (W 0).angle.angle.fastValue ℓ z p = (U 0).angle.angle.fastValue ℓ z p :=
    global_second_coefficientDerivative_eq_local (W 0) (U 0) rfl 2 2 hp _
  rw [hlead] at hout
  simpa only [W,globalCoefficients_finiteAnsatz,Function.comp_def,
    Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] using hout

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
