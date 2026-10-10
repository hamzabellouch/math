import OAI.Geometry.IsometricImmersion.Darboux.QCoefficientTube
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qMarginObservable_segment_error {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : S ⊆ U)
    {M c L epsilon : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hbound : ∀ w ∈ qCompactTube g S M c, ‖fderiv ℝ (qMarginObservable g) w‖ ≤ L)
    {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1, stateSegment w0 w1 sigma ∈ qCompactTube g S M c)
    (hdist : ‖w1 - w0‖ ≤ epsilon) {sigma : ℝ} (hs : sigma ∈ Icc (0 : ℝ) 1)
    (i : Fin 3) :
    |qMarginObservable g (stateSegment w0 w1 sigma) i - qMarginObservable g w0 i| ≤ L * epsilon := by
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r => qMarginObservable g (stateSegment w0 w1 r))
        (fderiv ℝ (qMarginObservable g) (stateSegment w0 w1 t) (w1 - w0)) t := by
    have hw := qCompactTube_subset_domain hSU M hc (hsegment t ht)
    have hobs := ((qMarginObservable_contDiffOn hg hU).contDiffAt
      ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
    exact hobs.hasFDerivAt.comp_hasDerivAt t (stateSegment_hasDerivAt w0 w1 t)
  have hderivbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖fderiv ℝ (qMarginObservable g) (stateSegment w0 w1 t) (w1 - w0)‖ ≤ L * ‖w1 - w0‖ :=
    (fderiv ℝ (qMarginObservable g) (stateSegment w0 w1 t)).le_of_opNorm_le
      (hbound _ (hsegment t (Ico_subset_Icc_self ht))) _
  have hv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hderivbound sigma hs
  simp only [stateSegment_zero, sub_zero] at hv
  have hnorm : ‖qMarginObservable g (stateSegment w0 w1 sigma) - qMarginObservable g w0‖ ≤
      L * epsilon := by
    calc
      _ ≤ (L * ‖w1 - w0‖) * sigma := hv
      _ ≤ L * ‖w1 - w0‖ :=
        mul_le_of_le_one_right (mul_nonneg hL (norm_nonneg _)) hs.2
      _ ≤ L * epsilon := mul_le_mul_of_nonneg_left hdist hL
  have hi := (norm_le_pi_norm
    (qMarginObservable g (stateSegment w0 w1 sigma) - qMarginObservable g w0) i).trans hnorm
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi

theorem qMargin_uniform_error_of_coordinate_bounds {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {nu : ℝ} (hnu : 0 < nu) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ w0 w1 : DarbouxState,
      statePoint w0 = statePoint w1 → statePoint w0 ∈ S →
      (∀ j : Fin 6, |w0 j| ≤ M) → (∀ j : Fin 6, |w1 j| ≤ M) →
      ∀ B epsilon : ℝ, 0 ≤ B → 0 ≤ epsilon →
      (∀ r : Fin 2, |christoffel g r 0 0 (statePoint w0)| ≤ B) →
      (∀ j : Fin 6, |w1 j - w0 j| ≤ epsilon) →
      nu ≤ |stateQDenominator g w0| → (1 + 2 * B) * epsilon ≤ nu / 2 →
      ∀ sigma ∈ Icc (0 : ℝ) 1, ∀ i : Fin 3,
        |qMarginObservable g (stateSegment w0 w1 sigma) i - qMarginObservable g w0 i| ≤
          L * epsilon := by
  obtain ⟨L, hL, hbound⟩ := qMarginObservable_uniform_fderiv_bound hg hU hS hSU M (half_pos hnu)
  refine ⟨L, hL, ?_⟩
  intro w0 w1 hp hpS h0 h1 B epsilon hB heps hGamma hjet hbase hsmall sigma hs i
  apply qMarginObservable_segment_error hg hU hSU (half_pos hnu) (zero_le_one.trans hL) hbound
  · intro t ht
    exact stateSegment_mem_qCompactTube_of_error g hp hpS ht h0 h1 hB heps hGamma hjet hbase hsmall
  · exact state_distance_le_of_coordinate_error heps hjet
  · exact hs

theorem qMarginObservable_lower_of_error {g : MetricField} {w0 w : DarbouxState}
    {eta gamma chi error : ℝ}
    (herr : ∀ i : Fin 3, |qMarginObservable g w i - qMarginObservable g w0 i| ≤ error)
    (hE : eta ≤ stateEnergy g w0) (hQ : gamma ≤ qFirstCoefficient g 5 w0)
    (hD : chi ≤ (qFirstCoefficient g 4 w0 / 2) ^ 2 + qFirstCoefficient g 5 w0)
    (hsmallE : error ≤ eta / 2) (hsmallQ : error ≤ gamma / 2) (hsmallD : error ≤ chi / 2) :
    eta / 2 ≤ stateEnergy g w ∧ gamma / 2 ≤ qFirstCoefficient g 5 w ∧
      chi / 2 ≤ (qFirstCoefficient g 4 w / 2) ^ 2 + qFirstCoefficient g 5 w := by
  have he := (abs_le.mp (herr 0)).1
  have hq := (abs_le.mp (herr 1)).1
  have hd := (abs_le.mp (herr 2)).1
  change -error ≤ stateEnergy g w - stateEnergy g w0 at he
  change -error ≤ qFirstCoefficient g 5 w - qFirstCoefficient g 5 w0 at hq
  change -error ≤ ((qFirstCoefficient g 4 w / 2) ^ 2 + qFirstCoefficient g 5 w) -
    ((qFirstCoefficient g 4 w0 / 2) ^ 2 + qFirstCoefficient g 5 w0) at hd
  exact ⟨by linarith, by linarith, by linarith⟩

theorem qBaseMargins_of_actual_solution {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    {eta kappa A D : ℝ} (heta : 0 < eta) (hkappa : 0 < kappa) (hA : 0 < A)
    (hE : eta ≤ heightEnergy g z p) (hK : gaussianCurvature g p ≤ -kappa)
    (hAbound : |covHessian g z p 0 0| ≤ A)
    (hd : (hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p < 0)
    (hDbound : |(hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p| ≤ D) :
    eta ≤ stateEnergy g (qSolutionJet z p) ∧
      1 / D ≤ qFirstCoefficient g 5 (qSolutionJet z p) ∧
      kappa * eta / A ^ 2 ≤ (qFirstCoefficient g 4 (qSolutionJet z p) / 2) ^ 2 +
        qFirstCoefficient g 5 (qSolutionJet z p) := by
  have henergy : stateEnergy g (qSolutionJet z p) = heightEnergy g z p := by
    unfold stateEnergy
    rw [statePoint_qSolutionJet, stateGradient_qSolutionJet, jetEnergy_at_height hg hp z]
  refine ⟨by simpa only [henergy] using hE, ?_, ?_⟩
  · rw [q_xx_coefficient_eq_neg_inv_time_ratio hg hU hz hp hxx hyy hD]
    calc
      1 / D ≤ 1 / |(hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p| :=
        div_le_div₀ zero_le_one le_rfl (abs_pos.mpr (ne_of_lt hd)) hDbound
      _ = _ := by rw [abs_of_neg hd]; simp only [div_neg, neg_div]
  · rw [q_principal_discriminant hg hU (qSolutionJet_mem_domain hp hxx)]
    simp only [statePoint_qSolutionJet, stateQDenominator_qSolutionJet, henergy]
    have hk : kappa ≤ -gaussianCurvature g p := by linarith
    have hprod : kappa * eta ≤ -(gaussianCurvature g p * heightEnergy g z p) := by
      simpa only [neg_mul] using
        (mul_le_mul hk hE heta.le (hkappa.le.trans hk))
    have hsq : (covHessian g z p 0 0) ^ 2 ≤ A ^ 2 := by
      simpa only [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg (covHessian g z p 0 0)) hA.le).mpr hAbound)
    exact div_le_div₀ ((mul_nonneg hkappa.le heta.le).trans hprod) hprod
      (sq_pos_of_ne_zero hxx) hsq

theorem qHeightJetSegment_uniform_positive_margins {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {nu : ℝ} (hnu : 0 < nu) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (z0 z : Coord → ℝ) (p : Coord), p ∈ S →
      (∀ j : Fin 6, |qSolutionJet z0 p j| ≤ M) →
      (∀ j : Fin 6, |qSolutionJet z p j| ≤ M) →
      ∀ B epsilon eta gamma chi : ℝ, 0 ≤ B → 0 ≤ epsilon → 0 < eta → 0 < gamma → 0 < chi →
      (∀ r : Fin 2, |christoffel g r 0 0 p| ≤ B) →
      (∀ j : Fin 6, |qSolutionJet z p j - qSolutionJet z0 p j| ≤ epsilon) →
      nu ≤ |covHessian g z0 p 0 0| → (1 + 2 * B) * epsilon ≤ nu / 2 →
      eta ≤ stateEnergy g (qSolutionJet z0 p) → gamma ≤ qFirstCoefficient g 5 (qSolutionJet z0 p) →
      chi ≤ (qFirstCoefficient g 4 (qSolutionJet z0 p) / 2) ^ 2 + qFirstCoefficient g 5 (qSolutionJet z0 p) →
      L * epsilon ≤ eta / 2 → L * epsilon ≤ gamma / 2 → L * epsilon ≤ chi / 2 →
      ∀ sigma ∈ Icc (0 : ℝ) 1,
        nu / 2 ≤ |stateQDenominator g (qHeightJetSegment z0 z sigma p)| ∧
        eta / 2 ≤ stateEnergy g (qHeightJetSegment z0 z sigma p) ∧
        gamma / 2 ≤ qFirstCoefficient g 5 (qHeightJetSegment z0 z sigma p) ∧
        chi / 2 ≤ (qFirstCoefficient g 4 (qHeightJetSegment z0 z sigma p) / 2) ^ 2 +
          qFirstCoefficient g 5 (qHeightJetSegment z0 z sigma p) := by
  obtain ⟨L, hL, herr⟩ := qMargin_uniform_error_of_coordinate_bounds hg hU hS hSU M hnu
  refine ⟨L, hL, ?_⟩
  intro z0 z p hp h0 h1 B epsilon eta gamma chi hB heps heta hgamma hchi
    hGamma hjet hbase hsmall hE hQ hD hsmallE hsmallQ hsmallD sigma hs
  have hpw : statePoint (qSolutionJet z0 p) = statePoint (qSolutionJet z p) := by
    simp only [statePoint_qSolutionJet]
  have hGamma' : ∀ r : Fin 2, |christoffel g r 0 0 (statePoint (qSolutionJet z0 p))| ≤ B := by
    simpa only [statePoint_qSolutionJet] using hGamma
  have hbase' : nu ≤ |stateQDenominator g (qSolutionJet z0 p)| := by
    simpa only [stateQDenominator_qSolutionJet] using hbase
  have he := herr (qSolutionJet z0 p) (qSolutionJet z p) hpw
    (by simpa only [statePoint_qSolutionJet] using hp) h0 h1 B epsilon hB heps
      hGamma' hjet hbase' hsmall sigma hs
  refine ⟨stateQDenominator_segment_lower g hpw hs hB heps hGamma' hjet hbase' hsmall, ?_⟩
  exact qMarginObservable_lower_of_error he hE hQ hD hsmallE hsmallQ hsmallD

end SmoothLocal.HighEquation

end

end OAI
