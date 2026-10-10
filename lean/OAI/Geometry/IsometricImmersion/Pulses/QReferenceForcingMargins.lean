import OAI.Geometry.IsometricImmersion.Darboux.QSameStripMargins
import OAI.Geometry.IsometricImmersion.Pulses.ForcingCoefficientSign

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Pulse

theorem actual_det_upper_of_entry_bound (g : MetricField) (p : Coord) {G : ℝ}
    (hG : 0 ≤ G) (hg : ∀ i j, |g p i j| ≤ G) : (g p).det ≤ 2*G^2 := by
  rw [Matrix.det_fin_two]
  calc
    g p 0 0*g p 1 1-g p 0 1*g p 1 0 ≤
        |g p 0 0*g p 1 1|+|g p 0 1*g p 1 0| := by
      linarith [le_abs_self (g p 0 0*g p 1 1),
        neg_le_abs (g p 0 1*g p 1 0)]
    _ = |g p 0 0| *|g p 1 1|+|g p 0 1| *|g p 1 0| := by rw [abs_mul,abs_mul]
    _ ≤ G*G+G*G := add_le_add
      (mul_le_mul (hg 0 0) (hg 1 1) (abs_nonneg _) hG)
      (mul_le_mul (hg 0 1) (hg 1 0) (abs_nonneg _) hG)
    _ = _ := by ring

theorem exists_uniform_reference_forcing_margins (G R M M0 : ℝ)
    {d nu c eta kappa : ℝ} (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hM0 : 0 ≤ M0)
    (hd : 0 < d) (hnu : 0 < nu) (hc : 0 < c) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ epsilon A : ℝ, 0 < epsilon ∧ 1 ≤ A ∧
      ∀ (g g0 : MetricField) (z z0 : Coord → ℝ) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn g0 U → IsOpen U →
      ContDiffOn ℝ ∞ z U → ContDiffOn ℝ ∞ z0 U →
      ∀ left right a b : ℝ, a ≤ b →
      closedRectangle left right a b ⊆ U →
      (∀ p ∈ closedRectangle left right a b, ‖p‖ ≤ R) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g x i j) p‖ ≤ G) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g0 x i j) p‖ ≤ G) →
      CoordinateBound z (closedRectangle left right a b) 3 M →
      CoordinateBound z0 (closedRectangle left right a b) 3 M0 →
      (∀ p ∈ closedRectangle left right a b, d ≤ |(g p).det|) →
      (∀ p ∈ closedRectangle left right a b, d ≤ |(g0 p).det|) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g0 x i j - g x i j) p‖ ≤ epsilon) →
      (M + M0) * (b - a) ≤ epsilon →
      (∀ x ∈ Ioo left right, z0 (boxPoint x a) = z (boxPoint x a)) →
      (∀ x ∈ Ioo left right,
        coordPartial 1 z0 (boxPoint x a) = coordPartial 1 z (boxPoint x a)) →
      (∀ p ∈ closedRectangle left right a b, nu ≤ |covHessian g z p 0 0|) →
      (∀ p ∈ closedRectangle left right a b, c ≤ |covHessian g z p 1 1|) →
      (∀ p ∈ closedRectangle left right a b, eta ≤ heightEnergy g z p) →
      (∀ p ∈ closedRectangle left right a b, gaussianCurvature g p ≤ -kappa) →
      (∀ p ∈ closedRectangle left right a b,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ closedRectangle left right a b,
        (hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p < 0) →
      ∀ l r : ℝ, left < l → r < right →
      ∀ p ∈ closedRectangle l r a b,
        eta/2 ≤ heightEnergy g0 z p ∧
        nu/2 ≤ |covHessian g0 z p 0 0| ∧
        |covHessian g0 z p 0 0| ≤ A ∧
        (g0 p).det ≤ 2*G^2 ∧
        forcingFloor (eta/2) (2*G^2) A ≤ |forcingCoefficient g0 z p| := by
  obtain ⟨epsilon,A,hepsilon,hA,hmargin⟩ :=
    exists_uniform_Q_same_strip_margins G R M M0 hG hR hM hM0 hd hnu hc heta hkappa
  refine ⟨epsilon,A,hepsilon,hA,?_⟩
  intro g g0 z z0 U hg hg0 hU hz hz0 left right a b hab hbox hpoint
    hgB hg0B hzB hz0B hdet hdet0 hmetric hwidth hvalue hvelocity
    hxx hyy henergy hK hD htime l r hleft hright p hp
  have hp0 : p 0 ∈ Ioo left right :=
    ⟨hleft.trans_le hp.1.1, hp.1.2.trans_lt hright⟩
  have hpointEq : boxPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> simp [boxPoint]
  have hpbox : p ∈ closedRectangle left right a b :=
    ⟨⟨hp0.1.le,hp0.2.le⟩,hp.2⟩
  have hm := ((hmargin g g0 z z0 U hg hg0 hU hz hz0 left right a b hab hbox hpoint
    hgB hg0B hzB hz0B hdet hdet0 hmetric hwidth hvalue hvelocity
    hxx hyy henergy hK hD htime (p 0) hp0 (p 1) hp.2).1 1 (by norm_num))
  simp only [qHeightJetSegment,stateSegment_one,hpointEq,
    stateQDenominator_qSolutionJet] at hm
  have hE : eta/2 ≤ heightEnergy g0 z p := by
    have hs := hm.2.2.1
    unfold stateEnergy at hs
    rw [statePoint_qSolutionJet,stateGradient_qSolutionJet,
      jetEnergy_at_height hg0 (hbox hpbox) z] at hs
    exact hs
  have hentry (i j : Fin 2) : |g0 p i j| ≤ G := by
    have hh := hg0B i j 0 (by norm_num) p hpbox
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hh
  have hdetup := actual_det_upper_of_entry_bound g0 p hG hentry
  exact ⟨hE,hm.1,hm.2.1,hdetup,
    forcingCoefficient_floor_of_reference_margins hg0 (hbox hpbox)
      (half_pos heta) (half_pos hnu) hE hdetup hm.1 hm.2.1⟩

end SmoothLocal.HighEquation

end

end OAI
