import OAI.Geometry.IsometricImmersion.Darboux.QStripJetControl

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem qSolutionJet_norm_bound_of_words {z : Coord → ℝ} {p : Coord} {R Z : ℝ}
    (hR : 0 ≤ R) (hpB : ‖p‖ ≤ R)
    (hjet : ∀ ds : List (Fin 2), ds.length ≤ 2 → |iteratedCoordPartial ds z p| ≤ Z) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  have hcoord (i : Fin 2) : |p i| ≤ R := (norm_le_pi_norm p i).trans hpB
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  fin_cases i
  · exact (hcoord 0).trans (le_max_left _ _)
  · exact (hcoord 1).trans (le_max_left _ _)
  · exact (hjet [0] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 0] (by norm_num)).trans (le_max_right _ _)

theorem exists_uniform_Q_same_strip_margins (G R M M0 : ℝ)
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
      ∀ x ∈ Ioo left right, ∀ t ∈ Icc a b,
      (∀ sigma ∈ Icc (0 : ℝ) 1,
        nu / 2 ≤ |stateQDenominator g0 (qHeightJetSegment z0 z sigma (boxPoint x t))| ∧
        |stateQDenominator g0 (qHeightJetSegment z0 z sigma (boxPoint x t))| ≤ A ∧
        eta / 2 ≤ stateEnergy g0 (qHeightJetSegment z0 z sigma (boxPoint x t)) ∧
        ((nu * c) / 2) / A^2 ≤ qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma (boxPoint x t)) ∧
        ((kappa / 2) * (eta / 2)) / A^2 ≤
          (qFirstCoefficient g0 4 (qHeightJetSegment z0 z sigma (boxPoint x t)) / 2)^2 +
            qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma (boxPoint x t))) ∧
      ((nu * c) / 2) / A^2 ≤
        averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 5 ∧
      ((nu * c) / 2) / A^2 ≤
        (averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 4 / 2)^2 +
          averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 5 := by
  let W := max R (max M M0)
  obtain ⟨epsilon, A, hepsilon, hA, htransfer⟩ :=
    exists_uniform_Q_metric_state_margins G W hG hd hnu heta (mul_pos hnu hc) hkappa
  refine ⟨epsilon, A, hepsilon, hA, ?_⟩
  intro g g0 z z0 U hg hg0 hU hz hz0 left right a b hab hbox hpoint
    hgB hg0B hzB hz0B hdet hdet0 hmetric hwidth hvalue hvelocity
    hxx hyy henergy hK hD htime x hx t ht
  have hpbox : boxPoint x t ∈ closedRectangle left right a b :=
    boxPoint_mem ⟨hx.1.le, hx.2.le⟩ ht
  have hp : boxPoint x t ∈ U := hbox hpbox
  have hwB : ‖qSolutionJet z (boxPoint x t)‖ ≤ W := by
    apply qSolutionJet_norm_bound_of_words hR (hpoint _ hpbox)
    intro ds hds
    exact (hzB ds (hds.trans (Nat.le_succ 2)) _ hpbox).trans (le_max_left _ _)
  have hw0B : ‖qSolutionJet z0 (boxPoint x t)‖ ≤ W := by
    apply qSolutionJet_norm_bound_of_words hR (hpoint _ hpbox)
    intro ds hds
    exact (hz0B ds (hds.trans (Nat.le_succ 2)) _ hpbox).trans (le_max_right _ _)
  have hjet : ‖qSolutionJet z0 (boxPoint x t) - qSolutionJet z (boxPoint x t)‖ ≤ epsilon :=
    (qSolutionJet_distance_on_same_strip hz hz0 hU hbox hx hab ht hM hM0
      hzB hz0B hvalue hvelocity).trans hwidth
  have hnum := stateNumerator_negative_of_solution_floors hg hU hz hp
    (hD _ hpbox) hnu hc (hxx _ hpbox) (hyy _ hpbox) (htime _ hpbox)
  have hstateE : eta ≤ stateEnergy g (qSolutionJet z (boxPoint x t)) := by
    unfold stateEnergy
    rw [statePoint_qSolutionJet, stateGradient_qSolutionJet, jetEnergy_at_height hg hp z]
    exact henergy _ hpbox
  have hsegment (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :=
    htransfer g g0 U hg hg0 hU (qSolutionJet z (boxPoint x t))
      (qHeightJetSegment z0 z sigma (boxPoint x t))
      (by rw [statePoint_qSolutionJet, statePoint_qHeightJetSegment])
      (by simpa only [statePoint_qSolutionJet] using hp)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hgB i j k hk _ hpbox)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hg0B i j k hk _ hpbox)
      hwB (stateSegment_norm_le hw0B hwB hs)
      (by simpa only [statePoint_qSolutionJet] using hdet _ hpbox)
      (by simpa only [statePoint_qSolutionJet] using hdet0 _ hpbox)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hmetric i j k hk _ hpbox)
      ((stateSegment_sub_right_norm_le hs).trans hjet)
      (by simpa only [stateQDenominator_qSolutionJet] using hxx _ hpbox) hstateE hnum
      (by simpa only [statePoint_qSolutionJet] using hK _ hpbox)
  refine ⟨hsegment, ?_⟩
  apply averagedQPrincipal_margin hg0 hU
  · intro sigma hs
    refine ⟨?_, ?_⟩
    · change statePoint (qHeightJetSegment z0 z sigma (boxPoint x t)) ∈ U
      rw [statePoint_qHeightJetSegment]
      exact hp
    · have hm := (hsegment sigma hs).1
      exact abs_pos.mp ((half_pos hnu).trans_le hm)
  · intro sigma hs
    exact (hsegment sigma hs).2.2.2.1

end SmoothLocal.HighEquation

end

end OAI
