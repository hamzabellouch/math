import OAI.Geometry.IsometricImmersion.Taylor.UniformTaylorPolynomial
import OAI.Geometry.IsometricImmersion.Darboux.QActualSegmentTransfer
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem stateBaseCompact_mem_of_norm {w : DarbouxState} {S : Set Coord} {M : ℝ}
    (hp : statePoint w ∈ S) (hw : ‖w‖ ≤ M) : w ∈ stateBaseCompact S M := by
  refine ⟨hp, ?_⟩
  constructor <;> intro i
  · exact (abs_le.mp ((norm_le_pi_norm w i).trans hw)).1
  · exact (abs_le.mp ((norm_le_pi_norm w i).trans hw)).2

theorem stateQDenominator_uniform_fderiv_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w ∈ stateBaseCompact S M, ‖fderiv ℝ (stateQDenominator g) w‖ ≤ L := by
  have hf := (stateQDenominator_contDiffOn hg hU).continuousOn_fderiv_of_isOpen
    (stateBaseDomain_isOpen hU) (by simp)
  obtain ⟨L, hL⟩ := (stateBaseCompact_isCompact hS M).exists_bound_of_continuousOn
    (hf.mono (fun _ hw => hSU hw.1))
  exact ⟨max L 0, le_max_right _ _, fun w hw => (hL w hw).trans (le_max_left _ _)⟩

theorem qHessian_time_hasDerivAt {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {x t : ℝ} (hx : x ∈ I) (hp : (![x, t] : Coord) ∈ U) :
    HasDerivAt (fun s => covHessian g P ![x, s] 0 0)
      (fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, t])
        (fderiv ℝ (qSolutionJet P) ![x, t] (Pi.single 1 1))) t := by
  have hf : DifferentiableAt ℝ (qSolutionJet P) ![x, t] :=
    ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hx)).differentiableAt (by simp)
  have hd := ((stateQDenominator_contDiffOn hg hU).contDiffAt
    ((stateBaseDomain_isOpen hU).mem_nhds
      (show qSolutionJet P ![x, t] ∈ stateBaseDomain U by
        change statePoint (qSolutionJet P ![x, t]) ∈ U
        rw [statePoint_qSolutionJet]
        exact hp))).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt t
    (hf.hasFDerivAt.comp_hasDerivAt t (verticalPoint_hasDerivAt x t))
  change HasDerivAt (fun s => stateQDenominator g (qSolutionJet P ![x, s]))
    (fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, t])
      (fderiv ℝ (qSolutionJet P) ![x, t] (Pi.single 1 1))) t at hc
  simp_rw [stateQDenominator_qSolutionJet] at hc
  exact hc

theorem exists_uniform_Hxx_time_variation {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a t x : ℝ, a ≤ t → x ∈ I →
      (∀ s ∈ Icc a t, (![x, s] : Coord) ∈ S) →
      (∀ s ∈ Icc a t, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j P ![x, s]‖ ≤ R) →
      |covHessian g P ![x, t] 0 0 - covHessian g P ![x, a] 0 0| ≤ L * |t - a| := by
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun p : Coord => p) S)
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hpoint : ∀ p ∈ S, ‖p‖ ≤ A0 := fun p hp => (hA p hp).trans (le_max_left _ _)
  obtain ⟨L, hL, hder⟩ := stateQDenominator_uniform_fderiv_bound hg hU hS hSU (max A0 R)
  refine ⟨L * max 1 R, mul_nonneg hL (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro P I hI hP a t x hat hx hseg hPB
  have hd (s : ℝ) (hs : s ∈ Icc a t) := qHessian_time_hasDerivAt hg hU hI hP hx (hSU (hseg s hs))
  have hbound (s : ℝ) (hs : s ∈ Icc a t) :
      ‖deriv (fun v => covHessian g P ![x, v] 0 0) s‖ ≤ L * max 1 R := by
    rw [(hd s hs).deriv]
    have hstate := qSolutionJet_norm_bound hP (spatialStrip_isOpen hI) hx hA0 hR
      (hpoint _ (hseg s hs)) (fun j hj => hPB s hs j (by omega))
    have houter := hder (qSolutionJet P ![x, s])
      (stateBaseCompact_mem_of_norm (by simpa only [statePoint_qSolutionJet] using hseg s hs) hstate)
    have hinner : ‖fderiv ℝ (qSolutionJet P) ![x, s]‖ ≤ max 1 R := by
      simpa only [norm_iteratedFDeriv_one] using
        qSolutionJet_positive_fullJet_bound hP (spatialStrip_isOpen hI) hx
          (show 1 ≤ (1 : ℕ) by omega) (fun j hj => hPB s hs j hj)
    have hv : ‖fderiv ℝ (qSolutionJet P) ![x, s] (Pi.single 1 1)‖ ≤ max 1 R := by
      have hv0 : ‖fderiv ℝ (qSolutionJet P) ![x, s] (Pi.single 1 1)‖ ≤
          ‖fderiv ℝ (qSolutionJet P) ![x, s]‖ * ‖(Pi.single 1 1 : Coord)‖ :=
        (fderiv ℝ (qSolutionJet P) ![x, s]).le_opNorm (Pi.single 1 1)
      rw [Pi.norm_single, norm_one, mul_one] at hv0
      exact hv0.trans hinner
    exact ((fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, s])).le_opNorm _).trans
      (mul_le_mul houter hv (norm_nonneg _) hL)
  have hv := (convex_Icc a t).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hd s hs).differentiableAt) hbound
    (show a ∈ Icc a t from ⟨le_rfl, hat⟩) (show t ∈ Icc a t from ⟨hat, le_rfl⟩)
  simpa only [Real.norm_eq_abs] using hv

theorem exists_uniform_Hxx_strip_width {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) {c : ℝ} (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a t x : ℝ,
      a ≤ t → t - a ≤ epsilon → x ∈ I →
      (∀ s ∈ Icc a t, (![x, s] : Coord) ∈ S) →
      (∀ s ∈ Icc a t, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j P ![x, s]‖ ≤ R) →
      c ≤ |covHessian g P ![x, a] 0 0| → c / 2 ≤ |covHessian g P ![x, t] 0 0| := by
  obtain ⟨L, hL, hvar⟩ := exists_uniform_Hxx_time_variation hg hU hS hSU R hR
  let epsilon := min 1 (c / (2 * (L + 1)))
  have he : 0 < epsilon := lt_min zero_lt_one (div_pos hc (by positivity))
  have hsmall : L * epsilon ≤ c / 2 := by
    have heupper : epsilon ≤ c / (2 * (L + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (L + 1))).mp heupper
    nlinarith [he.le]
  refine ⟨epsilon, he, min_le_left _ _, ?_⟩
  intro P I hI hP a t x hat htime hx hseg hPB hden
  have hv := hvar P I hI hP a t x hat hx hseg hPB
  rw [abs_of_nonneg (sub_nonneg.mpr hat)] at hv
  have hv' := hv.trans ((mul_le_mul_of_nonneg_left htime hL).trans hsmall)
  rw [abs_sub_comm] at hv'
  have htri : |covHessian g P ![x, a] 0 0| ≤
      |covHessian g P ![x, a] 0 0 - covHessian g P ![x, t] 0 0| +
        |covHessian g P ![x, t] 0 0| := by
    simpa only [sub_add_cancel] using abs_add_le
      (covHessian g P ![x, a] 0 0 - covHessian g P ![x, t] 0 0)
      (covHessian g P ![x, t] 0 0)
  linarith

end SmoothLocal.Taylor

end

end OAI
