import OAI.Geometry.IsometricImmersion.Taylor.TaylorResidual
import OAI.Geometry.IsometricImmersion.Darboux.QCoefficientTube
import OAI.Geometry.IsometricImmersion.Metrics.MetricPBundleBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem coordinateProjection_norm_le (i : Fin 2) :
    ‖(ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p i‖ ≤ 1 * ‖p‖
  rw [one_mul]
  exact norm_le_pi_norm p i

theorem coordinateProjection_positive_jet_bound (i : Fin 2) (p : Coord)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun q : Coord => q i) p‖ ≤ 1 := by
  let L : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := L.norm_iteratedFDeriv_comp_left
    (f := fun q : Coord => q) (x := p) contDiffAt_id (n := n) (WithTop.coe_le_coe.mpr le_top)
  have hL : ‖L‖ ≤ 1 := coordinateProjection_norm_le i
  exact h.trans ((mul_le_mul hL (norm_iteratedFDeriv_id_pos p hn)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem qSolutionJet_positive_fullJet_bound {P : Coord → ℝ} {V : Set Coord}
    (hP : ContDiffOn ℝ ∞ P V) (hV : IsOpen V) {p : Coord} (hp : p ∈ V)
    {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hB : ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (qSolutionJet P) p‖ ≤ max 1 B := by
  apply norm_iteratedFDeriv_pi_le
    ((qSolutionJet_contDiffOn hV hP).contDiffAt (hV.mem_nhds hp)) n
    (zero_le_one.trans (le_max_left _ _))
  intro i
  fin_cases i
  · exact (coordinateProjection_positive_jet_bound 0 p hn).trans (le_max_left _ _)
  · exact (coordinateProjection_positive_jet_bound 1 p hn).trans (le_max_left _ _)
  · exact ((norm_iteratedFDeriv_coordPartial_le hP hV hp 0 n).trans
      (hB (n + 1) (by omega))).trans (le_max_right _ _)
  · exact ((norm_iteratedFDeriv_coordPartial_le hP hV hp 1 n).trans
      (hB (n + 1) (by omega))).trans (le_max_right _ _)
  · exact (((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP hV 1) hV hp 0 n).trans
      (norm_iteratedFDeriv_coordPartial_le hP hV hp 1 (n + 1))).trans
        (hB (n + 1 + 1) (by omega))).trans (le_max_right _ _)
  · exact (((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP hV 0) hV hp 0 n).trans
      (norm_iteratedFDeriv_coordPartial_le hP hV hp 0 (n + 1))).trans
        (hB (n + 1 + 1) (by omega))).trans (le_max_right _ _)

theorem qCompactTube_finite_Q_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ C := by
  classical
  have hh : ∀ j : Fin (N + 1), ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ j.val (sixVariableQ g) w‖ ≤ C :=
    fun j => qCompactTube_derivative_bound hg hU hS hSU M hc
      (sixVariableQ_contDiffOn hg hU) j.val
  choose A hA using hh
  refine ⟨∑ j : Fin (N + 1), |A j|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro n hn w hw
  let j : Fin (N + 1) := ⟨n, by omega⟩
  exact (hA j w hw).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

theorem qSolutionJet_mem_qCompactTube {g : MetricField} {P : Coord → ℝ}
    {S : Set Coord} {p : Coord} (hp : p ∈ S) {M c : ℝ}
    (_hM : 0 ≤ M) (hstate : ‖qSolutionJet P p‖ ≤ M)
    (hden : c ≤ |covHessian g P p 0 0|) :
    qSolutionJet P p ∈ qCompactTube g S M c := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change statePoint (qSolutionJet P p) ∈ S
    rw [statePoint_qSolutionJet]
    exact hp
  · constructor <;> intro i
    · exact (abs_le.mp ((norm_le_pi_norm (qSolutionJet P p) i).trans hstate)).1
    · exact (abs_le.mp ((norm_le_pi_norm (qSolutionJet P p) i).trans hstate)).2
  · change c ≤ |stateQDenominator g (qSolutionJet P p)|
    rw [stateQDenominator_qSolutionJet]
    exact hden

theorem Q_height_composition_fullJet_bound {g : MetricField} {U S : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {p : Coord} (hpI : p ∈ spatialStrip I) (hpS : p ∈ S) (hSU : S ⊆ U)
    {M c B C : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (hstate : ‖qSolutionJet P p‖ ≤ M)
    (hden : c ≤ |covHessian g P p 0 0|) (n : ℕ)
    (hB : ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B)
    (hC : ∀ j ≤ n, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ j (sixVariableQ g) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun q => sixVariableQ g (qSolutionJet P q)) p‖ ≤
      (n.factorial : ℝ) * C * (max 1 B)^n := by
  have hxx : covHessian g P p 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  have hpD := mem_comparisonDomain hpI (hSU hpS) hxx
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hQ := sixVariableQ_contDiffOn hg hU
  have hQD := darbouxQStateDomain_isOpen hg hU
  have hinput := (qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).mono
    (show comparisonDomain g U P I ⊆ spatialStrip I from inter_subset_left)
  have hmap : MapsTo (qSolutionJet P) (comparisonDomain g U P I) (darbouxQStateDomain g U) :=
    fun _ hq => hq.2
  have houter : ∀ j, j ≤ n →
      ‖iteratedFDerivWithin ℝ j (sixVariableQ g) (darbouxQStateDomain g U) (qSolutionJet P p)‖ ≤ C := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hQD (hmap hpD)]
    exact hC j hj _ (qSolutionJet_mem_qCompactTube hpS hM hstate hden)
  have hinner : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDerivWithin ℝ j (qSolutionJet P) (comparisonDomain g U P I) p‖ ≤ (max 1 B)^j := by
    intro j hj hjn
    rw [iteratedFDerivWithin_of_isOpen j hD hpD]
    exact (qSolutionJet_positive_fullJet_bound hP (spatialStrip_isOpen hI) hpI hj
      (fun k hk => hB k (by omega))).trans (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le hQ hinput
    (WithTop.coe_le_coe.mpr le_top) hQD.uniqueDiffOn hD.uniqueDiffOn hmap hpD houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hD hpD] at hcomp
  exact hcomp

theorem exists_uniform_qResidual_fullJet_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ p : Coord, p ∈ spatialStrip I → p ∈ S →
      ‖qSolutionJet P p‖ ≤ M → c ≤ |covHessian g P p 0 0| →
      ∀ (n : ℕ), n ≤ N → ∀ B : ℝ,
      (∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (qResidual g P) p‖ ≤
        B + (n.factorial : ℝ) * C * (max 1 B)^n := by
  obtain ⟨C, hC, hCQ⟩ := qCompactTube_finite_Q_bound hg hU hS hSU M hc N
  refine ⟨C, hC, ?_⟩
  intro P I hI hP p hpI hpS hstate hden n hn B hB
  have hxx : covHessian g P p 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  have htt := (partial_contDiffOn (partial_contDiffOn hP (spatialStrip_isOpen hI) 1)
    (spatialStrip_isOpen hI) 1).contDiffAt ((spatialStrip_isOpen hI).mem_nhds hpI)
  have hQc := (sixVariableQ_contDiffAt_solutionJet hg hU (hSU hpS) hxx).comp p
    ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
      ((spatialStrip_isOpen hI).mem_nhds hpI))
  have hsecond : ‖iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 P)) p‖ ≤ B :=
    ((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP (spatialStrip_isOpen hI) 1)
      (spatialStrip_isOpen hI) hpI 1 n).trans
        (norm_iteratedFDeriv_coordPartial_le hP (spatialStrip_isOpen hI) hpI 1 (n + 1))).trans
          (hB (n + 1 + 1) (by omega))
  have hQbound := Q_height_composition_fullJet_bound hg hU hI hP hpI hpS hSU hM hc
    hstate hden n hB (fun j hj => hCQ j (hj.trans hn))
  change ‖iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 P) -
    (sixVariableQ g ∘ qSolutionJet P)) p‖ ≤ _
  rw [iteratedFDeriv_sub_apply (htt.of_le (WithTop.coe_le_coe.mpr le_top))
    (hQc.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hsecond hQbound)

end SmoothLocal.Taylor

end

end OAI
