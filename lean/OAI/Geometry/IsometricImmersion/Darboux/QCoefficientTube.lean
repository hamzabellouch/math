import OAI.Geometry.IsometricImmersion.Darboux.QSegmentDomain
import OAI.Geometry.IsometricImmersion.Metrics.StateCoefficientTube

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem stateQDenominator_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateQDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 0 0)

def qCompactTube (g : MetricField) (S : Set Coord) (M c : ℝ) : Set DarbouxState :=
  stateBaseCompact S M ∩ (fun w => |stateQDenominator g w|) ⁻¹' Ici c

theorem qCompactTube_isCompact {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M c : ℝ) : IsCompact (qCompactTube g S M c) := by
  have hbase := stateBaseCompact_isCompact hS M
  have hc : ContinuousOn (fun w => |stateQDenominator g w|) (stateBaseCompact S M) :=
    (stateQDenominator_contDiffOn hg hU).continuousOn.abs.mono (fun w hw => hSU hw.1)
  have hclosed : IsClosed (qCompactTube g S M c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed isClosed_Ici
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem qCompactTube_subset_domain {g : MetricField} {U S : Set Coord}
    (hSU : S ⊆ U) (M : ℝ) {c : ℝ} (hc : 0 < c) :
    qCompactTube g S M c ⊆ darbouxQStateDomain g U := by
  intro w hw
  refine ⟨hSU hw.1.1, ?_⟩
  intro hz
  have hh : c ≤ |stateQDenominator g w| := hw.2
  rw [hz, abs_zero] at hh
  linarith

theorem qCompactTube_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) {f : DarbouxState → ℝ}
    (hf : ContDiffOn ℝ ∞ f (darbouxQStateDomain g U)) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c, ‖iteratedFDeriv ℝ k f w‖ ≤ C := by
  have hDo := darbouxQStateDomain_isOpen hg hU
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) (darbouxQStateDomain g U) := by
    apply (hf.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top)
      hDo.uniqueDiffOn).congr
    intro w hw
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hDo.uniqueDiffOn
      ((hf.contDiffAt (hDo.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)) hw).symm
  exact (qCompactTube_isCompact hg hU hS hSU M c).exists_bound_of_continuousOn
    (hcont.mono (qCompactTube_subset_domain hSU M hc))

theorem qCoefficient_uniform_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (i : Fin 6) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ k (qFirstCoefficient g i) w‖ ≤ C :=
  qCompactTube_derivative_bound hg hU hS hSU M hc (qFirstCoefficient_contDiffOn hg hU i) k

def qMarginObservable (g : MetricField) (w : DarbouxState) : Fin 3 → ℝ :=
  ![stateEnergy g w, qFirstCoefficient g 5 w,
    (qFirstCoefficient g 4 w / 2) ^ 2 + qFirstCoefficient g 5 w]

theorem qMarginObservable_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (qMarginObservable g) (darbouxQStateDomain g U) := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (stateEnergy_contDiffOn hg).mono (fun _ hw => hw.1)
  · exact qFirstCoefficient_contDiffOn hg hU 5
  · exact (((qFirstCoefficient_contDiffOn hg hU 4).div_const 2).pow 2).add
      (qFirstCoefficient_contDiffOn hg hU 5)

theorem qMarginObservable_uniform_fderiv_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ w ∈ qCompactTube g S M c,
      ‖fderiv ℝ (qMarginObservable g) w‖ ≤ L := by
  have hcont := (qMarginObservable_contDiffOn hg hU).continuousOn_fderiv_of_isOpen
    (darbouxQStateDomain_isOpen hg hU) (by simp)
  obtain ⟨C, hC⟩ := (qCompactTube_isCompact hg hU hS hSU M c).exists_bound_of_continuousOn
    (hcont.mono (qCompactTube_subset_domain hSU M hc))
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro w hw
  exact (hC w hw).trans (le_max_left _ _)

theorem stateSegment_mem_qCompactTube_of_error (g : MetricField) {S : Set Coord}
    {w0 w1 : DarbouxState} (hp : statePoint w0 = statePoint w1) (hS : statePoint w0 ∈ S)
    {sigma M B epsilon nu : ℝ} (hs : sigma ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ i : Fin 6, |w0 i| ≤ M) (h1 : ∀ i : Fin 6, |w1 i| ≤ M)
    (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hGamma : ∀ r : Fin 2, |christoffel g r 0 0 (statePoint w0)| ≤ B)
    (hjet : ∀ i : Fin 6, |w1 i - w0 i| ≤ epsilon)
    (hbase : nu ≤ |stateQDenominator g w0|)
    (hsmall : (1 + 2 * B) * epsilon ≤ nu / 2) :
    stateSegment w0 w1 sigma ∈ qCompactTube g S M (nu / 2) := by
  refine ⟨⟨?_, ?_⟩, stateQDenominator_segment_lower g hp hs hB heps hGamma hjet hbase hsmall⟩
  · change statePoint (stateSegment w0 w1 sigma) ∈ S
    rw [statePoint_segment hp]
    exact hS
  · constructor <;> intro i
    · exact (abs_le.mp (stateSegment_coord_bound hs h0 h1 i)).1
    · exact (abs_le.mp (stateSegment_coord_bound hs h0 h1 i)).2

theorem qHeightJetSegment_uniform_coefficient_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {nu : ℝ} (hnu : 0 < nu) (i : Fin 6) (k : ℕ) :
    ∃ C : ℝ, ∀ (z0 z : Coord → ℝ) (p : Coord), p ∈ S →
      (∀ j : Fin 6, |qSolutionJet z0 p j| ≤ M) →
      (∀ j : Fin 6, |qSolutionJet z p j| ≤ M) →
      ∀ B epsilon : ℝ, 0 ≤ B → 0 ≤ epsilon →
      (∀ r : Fin 2, |christoffel g r 0 0 p| ≤ B) →
      (∀ j : Fin 6, |qSolutionJet z p j - qSolutionJet z0 p j| ≤ epsilon) →
      nu ≤ |covHessian g z0 p 0 0| → (1 + 2 * B) * epsilon ≤ nu / 2 →
      ∀ sigma ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ k (qFirstCoefficient g i) (qHeightJetSegment z0 z sigma p)‖ ≤ C := by
  obtain ⟨C, hC⟩ := qCoefficient_uniform_derivative_bound hg hU hS hSU M (half_pos hnu) i k
  refine ⟨C, ?_⟩
  intro z0 z p hp h0 h1 B epsilon hB heps hGamma hjet hbase hsmall sigma hs
  apply hC
  apply stateSegment_mem_qCompactTube_of_error g
    (by simp only [statePoint_qSolutionJet]) (by simpa only [statePoint_qSolutionJet] using hp)
    hs h0 h1 hB heps
  · simpa only [statePoint_qSolutionJet] using hGamma
  · exact hjet
  · simpa only [stateQDenominator_qSolutionJet] using hbase
  · exact hsmall

end SmoothLocal.HighEquation

end

end OAI
