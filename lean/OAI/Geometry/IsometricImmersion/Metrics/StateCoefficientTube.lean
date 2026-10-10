import OAI.Geometry.IsometricImmersion.Calculus.StateJetSegment
import OAI.Geometry.IsometricImmersion.Darboux.SixVariableLinearization
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateFirstCoefficient (g : MetricField) (i : Fin 6) (w : DarbouxState) : ℝ :=
  fderiv ℝ (sixVariableP g) w (Pi.single i 1)

theorem stateFirstCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (stateFirstCoefficient g i) (darbouxStateDomain g U) :=
  ((sixVariableP_contDiffOn hg hU).fderiv_of_isOpen
    (darbouxStateDomain_isOpen hg hU) (by simp)).clm_apply contDiffOn_const

theorem stateFirstCoefficient_mixed {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxStateDomain g U) :
    stateFirstCoefficient g 4 w = 2 * (stateMixed g w / stateDenominator g w) := by
  have hd : DifferentiableAt ℝ (sixVariableP g) w :=
    ((sixVariableP_contDiffOn hg hU).contDiffAt
      ((darbouxStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  unfold stateFirstCoefficient
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableP g (Function.update w 4 t)) =
      (fun t => solvedDarboux g (statePoint w) t (w 5) (stateGradient w)) :=
    funext (sixVariableP_update_mixed g w)
  rw [heq, solvedDarboux_deriv_b g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

theorem stateFirstCoefficient_yy {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxStateDomain g U) :
    stateFirstCoefficient g 5 w =
      -((stateMixed g w / stateDenominator g w) ^ 2 +
        gaussianCurvature g (statePoint w) * stateEnergy g w / (stateDenominator g w) ^ 2) := by
  have hd : DifferentiableAt ℝ (sixVariableP g) w :=
    ((sixVariableP_contDiffOn hg hU).contDiffAt
      ((darbouxStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  unfold stateFirstCoefficient
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableP g (Function.update w 5 t)) =
      (fun t => solvedDarboux g (statePoint w) (w 4) t (stateGradient w)) :=
    funext (sixVariableP_update_yy g w)
  rw [heq, solvedDarboux_deriv_c g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

theorem stateFirstCoefficient_gradient {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxStateDomain g U) (i : Fin 2) :
    stateFirstCoefficient g (gradientStateIndex i) w =
      christoffelAlongD g (statePoint w) (stateMixed g w / stateDenominator g w) i +
        gaussianCurvature g (statePoint w) *
          (coordPartial i (jetEnergy g (statePoint w)) (stateGradient w) / stateDenominator g w +
            stateEnergy g w * christoffel g i 1 1 (statePoint w) / (stateDenominator g w)^2) := by
  rw [stateFirstCoefficient, sixVariableP_gradient_axis hg hU hw i]
  exact solvedDarboux_firstJet hg hU hw.1 (stateGradient w) (w 4) (w 5) hw.2 i

def stateBaseCompact (S : Set Coord) (M : ℝ) : Set DarbouxState :=
  (statePoint ⁻¹' S) ∩ Icc (fun _ => -M) (fun _ => M)

def stateCompactTube (g : MetricField) (S : Set Coord) (M c : ℝ) : Set DarbouxState :=
  stateBaseCompact S M ∩ (fun w => |stateDenominator g w|) ⁻¹' Ici c

theorem stateBaseCompact_isCompact {S : Set Coord} (hS : IsCompact S) (M : ℝ) :
    IsCompact (stateBaseCompact S M) :=
  isCompact_Icc.inter_left (hS.isClosed.preimage statePoint_contDiff.continuous)

theorem stateCompactTube_isCompact {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M c : ℝ) : IsCompact (stateCompactTube g S M c) := by
  have hbase := stateBaseCompact_isCompact hS M
  have hc : ContinuousOn (fun w => |stateDenominator g w|) (stateBaseCompact S M) :=
    (stateDenominator_contDiffOn hg hU).continuousOn.abs.mono (fun w hw => hSU hw.1)
  have hclosed : IsClosed (stateCompactTube g S M c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed isClosed_Ici
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem stateCompactTube_subset_domain {g : MetricField} {U S : Set Coord}
    (hSU : S ⊆ U) (M : ℝ) {c : ℝ} (hc : 0 < c) :
    stateCompactTube g S M c ⊆ darbouxStateDomain g U := by
  intro w hw
  refine ⟨hSU hw.1.1, ?_⟩
  intro hz
  have hh : c ≤ |stateDenominator g w| := hw.2
  rw [hz, abs_zero] at hh
  linarith

theorem stateCompactTube_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) {f : DarbouxState → ℝ}
    (hf : ContDiffOn ℝ ∞ f (darbouxStateDomain g U)) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ stateCompactTube g S M c, ‖iteratedFDeriv ℝ k f w‖ ≤ C := by
  have hDo := darbouxStateDomain_isOpen hg hU
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) (darbouxStateDomain g U) := by
    apply (hf.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top)
      hDo.uniqueDiffOn).congr
    intro w hw
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hDo.uniqueDiffOn
      ((hf.contDiffAt (hDo.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)) hw).symm
  exact (stateCompactTube_isCompact hg hU hS hSU M c).exists_bound_of_continuousOn
    (hcont.mono (stateCompactTube_subset_domain hSU M hc))

theorem stateFirstCoefficient_uniform_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (i : Fin 6) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ stateCompactTube g S M c,
      ‖iteratedFDeriv ℝ k (stateFirstCoefficient g i) w‖ ≤ C :=
  stateCompactTube_derivative_bound hg hU hS hSU M hc
    (stateFirstCoefficient_contDiffOn hg hU i) k

theorem stateSegment_coord_bound {w0 w1 : DarbouxState} {sigma M : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ i, |w0 i| ≤ M) (h1 : ∀ i, |w1 i| ≤ M) (i : Fin 6) :
    |stateSegment w0 w1 sigma i| ≤ M := by
  change |(1 - sigma) * w0 i + sigma * w1 i| ≤ M
  calc
    _ ≤ |(1 - sigma) * w0 i| + |sigma * w1 i| := abs_add_le _ _
    _ = (1 - sigma) * |w0 i| + sigma * |w1 i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
    _ ≤ (1 - sigma) * M + sigma * M :=
      add_le_add (mul_le_mul_of_nonneg_left (h0 i) (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left (h1 i) hs.1)
    _ = M := by ring

theorem heightJetSegment_mem_compactTube (g : MetricField) (z0 z : Coord → ℝ)
    {S : Set Coord} {p : Coord} (hp : p ∈ S) {sigma M c : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ i, |solutionJet z0 p i| ≤ M) (h1 : ∀ i, |solutionJet z p i| ≤ M)
    (hden : c ≤ |stateDenominator g (heightJetSegment z0 z sigma p)|) :
    heightJetSegment z0 z sigma p ∈ stateCompactTube g S M c := by
  refine ⟨⟨?_, ?_⟩, hden⟩
  · simpa only [Set.mem_preimage, statePoint_heightJetSegment] using hp
  · constructor <;> intro i
    · exact (abs_le.mp (stateSegment_coord_bound hs h0 h1 i)).1
    · exact (abs_le.mp (stateSegment_coord_bound hs h0 h1 i)).2

end SmoothLocal.HighEquation

end

end OAI
