import OAI.Geometry.IsometricImmersion.Flows.FlowThirdVariation

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def timeFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (Y p.2) p.1

def timeSecondFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => deriv (Y p.2) u) p.1

def mixedFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => timeFlowDerivative Y (p.1, u)) p.2

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_time_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (Y s) (-q (coordinatePoint t (Y s t))) t := by
  have hsmooth := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have htime : DifferentiableAt ℝ (Y s) t :=
    ((hsmooth.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨ht, hs⟩)).differentiableAt
      (by simp)).comp t (differentiableAt_id.prodMk (differentiableAt_const s))
  have hderiv := (hode s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  simpa only [hderiv.deriv] using htime.hasDerivAt

theorem timeFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    timeFlowDerivative Y (t, s) = -q (coordinatePoint t (Y s t)) :=
  (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem flowPullback_hasDerivAt_t {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => C (coordinatePoint u (Y s u)))
      (coordPartial 0 C (coordinatePoint t (Y s t)) -
        q (coordinatePoint t (Y s t)) * coordPartial 1 C (coordinatePoint t (Y s t))) t := by
  have hT : HasDerivAt (fun u => coordinatePoint u (Y s u))
      (Pi.single 0 (1 : ℝ) - q (coordinatePoint t (Y s t)) • Pi.single 1 (1 : ℝ) : Coord) t := by
    convert
      ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
        ((cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).smul_const
          (Pi.single 1 (1 : ℝ) : Coord)) using 1 <;>
      first | rfl | simp only [coordinatePoint, one_smul, neg_smul, sub_eq_add_neg]
  have hp := hSU (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩)
  have hC' := ((hC.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  convert hC'.comp_hasDerivAt t hT using 1 <;>
    first | rfl | simp only [map_sub, map_smul, smul_eq_mul, coordPartial, flowCoordinateMap]

theorem cap_flow_mixed_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeFlowDerivative Y (t, u))
      (-coordPartial 1 q (coordinatePoint t (Y s t)) * initialFlowDerivative Y (t, s)) s := by
  have hd := (flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hq hs ht).neg
  have he : (fun u => timeFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -q (coordinatePoint t (Y u t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem mixedFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    mixedFlowDerivative Y (t, s) =
      -coordPartial 1 q (coordinatePoint t (Y s t)) * initialFlowDerivative Y (t, s) :=
  (cap_flow_mixed_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem cap_flow_time_second_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeFlowDerivative Y (u, s))
      (-coordPartial 0 q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t))) t := by
  have hd := (flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode hq hs ht).neg
  have he : (fun u => timeFlowDerivative Y (u, s)) =ᶠ[𝓝 t]
      (fun u => -q (coordinatePoint u (Y s u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hs hu
  convert hd.congr_of_eventuallyEq he using 1
  first | rfl | ring

theorem timeSecondFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    timeSecondFlowDerivative Y (t, s) =
      -coordPartial 0 q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t)) :=
  (cap_flow_time_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem cap_flow_mixed_initial_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => mixedFlowDerivative Y (t, u))
      (-coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) *
          (initialFlowDerivative Y (t, s))^2 -
        coordPartial 1 q (coordinatePoint t (Y s t)) * initialSecondFlowDerivative Y (t, s)) s := by
  have hdq := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdV : HasDerivAt (fun u => initialFlowDerivative Y (t, u))
      (initialSecondFlowDerivative Y (t, s)) s :=
    (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt.hasDerivAt
  have hd := hdq.neg.mul hdV
  have he : (fun u => mixedFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -coordPartial 1 q (coordinatePoint t (Y u t)) * initialFlowDerivative Y (t, u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact mixedFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem cap_flow_time_second_initial_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeSecondFlowDerivative Y (t, u))
      ((-coordPartial 1 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t)) * q (coordinatePoint t (Y s t)) +
        (coordPartial 1 q (coordinatePoint t (Y s t)))^2) * initialFlowDerivative Y (t, s)) s := by
  have hd0 := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 0) hs ht
  have hd1 := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdq := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hq hs ht
  have hd := hd0.neg.add (hd1.mul hdq)
  have he : (fun u => timeSecondFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -coordPartial 0 q (coordinatePoint t (Y u t)) +
        coordPartial 1 q (coordinatePoint t (Y u t)) * q (coordinatePoint t (Y u t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hu ht
  convert hd.congr_of_eventuallyEq he using 1
  first | rfl | (dsimp [initialFlowDerivative]; ring)

theorem cap_flow_time_third_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => timeSecondFlowDerivative Y (u, s))
      (-coordPartial 0 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        q (coordinatePoint t (Y s t)) * coordPartial 1 (coordPartial 0 q) (coordinatePoint t (Y s t)) +
        (coordPartial 0 (coordPartial 1 q) (coordinatePoint t (Y s t)) -
          q (coordinatePoint t (Y s t)) * coordPartial 1 (coordPartial 1 q) (coordinatePoint t (Y s t))) *
          q (coordinatePoint t (Y s t)) +
        coordPartial 1 q (coordinatePoint t (Y s t)) *
          (coordPartial 0 q (coordinatePoint t (Y s t)) -
            q (coordinatePoint t (Y s t)) * coordPartial 1 q (coordinatePoint t (Y s t)))) t := by
  have hd0 := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 0) hs ht
  have hd1 := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1) hs ht
  have hdq := flowPullback_hasDerivAt_t hq hU hSU hY hrange hstart hode hq hs ht
  have hd := hd0.neg.add (hd1.mul hdq)
  have he : (fun u => timeSecondFlowDerivative Y (u, s)) =ᶠ[𝓝 t]
      (fun u => -coordPartial 0 q (coordinatePoint u (Y s u)) +
        coordPartial 1 q (coordinatePoint u (Y s u)) * q (coordinatePoint u (Y s u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact timeSecondFlowDerivative_eq hq hU hSU hY hrange hstart hode hs hu
  convert hd.congr_of_eventuallyEq he using 1
  first | rfl | ring

end ActualFlow
end SmoothLocal.Flow

end

end OAI
