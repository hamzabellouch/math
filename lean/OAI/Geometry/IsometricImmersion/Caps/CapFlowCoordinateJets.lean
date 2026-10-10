import OAI.Geometry.IsometricImmersion.Flows.FlowLowBounds
import OAI.Geometry.IsometricImmersion.Flows.FlowTransport
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem coordPartial_time_of_pair_eq {f : Coord → ℝ} {F : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f capChartDomain)
    (he : ∀ p ∈ capChartDomain, f p = F (p 0, p 1))
    {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 0 f p = deriv (fun t => F (t, p 1)) (p 0) := by
  have hd := ((hf.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hp' : boxPoint (p 0) (p 1) = p := boxPoint_coord_eta p
  have hd' : HasFDerivAt f (fderiv ℝ f p) (boxPoint (p 0) (p 1)) := by rw [hp']; exact hd
  have hline := hd'.comp_hasDerivAt (p 0) (boxPoint_hasDerivAt_t (p 0) (p 1))
  have hevent : (fun t => F (t, p 1)) =ᶠ[𝓝 (p 0)] (fun t => f (boxPoint t (p 1))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with t ht
    have hm : boxPoint t (p 1) ∈ capChartDomain := by
      simpa [capChartDomain, coordinateRectangle, boxPoint] using And.intro ht hp.2
    simpa [boxPoint] using (he (boxPoint t (p 1)) hm).symm
  exact (hline.congr_of_eventuallyEq hevent).deriv.symm

theorem coordPartial_initial_of_pair_eq {f : Coord → ℝ} {F : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f capChartDomain)
    (he : ∀ p ∈ capChartDomain, f p = F (p 0, p 1))
    {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 1 f p = deriv (fun s => F (p 0, s)) (p 1) := by
  have hd := ((hf.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hp' : boxPoint (p 0) (p 1) = p := boxPoint_coord_eta p
  have hd' : HasFDerivAt f (fderiv ℝ f p) (boxPoint (p 0) (p 1)) := by rw [hp']; exact hd
  have hline := hd'.comp_hasDerivAt (p 1) (boxPoint_hasDerivAt_s (p 0) (p 1))
  have hevent : (fun s => F (p 0, s)) =ᶠ[𝓝 (p 1)] (fun s => f (boxPoint (p 0) s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.2] with s hs
    have hm : boxPoint (p 0) s ∈ capChartDomain := by
      simpa [capChartDomain, coordinateRectangle, boxPoint] using And.intro hp.1 hs
    simpa [boxPoint] using (he (boxPoint (p 0) s) hm).symm
  exact (hline.congr_of_eventuallyEq hevent).deriv.symm

section HeightWords
variable {Y : ℝ → ℝ → ℝ}
variable (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
include hY

theorem capFlowHeight_partial_zero_eq {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 0 (capFlowHeight Y) p = timeFlowDerivative Y (p 0, p 1) :=
  (capFlowHeight_hasDerivAt_time hY hp).deriv.symm

theorem capFlowHeight_partial_one_eq {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 1 (capFlowHeight Y) p = initialFlowDerivative Y (p 0, p 1) :=
  (capFlowHeight_hasDerivAt_initial hY hp).deriv.symm

theorem capFlowHeight_word_00 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [0, 0] (capFlowHeight Y) p = timeSecondFlowDerivative Y (p 0, p 1) :=
  coordPartial_time_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 0)
    (fun _ hx => capFlowHeight_partial_zero_eq hY hx) hp

theorem capFlowHeight_word_10 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 0] (capFlowHeight Y) p = mixedFlowDerivative Y (p 0, p 1) :=
  coordPartial_initial_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 0)
    (fun _ hx => capFlowHeight_partial_zero_eq hY hx) hp

theorem capFlowHeight_word_11 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1] (capFlowHeight Y) p = initialSecondFlowDerivative Y (p 0, p 1) :=
  coordPartial_initial_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1)
    (fun _ hx => capFlowHeight_partial_one_eq hY hx) hp

theorem capFlowHeight_word_000 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [0, 0, 0] (capFlowHeight Y) p =
      deriv (fun t => timeSecondFlowDerivative Y (t, p 1)) (p 0) :=
  coordPartial_time_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [0, 0])
    (fun _ hx => capFlowHeight_word_00 hY hx) hp

theorem capFlowHeight_word_100 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 0, 0] (capFlowHeight Y) p =
      deriv (fun s => timeSecondFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [0, 0])
    (fun _ hx => capFlowHeight_word_00 hY hx) hp

theorem capFlowHeight_word_110 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1, 0] (capFlowHeight Y) p =
      deriv (fun s => mixedFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [1, 0])
    (fun _ hx => capFlowHeight_word_10 hY hx) hp

theorem capFlowHeight_word_111 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1, 1] (capFlowHeight Y) p =
      deriv (fun s => initialSecondFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [1, 1])
    (fun _ hx => capFlowHeight_word_11 hY hx) hp

end HeightWords

theorem iterated_three_swap_outer {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] f p = iteratedCoordPartial [j, i, k] f p :=
  coordPartial_comm (partial_contDiffOn hf hU k) hU hp i j

theorem iterated_three_swap_inner {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] f p = iteratedCoordPartial [i, k, j] f p := by
  have he : coordPartial j (coordPartial k f) =ᶠ[𝓝 p] coordPartial k (coordPartial j f) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact coordPartial_comm hf hU hx j k
  exact coordPartial_eq_of_eventuallyEq he i

end SmoothLocal.Flow

end

end OAI
