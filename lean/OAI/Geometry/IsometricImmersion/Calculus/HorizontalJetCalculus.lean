import OAI.Geometry.IsometricImmersion.Calculus.MovingFirstJetBase
import OAI.Geometry.IsometricImmersion.Calculus.VerticalSliceJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def horizontalJet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) : ℕ → Coord → V
  | 0 => f
  | n + 1 => coordPartial 0 (horizontalJet f n)

theorem horizontalJet_eq_spatialJet (f : Coord → ℝ) (n : ℕ) :
    horizontalJet f n = spatialJet f n := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [horizontalJet, spatialJet, hn]

theorem horizontalJet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ n, ContDiffOn ℝ ∞ (horizontalJet f n) U := by
  intro n
  induction n with
  | zero => exact hf
  | succ _ hn => exact normed_coordPartial_contDiffOn hn hU 0

theorem horizontalPoint_contDiff (y : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => coordinatePoint x y) := by
  unfold coordinatePoint
  fun_prop

theorem horizontalJet_slice_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ)
    (hp : coordinatePoint x y ∈ U) :
    HasDerivAt (fun t => horizontalJet f n (coordinatePoint t y))
      (horizontalJet f (n + 1) (coordinatePoint x y)) x := by
  have hd : DifferentiableAt ℝ (horizontalJet f n) (coordinatePoint x y) :=
    ((horizontalJet_contDiffOn hU hf n).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt x (point_hasDerivAt_t x y)

theorem horizontalJet_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (y : ℝ) : ∀ n x, coordinatePoint x y ∈ U →
      iteratedDeriv n (fun t => f (coordinatePoint t y)) x =
        horizontalJet f n (coordinatePoint x y) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n hn =>
    intro x hx
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t => f (coordinatePoint t y)) =ᶠ[𝓝 x]
        (fun t => horizontalJet f n (coordinatePoint t y)) := by
      filter_upwards [(hU.preimage (horizontalPoint_contDiff y).continuous).mem_nhds hx] with t ht
      exact hn t ht
    rw [heq.deriv_eq]
    exact (horizontalJet_slice_hasDerivAt hU hf n hx).deriv

theorem horizontalJet_coordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin 2) : ∀ n p, p ∈ U →
      horizontalJet (coordPartial i f) n p = coordPartial i (horizontalJet f n) p := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n hn =>
    intro p hp
    have heq : horizontalJet (coordPartial i f) n =ᶠ[𝓝 p] coordPartial i (horizontalJet f n) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hn q hq
    have hd : coordPartial 0 (horizontalJet (coordPartial i f) n) p =
        coordPartial 0 (coordPartial i (horizontalJet f n)) p :=
      congrArg (fun L : Coord →L[ℝ] V => L (Pi.single 0 1)) heq.fderiv_eq
    change coordPartial 0 (horizontalJet (coordPartial i f) n) p =
      coordPartial i (coordPartial 0 (horizontalJet f n)) p
    rw [hd]
    exact coordPartial_comm (horizontalJet_contDiffOn hU hf n) hU hp 0 i

theorem horizontalJet_two_coordPartials
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : p ∈ U) (n : ℕ) (i j : Fin 2) :
    horizontalJet (coordPartial i (coordPartial j f)) n p =
      coordPartial i (coordPartial j (horizontalJet f n)) p := by
  rw [horizontalJet_coordPartial hU (normed_coordPartial_contDiffOn hf hU j) i n p hp]
  have heq : horizontalJet (coordPartial j f) n =ᶠ[𝓝 p] coordPartial j (horizontalJet f n) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact horizontalJet_coordPartial hU hf j n q hq
  exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single i 1)) heq.fderiv_eq

end SmoothLocal.HighEquation

end

end OAI
