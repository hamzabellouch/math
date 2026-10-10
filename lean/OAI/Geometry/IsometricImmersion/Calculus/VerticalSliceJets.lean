import OAI.Geometry.IsometricImmersion.Taylor.ActualDarbouxFaa
import OAI.Geometry.IsometricImmersion.Calculus.NormedCoordinateCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def verticalJet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) : ℕ → Coord → V
  | 0 => f
  | n + 1 => coordPartial 1 (verticalJet f n)

theorem verticalJet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ n, ContDiffOn ℝ ∞ (verticalJet f n) U := by
  intro n
  induction n with
  | zero => exact hf
  | succ n hn => exact normed_coordPartial_contDiffOn hn hU 1

theorem verticalPoint_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (![x, t] : Coord)) (Pi.single 1 (1 : ℝ)) y := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasDerivAt_const y x
  · convert hasDerivAt_id y using 1 <;> rfl

theorem verticalJet_slice_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ)
    (hp : (![x, y] : Coord) ∈ U) :
    HasDerivAt (fun t => verticalJet f n ![x, t]) (verticalJet f (n + 1) ![x, y]) y := by
  have hd : DifferentiableAt ℝ (verticalJet f n) ![x, y] :=
    (((verticalJet_contDiffOn hU hf n).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  exact hd.hasFDerivAt.comp_hasDerivAt y (verticalPoint_hasDerivAt x y)

theorem verticalJet_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (x : ℝ) : ∀ n y, (![x, y] : Coord) ∈ U →
      iteratedDeriv n (fun t => f ![x, t]) y = verticalJet f n ![x, y] := by
  intro n
  induction n with
  | zero => intro y hy; rfl
  | succ n hn =>
    intro y hy
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t => f ![x, t]) =ᶠ[𝓝 y]
        (fun t => verticalJet f n ![x, t]) := by
      filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hy] with t ht
      exact hn t ht
    rw [heq.deriv_eq]
    exact (verticalJet_slice_hasDerivAt hU hf n hy).deriv

theorem verticalJet_coordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin 2) : ∀ n p, p ∈ U →
      verticalJet (coordPartial i f) n p = coordPartial i (verticalJet f n) p := by
  intro n
  induction n with
  | zero => intro p hp; rfl
  | succ n hn =>
    intro p hp
    have heq : verticalJet (coordPartial i f) n =ᶠ[𝓝 p] coordPartial i (verticalJet f n) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hn q hq
    have hd : coordPartial 1 (verticalJet (coordPartial i f) n) p =
        coordPartial 1 (coordPartial i (verticalJet f n)) p := by
      exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single 1 1)) heq.fderiv_eq
    change coordPartial 1 (verticalJet (coordPartial i f) n) p =
      coordPartial i (coordPartial 1 (verticalJet f n)) p
    rw [hd]
    exact coordPartial_comm (verticalJet_contDiffOn hU hf n) hU hp 1 i

theorem verticalJet_two_coordPartials
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : p ∈ U) (n : ℕ) (i j : Fin 2) :
    verticalJet (coordPartial i (coordPartial j f)) n p =
      coordPartial i (coordPartial j (verticalJet f n)) p := by
  rw [verticalJet_coordPartial hU (normed_coordPartial_contDiffOn hf hU j) i n p hp]
  have heq : verticalJet (coordPartial j f) n =ᶠ[𝓝 p] coordPartial j (verticalJet f n) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact verticalJet_coordPartial hU hf j n q hq
  exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single i 1)) heq.fderiv_eq

theorem iteratedDeriv_state_eval {f : ℝ → DarbouxState} {y : ℝ}
    (hf : ContDiffAt ℝ ∞ f y) (n : ℕ) (i : Fin 6) :
    (iteratedDeriv n f y) i = iteratedDeriv n (fun t => f t i) y := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) y (fun _ => 1) = L (iteratedDeriv n f y)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

theorem solutionJetCurve_iteratedDeriv
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (n : ℕ) (hn : 2 ≤ n) :
    iteratedDeriv n (solutionJetCurve z x) y =
      ![0, 0, coordPartial 0 (verticalJet z n) ![x, y],
        coordPartial 1 (verticalJet z n) ![x, y],
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y],
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]] := by
  have hc := solutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · change iteratedDeriv n (fun _ : ℝ => x) y = 0
    simp [iteratedDeriv_const, show n ≠ 0 by omega]
  · change iteratedDeriv n id y = 0
    simp [iteratedDeriv_id, show n ≠ 0 by omega, show n ≠ 1 by omega]
  · change iteratedDeriv n (fun t => coordPartial 0 z ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn hz hU 0) x n y hp,
      verticalJet_coordPartial hU hz 0 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn hz hU 1) x n y hp,
      verticalJet_coordPartial hU hz 1 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn (normed_coordPartial_contDiffOn hz hU 1) hU 0) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn (normed_coordPartial_contDiffOn hz hU 1) hU 1) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 1 1]
    rfl

theorem actualDarboux_faaExpansion_coord
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (ell : ℕ) :
    coordPartial 0 (coordPartial 0 (verticalJet z ell)) ![x, y] =
      ∑ c : OrderedFinpartition ell,
        iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJetCurve z x y)
          (fun j => iteratedDeriv (c.partSize j) (solutionJetCurve z x) y) := by
  have hh := actualDarboux_faaExpansion hg hU hz hD hyy hp ell
  rw [verticalJet_slice hU (normed_coordPartial_contDiffOn (normed_coordPartial_contDiffOn hz hU 0) hU 0) x ell y hp,
    verticalJet_two_coordPartials hU hz hp ell 0 0] at hh
  exact hh

end SmoothLocal.HighEquation

end

end OAI
