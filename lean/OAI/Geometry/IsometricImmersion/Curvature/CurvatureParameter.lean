import OAI.Geometry.IsometricImmersion.Metric
import OAI.Geometry.IsometricImmersion.Calculus.SmoothCurry
import OAI.Geometry.IsometricImmersion.Volterra.VolterraInverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinate_square_isOpen : IsOpen square := by
  have heq : square = ⋂ i : Fin 2,
      (fun p : Coord => p i) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext p
    simp [square]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

def coordinatePoint (x y : ℝ) : Coord :=
  x • Pi.single 0 1 + y • Pi.single 1 1

theorem coordinatePoint_mem_square {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    coordinatePoint x y ∈ square := by
  intro i
  fin_cases i
  · simpa [coordinatePoint] using hx
  · simpa [coordinatePoint] using hy

theorem coordinatePoint_hasDerivAt_y (x y : ℝ) :
    HasDerivAt (coordinatePoint x) (Pi.single 1 (1 : ℝ) : Coord) y := by
  change HasDerivAt (fun t : ℝ => x • (Pi.single 0 (1 : ℝ) : Coord) +
    t • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) y
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id y).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (x • (Pi.single 0 (1 : ℝ) : Coord))

def curvatureYDerivative (K : Coord → ℝ) : ℕ → Coord → ℝ
  | 0 => K
  | n + 1 => coordPartial 1 (curvatureYDerivative K n)

theorem curvatureYDerivative_smooth {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square) :
    ∀ n, ContDiffOn ℝ ∞ (curvatureYDerivative K n) square := by
  intro n
  induction n with
  | zero => exact hK
  | succ n hn => exact partial_contDiffOn hn coordinate_square_isOpen 1

theorem compact_x_mem_square_interval {r : ℝ} (hr1 : r < 1)
    (x : Icc (-r) r) : (x : ℝ) ∈ Ioo (-1 : ℝ) 1 :=
  ⟨(neg_lt_neg hr1).trans_le x.2.1, x.2.2.trans_lt hr1⟩

def coordinateCurvatureFamily (K : Coord → ℝ) (r : ℝ) (y : ℝ) : IntervalFunctions r :=
  ContinuousMap.mkD (fun x : Icc (-r) r => K (coordinatePoint x y)) 0

theorem coordinateCurvatureFamily_apply {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square) (r : ℝ) (hr1 : r < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (x : Icc (-r) r) :
    coordinateCurvatureFamily K r y x = K (coordinatePoint x y) := by
  have hc : Continuous (fun z : Icc (-r) r => K (coordinatePoint z y)) :=
    hK.continuousOn.comp_continuous (by unfold coordinatePoint; fun_prop)
      (fun z => coordinatePoint_mem_square (compact_x_mem_square_interval hr1 z) hy)
  unfold coordinateCurvatureFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem coordinateCurvatureFamily_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square) (r : ℝ) (hr1 : r < 1) :
    ContDiffOn ℝ ∞ (coordinateCurvatureFamily K r) (Ioo (-1 : ℝ) 1) := by
  let H : ℕ → ℝ → Icc (-r) r → ℝ :=
    fun n y x => curvatureYDerivative K n (coordinatePoint x y)
  have hpointMem (y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 1) (x : Icc (-r) r) :
      coordinatePoint x y ∈ square :=
    coordinatePoint_mem_square (compact_x_mem_square_interval hr1 x) hy
  have hjoint (n : ℕ) : ContinuousOn (Function.uncurry (H n))
      ((Ioo (-1 : ℝ) 1) ×ˢ (Set.univ : Set (Icc (-r) r))) := by
    have hmap : Continuous (fun p : ℝ × Icc (-r) r => coordinatePoint p.2 p.1) := by
      unfold coordinatePoint
      fun_prop
    exact (curvatureYDerivative_smooth hK n).continuousOn.comp hmap.continuousOn
      (fun p hp => hpointMem p.1 hp.1 p.2)
  have hderiv (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 1) (x : Icc (-r) r) :
      HasDerivAt (fun s => H n s x) (H (n + 1) y x) y := by
    have hd : DifferentiableAt ℝ (curvatureYDerivative K n) (coordinatePoint x y) :=
      ((curvatureYDerivative_smooth hK n).contDiffAt
        (coordinate_square_isOpen.mem_nhds (hpointMem y hy x))).differentiableAt (by simp)
    change HasDerivAt (fun s => curvatureYDerivative K n (coordinatePoint x s))
      (coordPartial 1 (curvatureYDerivative K n) (coordinatePoint x y)) y
    exact hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  have hs := smooth_curry_of_joint_derivative_sequence H hjoint hderiv 0
  change ContDiffOn ℝ ∞
    (fun y => ContinuousMap.mkD (fun x : Icc (-r) r => K (coordinatePoint x y)) 0)
    (Ioo (-1 : ℝ) 1)
  exact hs

theorem coordinateCurvatureFamily_norm_le {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr1 : r < 1) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ‖coordinateCurvatureFamily K r y‖ ≤ (1 : ℝ) / 1000 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1 / 1000)).mpr
  intro x
  rw [coordinateCurvatureFamily_apply hK r hr1 hy x, Real.norm_eq_abs]
  exact hbound _ (coordinatePoint_mem_square (compact_x_mem_square_interval hr1 x) hy)

def prescribedVolterraFamily (K : Coord → ℝ) (r : ℝ) (hr : 0 < r) (y : ℝ) :
    IntervalFunctions r :=
  volterraSolution r hr (coordinateCurvatureFamily K r y)

theorem prescribedVolterraFamily_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ContDiffOn ℝ ∞ (prescribedVolterraFamily K r hr) (Ioo (-1 : ℝ) 1) :=
  volterraSolution_family_contDiffOn r hr hr1.le
    (coordinateCurvatureFamily_contDiffOn hK r hr1)
    (fun _ hy => coordinateCurvatureFamily_norm_le hK hbound r hr1 hy)

theorem prescribedVolterraFamily_equation {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    prescribedVolterraFamily K r hr y + volterraCLM r hr
      (coordinateCurvatureFamily K r y * prescribedVolterraFamily K r hr y) = 1 :=
  volterraSolution_equation r hr hr1.le (coordinateCurvatureFamily K r y)
    (coordinateCurvatureFamily_norm_le hK hbound r hr1 hy)

end SmoothLocal.ODE

end

end OAI
