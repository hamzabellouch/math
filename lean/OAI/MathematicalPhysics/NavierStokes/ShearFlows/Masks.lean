import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Construction
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Differential

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem cube_integral_prod (L : ℝ) (f : Fin 3 → ℝ → ℝ) :
    (∫ x in fundamentalCube L, ∏ j, f j (x j)) =
      ∏ j, ∫ s in Icc (0 : ℝ) L, f j s := by
  unfold fundamentalCube
  rw [← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod f

theorem cube_integral_three (L : ℝ) (f g h : ℝ → ℝ) :
    (∫ x in fundamentalCube L, f (x 0) * g (x 1) * h (x 2)) =
      (∫ s in Icc (0 : ℝ) L, f s) * (∫ s in Icc (0 : ℝ) L, g s) *
        (∫ s in Icc (0 : ℝ) L, h s) := by
  simpa [Fin.prod_univ_succ, mul_assoc] using cube_integral_prod L ![f,g,h]

theorem circleMask_setIntegral_zero {L a b c d : ℝ} (hL : 0 < L)
    (hab : a < b) (hcd : c < d) (p : ℝ) :
    (∫ x in Icc (0 : ℝ) L, circleMask L a b c d p x) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le]
  exact circleMask_integral_zero hL hab hcd p

theorem planarMask_cube_mean_zero {L : ℝ} (hL : 0 < L)
    (R : RationalBox 2) {r : ℚ} (hr : 0 < r) :
    (∫ x in fundamentalCube L, planarMask L R r (horizontal x)) = 0 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let f := circleMask L (R.lower 0 - 2*r) (R.lower 0 - r) (R.upper 0 + r)
    (R.upper 0 + 2*r) (R.center 0)
  let g := circleCutoff L (R.lower 1 - 2*r) (R.lower 1 - r) (R.upper 1 + r)
    (R.upper 1 + 2*r)
  change (∫ x in fundamentalCube L, f (x 0) * g (x 1)) = 0
  have hz : (∫ s in Icc (0 : ℝ) L, f s) = 0 :=
    circleMask_setIntegral_zero hL (by linarith) (by linarith) _
  have heq := cube_integral_three L f g (fun _ => 1)
  simpa [hz] using heq

namespace Input

def horizontalBox (d : Input) : RationalBox 2 := d.centers.inflate (2*d.h)

def horizontalRadius (d : Input) : ℚ :=
  boxChartGap d.planarLower d.planarUpper d.horizontalBox / 8

def sourceMask (d : Input) (i : Fin d.instructions.length) : Plane → ℝ :=
  planarMask d.period (d.sources i) d.sourceRadius

def targetMask (d : Input) (i : Fin d.instructions.length) : Plane → ℝ :=
  planarMask d.period (d.targets i) d.targetRadius

def heightMask (d : Input) (i : Fin d.instructions.length) : ℝ → ℝ :=
  letI := twoAtLeastTwo
  circleMask d.period (d.privateHeight i - 2*d.heightRadius)
    (d.privateHeight i - d.heightRadius) (d.privateHeight i + d.heightRadius)
    (d.privateHeight i + 2*d.heightRadius) (d.privateHeight i)

def horizontalProfile (d : Input) (i : Fin d.instructions.length) (j : Fin 2) : ℝ → ℝ :=
  letI := twoAtLeastTwo
  periodize d.period (fun x => (x - (d.sources i).center j) *
    closedCutoff (d.horizontalBox.lower j - 2*d.horizontalRadius)
      (d.horizontalBox.lower j - d.horizontalRadius)
      (d.horizontalBox.upper j + d.horizontalRadius)
      (d.horizontalBox.upper j + 2*d.horizontalRadius) x)

end Input

theorem horizontalRadius_pos {d : Input} (hd : ValidInput d) : 0 < d.horizontalRadius := by
  apply div_pos _ (by norm_num : (0 : ℚ) < 8)
  apply boxChartGap_pos
  intro j
  constructor
  · exact_mod_cast (hd.chartMargin j).1
  · exact_mod_cast (hd.chartMargin j).2

theorem horizontal_collars_inside {d : Input} (hd : ValidInput d) (j : Fin 2) :
    d.planarLower j < d.horizontalBox.lower j - 2*d.horizontalRadius ∧
      d.horizontalBox.upper j + 2*d.horizontalRadius < d.planarUpper j := by
  have hh := horizontalRadius_pos hd
  have hb := boxChartGap_bounds d.planarLower d.planarUpper d.horizontalBox j
  have heq : 8 * d.horizontalRadius = boxChartGap d.planarLower d.planarUpper d.horizontalBox := by
    dsimp [Input.horizontalRadius]
    ring
  constructor <;> linarith

theorem sourceMask_smooth {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) :
    ContDiff ℝ ∞ (d.sourceMask i) :=
  planarMask_smooth (by exact_mod_cast hd.period_pos) _ (sourceRadius_pos hd)

theorem targetMask_smooth {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) :
    ContDiff ℝ ∞ (d.targetMask i) :=
  planarMask_smooth (by exact_mod_cast hd.period_pos) _ (targetRadius_pos hd)

theorem heightMask_smooth {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) :
    ContDiff ℝ ∞ (d.heightMask i) := by
  have hr : (0 : ℝ) < d.heightRadius := by
    exact_mod_cast (div_pos (heightSpacing_pos hd) (by norm_num : (0 : ℚ) < 8))
  exact circleMask_smooth (by exact_mod_cast hd.period_pos) (by linarith) (by linarith) _

theorem heightMask_periodic (d : Input) (i : Fin d.instructions.length) :
    Function.Periodic (d.heightMask i) d.period := circleMask_periodic _ _ _ _ _ _

theorem heightMask_integral_zero {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) :
    (∫ s in Icc (0 : ℝ) d.period, d.heightMask i s) = 0 := by
  have hr : (0 : ℝ) < d.heightRadius := by
    exact_mod_cast (div_pos (heightSpacing_pos hd) (by norm_num : (0 : ℚ) < 8))
  exact circleMask_setIntegral_zero (by exact_mod_cast hd.period_pos)
    (by linarith) (by linarith) _

theorem horizontalProfile_periodic (d : Input) (i : Fin d.instructions.length) (j : Fin 2) :
    Function.Periodic (d.horizontalProfile i j) d.period := periodize_periodic _ _

theorem horizontalProfile_smooth {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) (j : Fin 2) : ContDiff ℝ ∞ (d.horizontalProfile i j) := by
  have hr : (0 : ℝ) < d.horizontalRadius := by exact_mod_cast horizontalRadius_pos hd
  apply periodize_smooth (by exact_mod_cast hd.period_pos)
  · exact maskPotential_support (by linarith) (by linarith) _
  · exact (contDiff_id.sub contDiff_const).mul (closedCutoff_smooth _ _ _ _)

theorem horizontalProfile_eq {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) (j : Fin 2) {x : ℝ}
    (hx : x ∈ Icc (d.horizontalBox.lower j - d.horizontalRadius : ℝ)
      (d.horizontalBox.upper j + d.horizontalRadius : ℝ)) :
    d.horizontalProfile i j x = x - (d.sources i).center j := by
  have hr : (0 : ℝ) < d.horizontalRadius := by exact_mod_cast horizontalRadius_pos hd
  have hA : (d.planarLower j : ℝ) < d.horizontalBox.lower j - 2*d.horizontalRadius := by
    exact_mod_cast (horizontal_collars_inside hd j).1
  have hB : (d.horizontalBox.upper j : ℝ) + 2*d.horizontalRadius < d.planarUpper j := by
    exact_mod_cast (horizontal_collars_inside hd j).2
  have hlen : (d.planarUpper j : ℝ) - d.planarLower j ≤ d.period := by
    exact_mod_cast (hd.chart_length j.castSucc).le
  unfold Input.horizontalProfile
  rw [periodize_eq_in_chart (A := d.planarLower j) (B := d.planarUpper j)
    (by exact_mod_cast hd.period_pos) hlen]
  · rw [closedCutoff_plateau (by linarith) (by linarith) hx, mul_one]
  · intro y hy
    have hy' := maskPotential_support
      (show (d.horizontalBox.lower j : ℝ) - 2*d.horizontalRadius <
        d.horizontalBox.lower j - d.horizontalRadius by linarith)
      (show (d.horizontalBox.upper j : ℝ) + d.horizontalRadius <
        d.horizontalBox.upper j + 2*d.horizontalRadius by linarith) ((d.sources i).center j) hy
    exact ⟨hA.trans_le hy'.1, hy'.2.trans_lt hB⟩
  · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem heightMask_near_privateHeight {d : Input} (hd : ValidInput d)
    (i j : Fin d.instructions.length) {z : ℝ}
    (hz : |z - (d.privateHeight i : ℝ)| < (d.heightRadius : ℝ)) :
    d.heightMask j z = if j = i then 1 else 0 := by
  have hL : (0 : ℝ) < d.period := by exact_mod_cast hd.period_pos
  have hr : (0 : ℝ) < d.heightRadius := by
    exact_mod_cast (div_pos (heightSpacing_pos hd) (by norm_num : (0 : ℚ) < 8))
  have hlen : (d.chart.upper 2 : ℝ) - d.chart.lower 2 ≤ d.period := by
    exact_mod_cast (hd.chart_length 2).le
  have hA (k : Fin d.instructions.length) :
      (d.chart.lower 2 : ℝ) < d.privateHeight k - 2*d.heightRadius := by
    exact_mod_cast (privateHeight_collars_inside hd k).1
  have hB (k : Fin d.instructions.length) :
      (d.privateHeight k + 2*d.heightRadius : ℝ) < d.chart.upper 2 := by
    exact_mod_cast (privateHeight_collars_inside hd k).2
  have hz' := abs_lt.mp hz
  have hzi : z ∈ Icc (d.privateHeight i - 2*d.heightRadius : ℝ)
      (d.privateHeight i + 2*d.heightRadius : ℝ) := ⟨by linarith, by linarith⟩
  split_ifs with hji
  · subst j
    apply circleMask_plateau hL hlen (hA i) (hB i) (by linarith) (by linarith)
    exact ⟨by linarith, by linarith⟩
  · apply circleMask_zero_in_chart hL hlen (hA j) (hB j) (by linarith) (by linarith)
    · exact ⟨(hA i).trans_le hzi.1, hzi.2.trans_lt (hB i)⟩
    · intro hzj
      exact Set.disjoint_left.mp (privateHeight_collars_disjoint hd (Ne.symm hji)) hzi hzj

end ShearFlows

end

end OAI
