import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Extension
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Geometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

namespace Input

def planarLower (d : Input) (j : Fin 2) : ℚ := d.chart.lower j.castSucc
def planarUpper (d : Input) (j : Fin 2) : ℚ := d.chart.upper j.castSucc
def sources (d : Input) (i : Fin d.instructions.length) : RationalBox 2 :=
  (d.instructions.get i).source
def targets (d : Input) (i : Fin d.instructions.length) : RationalBox 2 :=
  (d.instructions.get i).target
def sourceRadius (d : Input) : ℚ := collarRadius d.planarLower d.planarUpper d.sources
def targetRadius (d : Input) : ℚ := collarRadius d.planarLower d.planarUpper d.targets

def heightSpacing (d : Input) : ℚ :=
  letI := neZeroThree
  (d.chart.upper 2 - d.chart.lower 2) / (d.instructions.length + 1)
def privateHeight (d : Input) (i : Fin d.instructions.length) : ℚ :=
  letI := neZeroThree
  d.chart.lower 2 + ((i : ℕ) + 1) * d.heightSpacing
def heightRadius (d : Input) : ℚ := d.heightSpacing / 8

end Input

theorem boxChartGap_pos_of_inChart {A B : Fin 2 → ℚ} {R : RationalBox 2}
    (hR : R.positive)
    (hc : R.carrier ⊆ {x | ∀ j, (A j : ℝ) < x j ∧ x j < (B j : ℝ)}) :
    0 < boxChartGap A B R := by
  have hlo : (fun j => (R.lower j : ℝ)) ∈ R.carrier := by
    intro j
    exact ⟨le_rfl, by simpa using (Rat.cast_le.mpr (hR j).le : (R.lower j : ℝ) ≤ R.upper j)⟩
  have hhi : (fun j => (R.upper j : ℝ)) ∈ R.carrier := by
    intro j
    exact ⟨by simpa using (Rat.cast_le.mpr (hR j).le : (R.lower j : ℝ) ≤ R.upper j), le_rfl⟩
  apply boxChartGap_pos
  intro j
  exact ⟨by exact_mod_cast (hc hlo j).1, by exact_mod_cast (hc hhi j).2⟩

theorem sourceRadius_pos {d : Input} (hd : ValidInput d) : 0 < d.sourceRadius := by
  apply collarRadius_pos
  · intro i
    exact boxChartGap_pos_of_inChart (hd.source_positive _ (List.getElem_mem _))
      (hd.source_in_chart _ (List.getElem_mem _))
  · intro i j hij
    exact boxGap_pos_of_separated _ _ (hd.source_positive _ (List.getElem_mem _))
      (hd.source_positive _ (List.getElem_mem _)) (hd.source_separation i j hij)

theorem targetRadius_pos {d : Input} (hd : ValidInput d) : 0 < d.targetRadius := by
  apply collarRadius_pos
  · intro i
    exact boxChartGap_pos_of_inChart (hd.target_positive _ (List.getElem_mem _))
      (hd.target_in_chart _ (List.getElem_mem _))
  · intro i j hij
    exact boxGap_pos_of_separated _ _ (hd.target_positive _ (List.getElem_mem _))
      (hd.target_positive _ (List.getElem_mem _)) (hd.target_separation i j hij)

theorem heightSpacing_pos {d : Input} (hd : ValidInput d) : 0 < d.heightSpacing := by
  exact div_pos (sub_pos.mpr (hd.chart_positive 2)) (by positivity)

theorem privateHeight_collars_inside {d : Input} (hd : ValidInput d)
    (i : Fin d.instructions.length) :
    d.chart.lower 2 < d.privateHeight i - 2 * d.heightRadius ∧
      d.privateHeight i + 2 * d.heightRadius < d.chart.upper 2 := by
  have hs := heightSpacing_pos hd
  have hin : (i : ℚ) + 1 ≤ d.instructions.length := by exact_mod_cast i.isLt
  have hi : (0 : ℚ) ≤ i := by positivity
  have hden : (d.instructions.length : ℚ) + 1 ≠ 0 := by positivity
  have heq : ((d.instructions.length : ℚ) + 1) * d.heightSpacing =
      d.chart.upper 2 - d.chart.lower 2 := by
    dsimp [Input.heightSpacing]
    field_simp
  dsimp [Input.privateHeight, Input.heightRadius]
  constructor <;> nlinarith

theorem privateHeight_order {d : Input} (hd : ValidInput d)
    {i j : Fin d.instructions.length} (hij : i < j) :
    d.privateHeight i + 2 * d.heightRadius <
      d.privateHeight j - 2 * d.heightRadius := by
  have hs := heightSpacing_pos hd
  have hij' : (i : ℚ) + 1 ≤ j := by exact_mod_cast hij
  dsimp [Input.privateHeight, Input.heightRadius]
  nlinarith

theorem privateHeight_collars_disjoint {d : Input} (hd : ValidInput d)
    {i j : Fin d.instructions.length} (hij : i ≠ j) :
    Disjoint (Icc (d.privateHeight i - 2 * d.heightRadius : ℝ)
      (d.privateHeight i + 2 * d.heightRadius : ℝ))
      (Icc (d.privateHeight j - 2 * d.heightRadius : ℝ)
        (d.privateHeight j + 2 * d.heightRadius : ℝ)) := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · apply Set.disjoint_left.mpr
    intro x hxi hxj
    have ho : (d.privateHeight i + 2 * d.heightRadius : ℝ) <
        d.privateHeight j - 2 * d.heightRadius := by exact_mod_cast privateHeight_order hd hij
    linarith [hxi.2, hxj.1]
  · apply Disjoint.symm
    apply Set.disjoint_left.mpr
    intro x hxj hxi
    have ho : (d.privateHeight j + 2 * d.heightRadius : ℝ) <
        d.privateHeight i - 2 * d.heightRadius := by exact_mod_cast privateHeight_order hd hij
    linarith [hxj.2, hxi.1]

def circleCutoff (L a b c d : ℝ) : ℝ → ℝ := periodize L (closedCutoff a b c d)

theorem circleCutoff_smooth {L a b c d : ℝ} (hL : 0 < L)
    (hab : a < b) (hcd : c < d) : ContDiff ℝ ∞ (circleCutoff L a b c d) :=
  periodize_smooth hL ((closedCutoff_support hab hcd).trans Ioo_subset_Icc_self)
    (closedCutoff_smooth _ _ _ _)

theorem circleCutoff_periodic (L a b c d : ℝ) :
    Function.Periodic (circleCutoff L a b c d) L := periodize_periodic _ _

theorem circleCutoff_eq_in_chart {L A B a b c d x : ℝ}
    (hL : 0 < L) (hlen : B - A ≤ L) (hAa : A < a) (hdB : d < B)
    (hab : a < b) (hcd : c < d) (hx : x ∈ Icc A B) :
    circleCutoff L a b c d x = closedCutoff a b c d x := by
  apply periodize_eq_in_chart hL hlen _ hx
  intro x hx
  have h := closedCutoff_support hab hcd hx
  exact ⟨hAa.trans h.1, h.2.trans hdB⟩

theorem circleCutoff_plateau {L A B a b c d x : ℝ}
    (hL : 0 < L) (hlen : B - A ≤ L) (hAa : A < a) (hdB : d < B)
    (hab : a < b) (hcd : c < d) (hx : x ∈ Icc b c) :
    circleCutoff L a b c d x = 1 := by
  rw [circleCutoff_eq_in_chart hL hlen hAa hdB hab hcd
    ⟨(hAa.trans_le (hab.le.trans hx.1)).le, (hx.2.trans (hcd.le.trans hdB.le))⟩]
  exact closedCutoff_plateau hab hcd hx

theorem circleCutoff_zero_in_chart {L A B a b c d x : ℝ}
    (hL : 0 < L) (hlen : B - A ≤ L) (hAa : A < a) (hdB : d < B)
    (hab : a < b) (hcd : c < d) (hx : x ∈ Icc A B) (hout : x ∉ Icc a d) :
    circleCutoff L a b c d x = 0 := by
  rw [circleCutoff_eq_in_chart hL hlen hAa hdB hab hcd hx]
  by_contra h
  exact hout (Ioo_subset_Icc_self (closedCutoff_support hab hcd h))

def planarMask (L : ℝ) (R : RationalBox 2) (r : ℚ) (X : Plane) : ℝ :=
  letI := neZeroTwo
  letI := twoAtLeastTwo
  circleMask L (R.lower 0 - 2*r) (R.lower 0 - r) (R.upper 0 + r) (R.upper 0 + 2*r)
    (R.center 0) (X 0) *
  circleCutoff L (R.lower 1 - 2*r) (R.lower 1 - r) (R.upper 1 + r) (R.upper 1 + 2*r)
    (X 1)

theorem planarMask_smooth {L : ℝ} (hL : 0 < L) (R : RationalBox 2)
    {r : ℚ} (hr : 0 < r) : ContDiff ℝ ∞ (planarMask L R r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  apply ContDiff.mul
  · exact (circleMask_smooth hL (by linarith) (by linarith) _).comp (ContinuousLinearMap.proj 0 : Plane →L[ℝ] ℝ).contDiff
  · exact (circleCutoff_smooth hL (by linarith) (by linarith)).comp (ContinuousLinearMap.proj 1 : Plane →L[ℝ] ℝ).contDiff

theorem planarMask_periodic (L : ℝ) (R : RationalBox 2) (r : ℚ)
    (X : Plane) (n : Fin 2 → ℤ) :
    planarMask L R r (X + fun j => L * (n j : ℝ)) = planarMask L R r X := by
  dsimp [planarMask]
  congr 1
  · simpa [mul_comm] using (circleMask_periodic L _ _ _ _ _).int_mul (n 0) (X 0)
  · simpa [mul_comm] using (circleCutoff_periodic L _ _ _ _).int_mul (n 1) (X 1)

theorem planarMask_plateau {L : ℝ} {A B : Fin 2 → ℚ} (hL : 0 < L)
    (hlen : ∀ j, (B j : ℝ) - A j ≤ L) (R : RationalBox 2) {r : ℚ} (hr : 0 < r)
    (hc : ∀ j, A j < R.lower j - 2*r ∧ R.upper j + 2*r < B j)
    {X : Plane} (hX : ∀ j, (R.lower j : ℝ) - r < X j ∧ X j < R.upper j + r) :
    planarMask L R r X = 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hA (j) : (A j : ℝ) < R.lower j - 2*r := by exact_mod_cast (hc j).1
  have hB (j) : (R.upper j : ℝ) + 2*r < B j := by exact_mod_cast (hc j).2
  rw [planarMask, circleMask_plateau hL (hlen 0) (hA 0) (hB 0)
    (by linarith) (by linarith) (hX 0),
    circleCutoff_plateau hL (hlen 1) (hA 1) (hB 1)
      (by linarith) (by linarith) ⟨(hX 1).1.le, (hX 1).2.le⟩, one_mul]

theorem planarMask_zero_in_chart {L : ℝ} {A B : Fin 2 → ℚ} (hL : 0 < L)
    (hlen : ∀ j, (B j : ℝ) - A j ≤ L) (R : RationalBox 2) {r : ℚ} (hr : 0 < r)
    (hc : ∀ j, A j < R.lower j - 2*r ∧ R.upper j + 2*r < B j)
    {X : Plane} (hX : ∀ j, (A j : ℝ) < X j ∧ X j < B j)
    (hout : X ∉ (R.inflate (2*r)).carrier) : planarMask L R r X = 0 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hA (j) : (A j : ℝ) < R.lower j - 2*r := by exact_mod_cast (hc j).1
  have hB (j) : (R.upper j : ℝ) + 2*r < B j := by exact_mod_cast (hc j).2
  have hout' : ∃ j, X j ∉ Icc ((R.lower j : ℝ) - 2*r) ((R.upper j : ℝ) + 2*r) := by
    by_contra hh
    push Not at hh
    apply hout
    intro j
    simpa [RationalBox.inflate] using hh j
  obtain ⟨j,hj⟩ := hout'
  fin_cases j
  · rw [planarMask, circleMask_zero_in_chart hL (hlen 0) (hA 0) (hB 0)
      (by linarith) (by linarith) (hX 0) hj, zero_mul]
  · rw [planarMask, circleCutoff_zero_in_chart hL (hlen 1) (hA 1) (hB 1)
      (by linarith) (by linarith) (Ioo_subset_Icc_self (hX 1)) hj, mul_zero]

theorem near_box_inside_plateau (R : RationalBox 2) {r : ℚ}
    {X Y : Plane} (hY : Y ∈ R.carrier) (hXY : ‖X - Y‖ < (r : ℝ)) :
    ∀ j, (R.lower j : ℝ) - r < X j ∧ X j < R.upper j + r := by
  intro j
  have hj : |X j - Y j| < (r : ℝ) :=
    (norm_le_pi_norm (X - Y) j).trans_lt hXY
  have hb := abs_lt.mp hj
  constructor <;> linarith [(hY j).1, (hY j).2]

theorem familyMask_near {n : ℕ} {L : ℝ} {A B : Fin 2 → ℚ}
    (R : Fin n → RationalBox 2) (hL : 0 < L)
    (hlen : ∀ j, (B j : ℝ) - A j ≤ L) (hr : 0 < collarRadius A B R)
    (i j : Fin n) {X Y : Plane} (hY : Y ∈ (R i).carrier)
    (hXY : ‖X - Y‖ < (collarRadius A B R : ℝ)) :
    planarMask L (R j) (collarRadius A B R) X = if j = i then 1 else 0 := by
  have hX := near_box_inside_plateau (R i) hY hXY
  have hr' : (0 : ℝ) < collarRadius A B R := by exact_mod_cast hr
  have hXi : X ∈ ((R i).inflate (2 * collarRadius A B R)).carrier := by
    intro k
    dsimp [RationalBox.inflate]
    push_cast
    constructor <;> linarith [(hX k).1, (hX k).2]
  have hAc (k) : (A k : ℝ) < (R i).lower k - 2 * collarRadius A B R := by
    exact_mod_cast (collar_inside_chart hr i k).1
  have hBc (k) : ((R i).upper k : ℝ) + 2 * collarRadius A B R < B k := by
    exact_mod_cast (collar_inside_chart hr i k).2
  have hchart : ∀ k, (A k : ℝ) < X k ∧ X k < B k := by
    intro k
    constructor <;> linarith [(hX k).1, (hX k).2, hAc k, hBc k]
  split_ifs with hji
  · subst j
    exact planarMask_plateau hL hlen (R i) hr (collar_inside_chart hr i) hX
  · apply planarMask_zero_in_chart hL hlen (R j) hr (collar_inside_chart hr j) hchart
    intro hXj
    exact Set.disjoint_left.mp (collar_disjoint hr (Ne.symm hji)) hXi hXj

theorem sourceMask_near_box {d : Input} (hd : ValidInput d)
    (i j : Fin d.instructions.length) {X Y : Plane}
    (hY : Y ∈ (d.sources i).carrier) (hXY : ‖X - Y‖ < (d.sourceRadius : ℝ)) :
    planarMask d.period (d.sources j) d.sourceRadius X = if j = i then 1 else 0 :=
  familyMask_near d.sources (by exact_mod_cast hd.period_pos)
    (fun k => by exact_mod_cast (hd.chart_length k.castSucc).le)
    (sourceRadius_pos hd) i j hY hXY

theorem targetMask_near_box {d : Input} (hd : ValidInput d)
    (i j : Fin d.instructions.length) {X Y : Plane}
    (hY : Y ∈ (d.targets i).carrier) (hXY : ‖X - Y‖ < (d.targetRadius : ℝ)) :
    planarMask d.period (d.targets j) d.targetRadius X = if j = i then 1 else 0 :=
  familyMask_near d.targets (by exact_mod_cast hd.period_pos)
    (fun k => by exact_mod_cast (hd.chart_length k.castSucc).le)
    (targetRadius_pos hd) i j hY hXY

end ShearFlows

end

end OAI
