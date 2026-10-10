import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid
import OAI.Analysis.LipschitzHilbert.Geometry.SeparatedPacking

namespace OAI

/-!
# The actual angular annulus bins

The positive and negative dyadic annuli about a reference slope are each
partitioned into `M` equal half-open bins, as in §6 of the manuscript.
Enlargement is concentric. No choice of a significant list enters these
definitions.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.AngularBins

abbrev Bin (M : ℕ) := Bool × ℤ × Fin M

def radialCoordinate (s : ℝ) (positive : Bool) (a : ℝ) : ℝ :=
  if positive then a - s else s - a

def width (M : ℕ) (h : ℤ) : ℝ := DyadicLineGrid.scale h / M

def radialStart (M : ℕ) (h : ℤ) (j : Fin M) : ℝ :=
  DyadicLineGrid.scale h + (j : ℝ) * width M h

def radialMidpoint (M : ℕ) (h : ℤ) (j : Fin M) : ℝ :=
  radialStart M h j + width M h / 2

def baseBin (s : ℝ) {M : ℕ} (b : Bin M) : Set ℝ :=
  {a | radialStart M b.2.1 b.2.2 ≤ radialCoordinate s b.1 a ∧
    radialCoordinate s b.1 a < radialStart M b.2.1 b.2.2 + width M b.2.1}

def enlargedBin (s c : ℝ) {M : ℕ} (b : Bin M) : Set ℝ :=
  {a | |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
    c * width M b.2.1 / 2}

theorem radialCoordinate_abs (s a : ℝ) (positive : Bool) :
    |radialCoordinate s positive a| = |a - s| := by
  cases positive <;> simp [radialCoordinate, abs_sub_comm]

theorem radialCoordinate_sub_abs (s a a' : ℝ) (positive : Bool) :
    |radialCoordinate s positive a - radialCoordinate s positive a'| = |a - a'| := by
  cases positive <;> simp only [radialCoordinate, Bool.false_eq_true, ite_false, ite_true]
  · have h : (s - a) - (s - a') = -(a - a') := by ring
    rw [h, abs_neg]
  · congr 1
    ring

theorem width_pos {M : ℕ} (hM : 0 < M) (h : ℤ) : 0 < width M h :=
  div_pos (DyadicLineGrid.scale_pos h) (by exact_mod_cast hM)

theorem width_mul {M : ℕ} (hM : 0 < M) (h : ℤ) :
    (M : ℝ) * width M h = DyadicLineGrid.scale h := by
  unfold width
  field_simp [show (M : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hM]

theorem continuous_radialCoordinate (s : ℝ) (positive : Bool) :
    Continuous (radialCoordinate s positive) := by
  cases positive
  · change Continuous (fun a : ℝ => s - a)
    exact continuous_const.sub continuous_id
  · change Continuous (fun a : ℝ => a - s)
    exact continuous_id.sub continuous_const

theorem measurableSet_baseBin (s : ℝ) {M : ℕ} (b : Bin M) :
    MeasurableSet (baseBin s b) := by
  exact (measurableSet_le measurable_const (continuous_radialCoordinate s b.1).measurable).inter
    (measurableSet_lt (continuous_radialCoordinate s b.1).measurable measurable_const)

theorem measurableSet_enlargedBin (s c : ℝ) {M : ℕ} (b : Bin M) :
    MeasurableSet (enlargedBin s c b) :=
  measurableSet_le (((continuous_radialCoordinate s b.1).sub continuous_const).abs.measurable)
    measurable_const

theorem baseBin_subset_enlargedBin (s : ℝ) {c : ℝ} (hc : 1 ≤ c)
    {M : ℕ} (hM : 0 < M) (b : Bin M) : baseBin s b ⊆ enlargedBin s c b := by
  intro a ha
  have hw := width_pos hM b.2.1
  have hcw : width M b.2.1 ≤ c * width M b.2.1 :=
    le_mul_of_one_le_left hw.le hc
  change radialStart M b.2.1 b.2.2 ≤ radialCoordinate s b.1 a ∧
    radialCoordinate s b.1 a < radialStart M b.2.1 b.2.2 + width M b.2.1 at ha
  change |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤ _
  unfold radialMidpoint
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every slope other than the reference belongs to an actual angular bin. -/
theorem exists_baseBin (s : ℝ) {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : a ≠ s) :
    ∃ b : Bin M, a ∈ baseBin s b := by
  have hr : 0 < |a - s| := abs_pos.mpr (sub_ne_zero.mpr ha)
  obtain ⟨h, hh0, hh1⟩ := exists_mem_Ico_zpow hr (by norm_num : (1 : ℝ) < 2)
  change DyadicLineGrid.scale h ≤ |a - s| at hh0
  change |a - s| < DyadicLineGrid.scale (h + 1) at hh1
  rw [DyadicLineGrid.scale_succ] at hh1
  have hw := width_pos hM h
  have hm := width_mul hM h
  let x : ℝ := (|a - s| - DyadicLineGrid.scale h) / width M h
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr hh0) hw.le
  have hxM : x < M := (div_lt_iff₀ hw).mpr (by nlinarith)
  let j : Fin M := ⟨⌊x⌋₊, (Nat.floor_lt hx0).mpr hxM⟩
  have hj0 := mul_le_mul_of_nonneg_right (Nat.floor_le hx0) hw.le
  have hj1 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one x) hw
  have hxw : x * width M h = |a - s| - DyadicLineGrid.scale h := by
    dsimp only [x]
    exact div_mul_cancel₀ _ hw.ne'
  rw [hxw] at hj0 hj1
  have hrad : ∃ positive : Bool, radialCoordinate s positive a = |a - s| := by
    by_cases hsa : s ≤ a
    · exact ⟨true, by simp [radialCoordinate, abs_of_nonneg (sub_nonneg.mpr hsa)]⟩
    · exact ⟨false, by simp [radialCoordinate, abs_of_neg (sub_neg.mpr (lt_of_not_ge hsa))]⟩
  obtain ⟨positive, hpositive⟩ := hrad
  refine ⟨(positive, h, j), ?_⟩
  change radialStart M h j ≤ radialCoordinate s positive a ∧
    radialCoordinate s positive a < radialStart M h j + width M h
  rw [hpositive]
  dsimp only [radialStart, j]
  constructor <;> nlinarith

theorem baseBin_radial_bounds (s : ℝ) {M : ℕ} (hM : 0 < M)
    {b : Bin M} {a : ℝ} (ha : a ∈ baseBin s b) :
    DyadicLineGrid.scale b.2.1 ≤ |a - s| ∧
      |a - s| < 2 * DyadicLineGrid.scale b.2.1 := by
  have hw := width_pos hM b.2.1
  have hm := width_mul hM b.2.1
  have hj0 : (0 : ℝ) ≤ b.2.2 := Nat.cast_nonneg _
  have hj1 : (b.2.2 : ℝ) + 1 ≤ M := by exact_mod_cast b.2.2.isLt
  have hstart : DyadicLineGrid.scale b.2.1 ≤ radialStart M b.2.1 b.2.2 := by
    unfold radialStart
    linarith [mul_nonneg hj0 hw.le]
  have hend : radialStart M b.2.1 b.2.2 + width M b.2.1 ≤
      2 * DyadicLineGrid.scale b.2.1 := by
    have hmul := mul_le_mul_of_nonneg_right hj1 hw.le
    unfold radialStart
    nlinarith
  have ha' : 0 ≤ radialCoordinate s b.1 a :=
    (DyadicLineGrid.scale_pos b.2.1).le.trans (hstart.trans ha.1)
  rw [← radialCoordinate_abs s a b.1, abs_of_nonneg ha']
  exact ⟨hstart.trans ha.1, ha.2.trans_le hend⟩

theorem baseBin_diameter_lt (s : ℝ) {M : ℕ} (b : Bin M)
    {a a' : ℝ} (ha : a ∈ baseBin s b) (ha' : a' ∈ baseBin s b) :
    |a - a'| < width M b.2.1 := by
  rw [← radialCoordinate_sub_abs s a a' b.1]
  exact abs_lt.mpr ⟨by linarith [ha.1, ha'.2], by linarith [ha.2, ha'.1]⟩

/-- A perturbation of a base-bin slope by at most `(c-1)/2` bin widths
lies in its concentric enlargement. -/
theorem nearby_mem_enlargedBin (s : ℝ) {M : ℕ} (b : Bin M) {c a a' : ℝ}
    (ha : a ∈ baseBin s b)
    (hnear : |a' - a| ≤ (c - 1) * width M b.2.1 / 2) :
    a' ∈ enlargedBin s c b := by
  have hbase : |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
      width M b.2.1 / 2 := by
    unfold radialMidpoint
    exact abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have htri := abs_add_le (radialCoordinate s b.1 a' - radialCoordinate s b.1 a)
    (radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2)
  rw [sub_add_sub_cancel, radialCoordinate_sub_abs] at htri
  change |radialCoordinate s b.1 a' - radialMidpoint M b.2.1 b.2.2| ≤ _
  linarith

/-- A separated list occupies distinct bins whenever those bins are
strictly narrower than the separation scale. -/
theorem assigned_bins_injective {ι : Type*} (s : ℝ) {M : ℕ}
    (frequency : ι → ℝ) (bin : ι → Bin M) {rho : ℝ}
    (hsep : PhaseCombinatorics.Separated frequency rho)
    (hmem : ∀ i, frequency i ∈ baseBin s (bin i))
    (hwidth : ∀ i, width M (bin i).2.1 < rho) : Function.Injective bin := by
  intro i j hij
  by_contra hne
  have hdiam := baseBin_diameter_lt s (bin i) (hmem i) (by simpa only [hij] using hmem j)
  exact (not_lt_of_ge (hsep hne)) (hdiam.trans (hwidth i))

end LipschitzHilbert.AngularBins

end

end OAI
