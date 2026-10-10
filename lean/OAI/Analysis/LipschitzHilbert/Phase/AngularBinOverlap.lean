import OAI.Analysis.LipschitzHilbert.Phase.AngularBins
import Mathlib.Data.Int.Interval

namespace OAI

/-! Fixed overlap of the enlarged angular annulus bins from §6. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.AngularBins

attribute [local instance] Classical.propDecidable

theorem enlargedBin_radial_bounds (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hcM : c ≤ M) {b : Bin M} {a : ℝ}
    (ha : a ∈ enlargedBin s c b) :
    DyadicLineGrid.scale b.2.1 / 2 ≤ |a - s| ∧
      |a - s| ≤ 5 * DyadicLineGrid.scale b.2.1 / 2 := by
  have hw := width_pos hM b.2.1
  have hm := width_mul hM b.2.1
  have hj0 : (0 : ℝ) ≤ b.2.2 := Nat.cast_nonneg _
  have hj1 : (b.2.2 : ℝ) + 1 ≤ M := by exact_mod_cast b.2.2.isLt
  have hmid0 : DyadicLineGrid.scale b.2.1 ≤ radialMidpoint M b.2.1 b.2.2 := by
    unfold radialMidpoint radialStart
    nlinarith [mul_nonneg hj0 hw.le]
  have hmid1 : radialMidpoint M b.2.1 b.2.2 ≤ 2 * DyadicLineGrid.scale b.2.1 := by
    have hmul := mul_le_mul_of_nonneg_right hj1 hw.le
    unfold radialMidpoint radialStart
    nlinarith
  have hrad := mul_le_mul_of_nonneg_right hcM hw.le
  change |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤ _ at ha
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  have hcoord : 0 ≤ radialCoordinate s b.1 a := by
    have hs := DyadicLineGrid.scale_pos b.2.1
    nlinarith
  rw [← radialCoordinate_abs s a b.1, abs_of_nonneg hcoord]
  constructor <;> nlinarith

/-- Any two enlarged annuli covering the same point have levels differing
by at most two, uniformly in the number of angular subdivisions. -/
theorem enlargedBin_levels_near (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hcM : c ≤ M) {b b' : Bin M} {a : ℝ}
    (ha : a ∈ enlargedBin s c b) (ha' : a ∈ enlargedBin s c b') :
    b'.2.1 - 2 ≤ b.2.1 ∧ b.2.1 ≤ b'.2.1 + 2 := by
  have hb := enlargedBin_radial_bounds s hM hcM ha
  have hb' := enlargedBin_radial_bounds s hM hcM ha'
  have hlevel {i j : ℤ} (hij : DyadicLineGrid.scale i ≤ 5 * DyadicLineGrid.scale j) :
      i ≤ j + 2 := by
    by_contra hn
    have hji : j + 3 ≤ i := by omega
    have hpow : DyadicLineGrid.scale (j + 3) ≤ DyadicLineGrid.scale i :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hji
    have heq : DyadicLineGrid.scale (j + 3) = 8 * DyadicLineGrid.scale j := by
      simp only [DyadicLineGrid.scale, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
    rw [heq] at hpow
    have hs := DyadicLineGrid.scale_pos j
    linarith
  constructor
  · have h := hlevel (show DyadicLineGrid.scale b'.2.1 ≤
        5 * DyadicLineGrid.scale b.2.1 by linarith)
    omega
  · exact hlevel (by linarith)

theorem radialMidpoint_separated {M : ℕ} (hM : 0 < M) (h : ℤ) :
    PhaseCombinatorics.Separated (radialMidpoint M h) (width M h) := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hcast : 1 ≤ |(i : ℝ) - (j : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hle : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonneg (by linarith)]
      linarith
  have heq : radialMidpoint M h i - radialMidpoint M h j =
      ((i : ℝ) - j) * width M h := by
    unfold radialMidpoint radialStart
    ring
  rw [heq, abs_mul, abs_of_pos (width_pos hM h)]
  exact le_mul_of_one_le_left (width_pos hM h).le hcast

theorem finite_level_overlap (s a : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (positive : Bool) (h : ℤ) (t : Finset (Fin M))
    (ht : ∀ j ∈ t, a ∈ enlargedBin s c (positive, h, j)) :
    (t.card : ℝ) ≤ 1 + c := by
  have hw := width_pos hM h
  have hsep : PhaseCombinatorics.Separated (fun j : t => radialMidpoint M h j.1)
      (width M h) := by
    intro i j hij
    exact radialMidpoint_separated hM h (fun heq => hij (Subtype.ext heq))
  have hbounds : ∀ j : t,
      radialCoordinate s positive a - c * width M h / 2 ≤ radialMidpoint M h j.1 ∧
      radialMidpoint M h j.1 ≤ radialCoordinate s positive a + c * width M h / 2 := by
    intro j
    have hj := ht j.1 j.2
    change |radialCoordinate s positive a - radialMidpoint M h j.1| ≤
      c * width M h / 2 at hj
    obtain ⟨hj0, hj1⟩ := abs_le.mp hj
    constructor <;> linarith
  have hpack := PhaseCombinatorics.separated_card_le_span _ hw
    (show radialCoordinate s positive a - c * width M h / 2 ≤
      radialCoordinate s positive a + c * width M h / 2 by
        nlinarith [mul_nonneg hc hw.le])
    hsep hbounds
  have heq : ((radialCoordinate s positive a + c * width M h / 2) -
      (radialCoordinate s positive a - c * width M h / 2)) / width M h = c := by
    field_simp [hw.ne']
    ring
  simpa only [Fintype.card_coe, heq] using hpack

/-- The enlarged annulus bins have uniformly bounded multiplicity. The
constant includes both signs, so no boundary case requires choosing the
sign of the evaluation point. -/
theorem finite_overlap_card (s a : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) (t : Finset (Bin M))
    (ht : ∀ b ∈ t, a ∈ enlargedBin s c b) :
    (t.card : ℝ) ≤ 10 * (1 + c) := by
  classical
  by_cases hempty : t = ∅
  · simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨b₀, hb₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let p : Bin M → Bool × ℤ := fun b => (b.1, b.2.1)
  let levels : Finset (Bool × ℤ) := Finset.univ.product
    (Finset.Icc (b₀.2.1 - 2) (b₀.2.1 + 2))
  have hmaps : (t : Set (Bin M)).MapsTo p levels := by
    intro b hb
    have hnear := enlargedBin_levels_near s hM hcM (ht b hb) (ht b₀ hb₀)
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr hnear⟩
  have hlevels : levels.card = 10 := by
    have hcard : ((Finset.Icc (b₀.2.1 - 2) (b₀.2.1 + 2)).card : ℤ) = 5 := by
      rw [Int.card_Icc_of_le (a := b₀.2.1 - 2) (b := b₀.2.1 + 2) (by omega)]
      omega
    have hcard' : (Finset.Icc (b₀.2.1 - 2) (b₀.2.1 + 2)).card = 5 := by
      exact_mod_cast hcard
    simp [levels, Finset.card_product, hcard']
  have hfiber (v : Bool × ℤ) :
      ((t.filter (fun b => p b = v)).card : ℝ) ≤ 1 + c := by
    let u := t.filter (fun b => p b = v)
    let slots := u.image (fun b => b.2.2)
    have hinj : (u : Set (Bin M)).InjOn (fun b => b.2.2) := by
      intro b hb b' hb' heq
      have hp := (Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hb').2.symm
      exact Prod.ext (congrArg (fun v : Bool × ℤ => v.1) hp)
        (Prod.ext (congrArg (fun v : Bool × ℤ => v.2) hp) heq)
    have hslots : slots.card = u.card := Finset.card_image_of_injOn hinj
    have h := finite_level_overlap s a hM hc v.1 v.2 slots (by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      have hpair := (Finset.mem_filter.mp hb).2
      have heq : (v.1, v.2, b.2.2) = b := by
        exact Prod.ext (congrArg (fun v : Bool × ℤ => v.1) hpair.symm)
          (Prod.ext (congrArg (fun v : Bool × ℤ => v.2) hpair.symm) rfl)
      rw [heq]
      exact ht b (Finset.mem_filter.mp hb).1)
    simpa only [hslots] using h
  calc
    (t.card : ℝ) = ∑ v ∈ levels, ((t.filter (fun b => p b = v)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    _ ≤ ∑ _v ∈ levels, (1 + c) := Finset.sum_le_sum fun v _ => hfiber v
    _ = 10 * (1 + c) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hlevels, Nat.cast_ofNat]

/-- Every finite family of the actual bin indicator functions has the
same uniform pointwise bound required by the line-counting lemma. -/
theorem finite_indicator_overlap (s a : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) (t : Finset (Bin M)) :
    (∑ b ∈ t, (enlargedBin s c b).indicator (1 : ℝ → ℝ) a) ≤ 10 * (1 + c) := by
  classical
  have h := finite_overlap_card s a hM hc hcM
    (t.filter (fun b => a ∈ enlargedBin s c b)) (by
      intro b hb
      exact (Finset.mem_filter.mp hb).2)
  convert h using 1
  simp only [Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum,
    Set.indicator_apply, Pi.one_apply]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> norm_num

def binFunction {X : Type*} (s c : ℝ) {M : ℕ} (u : X → ℝ) (b : Bin M) : X → ℝ :=
  fun x => (enlargedBin s c b).indicator (1 : ℝ → ℝ) (u x)

theorem measurable_binFunction {X : Type*} [MeasurableSpace X]
    (s c : ℝ) {M : ℕ} (u : X → ℝ) (hu : Measurable u) (b : Bin M) :
    Measurable (binFunction s c u b) :=
  (measurable_one.indicator (measurableSet_enlargedBin s c b)).comp hu

theorem binFunction_bounds {X : Type*} (s c : ℝ) {M : ℕ} (u : X → ℝ)
    (b : Bin M) (x : X) : 0 ≤ binFunction s c u b x ∧ binFunction s c u b x ≤ 1 := by
  by_cases hx : u x ∈ enlargedBin s c b <;> simp [binFunction, Set.indicator, hx]

theorem finite_binFunction_sum {X : Type*} (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) (u : X → ℝ)
    (t : Finset (Bin M)) (x : X) :
    (∑ b ∈ t, binFunction s c u b x) ≤ 10 * (1 + c) :=
  finite_indicator_overlap s (u x) hM hc hcM t

end LipschitzHilbert.AngularBins

end

end OAI
