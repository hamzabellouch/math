import OAI.Probability.SLE.Gauge.CoverGrid
import OAI.Probability.SLE.Gauge.CoverSchedule
import OAI.Probability.SLE.Gauge.CoverGaugeBounds
import OAI.Probability.SLE.Gauge.DenseCoverUpperReduction

namespace OAI

/-! The actual finite terminal-sausage candidates and missed cells in the
explicit-gauge cover. All selections here are deterministic at one mesh. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

abbrev DenseCandidateIndex := (ℤ × ℤ) × ℕ

def denseCandidateCenter (T : ℝ) (n : ℕ) (i : DenseCandidateIndex) : ℂ :=
  coverGridCenter (coverRadius T n) i.1

def denseCandidateRadius (T : ℝ) (i : DenseCandidateIndex) : ℝ :=
  Real.exp (-1) * coverRadius T i.2

def denseCandidateThreshold (κ T b c : ℝ) (n : ℕ) (i : DenseCandidateIndex) : ℝ :=
  b * denseCandidateRadius T i ^ dimension κ * (coverMultiplicity c n : ℝ) ^ codimension κ

def denseCandidateIndices (R T : ℝ) (K : Set ℂ) (κ b c v : ℝ)
    (n : ℕ) (γ : ℝ≥0 → ℂ) : Finset DenseCandidateIndex := by
  classical
  exact ((retainedCoverGridIndex R (coverRadius T n) K) ×ˢ coverTestWindow n).filter
    (fun i => ENNReal.ofReal (denseCandidateThreshold κ T b c n i) ≤
      wholeSausageCharge κ γ v (closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i)))

def denseFineCell (T : ℝ) (n : ℕ) (ij : ℤ × ℤ) : Set ℂ :=
  closedBall (coverGridCenter (coverRadius T n) ij) (2 * coverRadius T n)

def denseMissedCell (κ T b c v : ℝ) (n : ℕ) (ij : ℤ × ℤ)
    (γ : ℝ≥0 → ℂ) : Prop :=
  (range γ ∩ denseFineCell T n ij).Nonempty ∧
    ∀ j ∈ coverTestWindow n,
      wholeSausageCharge κ γ v
        (closedBall (denseCandidateCenter T n (ij, j)) (denseCandidateRadius T (ij, j))) <
          ENNReal.ofReal (denseCandidateThreshold κ T b c n (ij, j))

lemma denseCandidate_mem {R T κ b c v : ℝ} {K : Set ℂ} {n : ℕ}
    {γ : ℝ≥0 → ℂ} {i : DenseCandidateIndex}
    (hi : i ∈ denseCandidateIndices R T K κ b c v n γ) :
    i.1 ∈ retainedCoverGridIndex R (coverRadius T n) K ∧ i.2 ∈ coverTestWindow n ∧
      ENNReal.ofReal (denseCandidateThreshold κ T b c n i) ≤
        wholeSausageCharge κ γ v (closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i)) := by
  classical
  exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1,
    (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).2, (Finset.mem_filter.mp hi).2⟩

lemma denseCandidateRadius_pos (T : ℝ) (i : DenseCandidateIndex) :
    0 < denseCandidateRadius T i := mul_pos (Real.exp_pos _) (coverRadius_pos _ _)

lemma denseCandidateRadius_le_one {T : ℝ} (hT : 0 ≤ T) (i : DenseCandidateIndex) :
    denseCandidateRadius T i ≤ 1 := by
  have hr : coverRadius T i.2 ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hT) (Nat.cast_nonneg _)
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  calc
    _ ≤ Real.exp (-1) * 1 := mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
    _ = Real.exp (-1) := mul_one _
    _ ≤ 1 := he

/-- Every fine cell is eventually contained in every candidate disk at its
center throughout the exact window `floor(n/3)..floor(2n/3)`. -/
theorem denseFineCell_eventually_subset_candidate {T : ℝ} (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ coverTestWindow n, ∀ ij : ℤ × ℤ,
      denseFineCell T n ij ⊆
        closedBall (denseCandidateCenter T n (ij, j)) (denseCandidateRadius T (ij, j)) := by
  have hlarge : ∀ᶠ n : ℕ in atTop, 3 * (1 + Real.log 2) / T ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with n hn
  intro j hj ij z hz
  have hjn : 3 * j ≤ 2 * n := by
    have hh := (Finset.mem_Icc.mp hj).2
    omega
  have hjR : (3 : ℝ) * j ≤ 2 * n := by exact_mod_cast hjn
  have hnT := (div_le_iff₀ hT).mp hn
  have he : 2 * coverRadius T n ≤ denseCandidateRadius T (ij, j) := by
    dsimp only [coverRadius, denseCandidateRadius]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hz.trans he

/-- The missed cells are exactly the visited retained cells with no terminal
candidate; this yields a pointwise cover without a random selection rule. -/
theorem dense_candidates_and_missed_cover
    {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) {K : Set ℂ} (hK : K ⊆ closedBall 0 R)
    (κ b c : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : ℝ) (γ : ℝ≥0 → ℂ) z, z ∈ K ∩ range γ →
      (∃ i ∈ denseCandidateIndices R T K κ b c v n γ,
        z ∈ closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i)) ∨
      ∃ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
        denseMissedCell κ T b c v n ij γ ∧ z ∈ denseFineCell T n ij := by
  classical
  filter_upwards [denseFineCell_eventually_subset_candidate hT] with n hn
  intro v γ z hz
  obtain ⟨ij, hij, hzcell⟩ := mem_iUnion₂.mp
    (retainedCoverGrid_covers hR (coverRadius_pos T n) hK hz.1)
  by_cases hs : ∃ j ∈ coverTestWindow n,
      ENNReal.ofReal (denseCandidateThreshold κ T b c n (ij, j)) ≤
        wholeSausageCharge κ γ v
          (closedBall (denseCandidateCenter T n (ij, j)) (denseCandidateRadius T (ij, j)))
  · obtain ⟨j, hj, hmass⟩ := hs
    exact Or.inl ⟨(ij, j), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hij, hj⟩, hmass⟩, hn j hj ij hzcell⟩
  · refine Or.inr ⟨ij, hij, ⟨⟨z, hz.2, hzcell⟩, ?_⟩, hzcell⟩
    intro j hj
    exact lt_of_not_ge (fun hmass => hs ⟨j, hj, hmass⟩)

lemma denseCandidate_disk_subset {R T κ b c v : ℝ} (hT : 0 ≤ T) {K : Set ℂ}
    (hK : K ⊆ closedBall 0 R) {n : ℕ} {γ : ℝ≥0 → ℂ} {i : DenseCandidateIndex}
    (hi : i ∈ denseCandidateIndices R T K κ b c v n γ) :
    closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i) ⊆ closedBall 0 (R + 3) := by
  have hheight : ∀ z ∈ K, -R ≤ z.im := by
    intro z hz
    have hn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hK hz
    have him := (Complex.abs_im_le_norm z).trans hn
    exact (abs_le.mp him).1
  have hcenter := (retainedCoverGrid_center_bounds hK hheight (denseCandidate_mem hi).1).1
  have hrn : coverRadius T n ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hp := mul_nonneg hT (Nat.cast_nonneg n)
    linarith)
  intro z hz
  have ht := dist_triangle z (denseCandidateCenter T n i) 0
  have hr := denseCandidateRadius_le_one hT i
  change dist z 0 ≤ R + 3
  change dist z (denseCandidateCenter T n i) ≤ denseCandidateRadius T i at hz
  change ‖denseCandidateCenter T n i‖ ≤ R + 2 * coverRadius T n at hcenter
  simp only [dist_zero_right] at ht ⊢
  linarith

def denseCoverDiameter (T : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (max (8 * Real.exp (-1) * coverRadius T (n / 3)) (4 * coverRadius T n))

lemma denseCoverDiameter_tendsto_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (denseCoverDiameter T) atTop (𝓝 0) :=
  cover_diameter_tendsto_zero hT (8 * Real.exp (-1)) 4

lemma denseCandidate_enlarged_diameter {R T κ b c v : ℝ} (hT : 0 ≤ T) {K : Set ℂ}
    {n : ℕ} {γ : ℝ≥0 → ℂ} {i : DenseCandidateIndex}
    (hi : i ∈ denseCandidateIndices R T K κ b c v n γ) :
    ediam (closedBall (denseCandidateCenter T n i) (4 * denseCandidateRadius T i)) ≤
      denseCoverDiameter T n := by
  apply (ediam_le_of_forall_dist_le ?_).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  intro x hx y hy
  have ht := dist_triangle x (denseCandidateCenter T n i) y
  have hx' : dist x (denseCandidateCenter T n i) ≤ 4 * denseCandidateRadius T i := hx
  have hy' : dist (denseCandidateCenter T n i) y ≤ 4 * denseCandidateRadius T i := by
    change dist y (denseCandidateCenter T n i) ≤ 4 * denseCandidateRadius T i at hy
    simpa only [dist_comm] using hy
  have hr := coverRadius_window_upper hT (denseCandidate_mem hi).2.1
  have he := Real.exp_pos (-1)
  dsimp only [denseCandidateRadius] at hx' hy'
  nlinarith

lemma denseFineCell_diameter (T : ℝ) (n : ℕ) (ij : ℤ × ℤ) :
    ediam (denseFineCell T n ij) ≤ denseCoverDiameter T n :=
  (coverGrid_cell_diameter (coverRadius_pos T n) ij).trans
    (ENNReal.ofReal_le_ofReal (le_max_right _ _))


local instance denseCandidatePathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance denseCandidatePathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem denseMissedCell_measurable
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (κ T b c v : ℝ) (n : ℕ) (ij : ℤ × ℤ) :
    MeasurableSet {ω | denseMissedCell κ T b c v n ij (f ω)} := by
  have hm := measurableSet_visited_without_candidate f hf κ v (coverTestWindow n)
    (fun j => closedBall (denseCandidateCenter T n (ij, j)) (denseCandidateRadius T (ij, j)))
    (fun j => denseCandidateThreshold κ T b c n (ij, j))
    (Q := denseFineCell T n ij) isClosed_closedBall
  convert hm using 1
  ext ω
  simp only [denseMissedCell, mem_ofPred_eq, Set.Nonempty, mem_inter_iff, mem_range]
  constructor
  · rintro ⟨⟨z, ⟨t, rfl⟩, hz⟩, hh⟩
    exact ⟨⟨t, hz⟩, hh⟩
  · rintro ⟨⟨t, ht⟩, hh⟩
    exact ⟨⟨f ω t, ⟨t, rfl⟩, ht⟩, hh⟩

lemma extendedGauge_closedBall_le {h : ℝ → ℝ} (hh : IsGauge h)
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    extendedGauge h (ediam (closedBall z r)) ≤ ENNReal.ofReal (h (2 * r)) := by
  have hd : ediam (closedBall z r) ≤ ENNReal.ofReal (2 * r) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' : dist x z ≤ r := hx
    have hy' : dist z y ≤ r := by
      change dist y z ≤ r at hy
      simpa only [dist_comm] using hy
    exact (dist_triangle x z y).trans (by linarith)
  have hdR : (ediam (closedBall z r)).toReal ≤ 2 * r := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hd).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  exact ENNReal.ofReal_le_ofReal
    (hh.monotoneOn ENNReal.toReal_nonneg (show 0 ≤ 2 * r by positivity) hdR)

/-- The prescribed integer multiplicity pays the logarithmic correction of
all selected disks, uniformly throughout the window. -/
theorem denseCandidate_eventual_gauge_charge
    {κ T b c : ℝ} (hκ8 : κ < 8) (hT : 0 < T) (hb : 0 < b) (hc : 0 < c)
    {h : ℝ → ℝ} (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (R : ℝ) (K : Set ℂ) (v : ℝ) (γ : ℝ≥0 → ℂ) i,
        i ∈ denseCandidateIndices R T K κ b c v n γ →
        extendedGauge h (ediam (closedBall (denseCandidateCenter T n i)
          (4 * denseCandidateRadius T i))) ≤
            (C : ℝ≥0∞) * wholeSausageCharge κ γ v
              (closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i)) := by
  have hp : 0 ≤ codimension κ := by dsimp [codimension, dimension]; linarith
  obtain ⟨A, hA, hbound⟩ := CoverGaugeBounds.eventual_window_bound hκ8
    (mul_pos (by norm_num : (0 : ℝ) < 8) (Real.exp_pos (-1))) hT hf
  let L := b * (Real.exp (-1)) ^ dimension κ * (c / 2) ^ codimension κ
  have hL : 0 < L := by dsimp only [L]; positivity
  let C : ℝ≥0 := ⟨A / L, (div_pos hA hL).le⟩
  refine ⟨C, div_pos hA hL, ?_⟩
  filter_upwards [hbound, coverMultiplicity_mass_lower hc hp,
    eventually_ge_atTop (12 : ℕ)] with n hn hmass hn12
  intro R K v γ i hi
  have hj := (denseCandidate_mem hi).2.1
  have hjlow : (n : ℝ) / 4 ≤ (i.2 : ℝ) := by
    have hnI : n / 3 ≤ i.2 := (Finset.mem_Icc.mp hj).1
    have hfour : n ≤ 4 * i.2 := by omega
    have hfourR : (n : ℝ) ≤ 4 * i.2 := by exact_mod_cast hfour
    linarith
  have hjhigh : i.2 ≤ n := by
    have hnI := (Finset.mem_Icc.mp hj).2
    omega
  have hg := hn i.2 hjlow hjhigh
  change h (8 * Real.exp (-1) * coverRadius T i.2) ≤
    A * coverRadius T i.2 ^ dimension κ * (Real.log (n : ℝ)) ^ (codimension κ / 2) at hg
  have hscale : L * (coverRadius T i.2 ^ dimension κ *
      (Real.log (n : ℝ)) ^ (codimension κ / 2)) ≤ denseCandidateThreshold κ T b c n i := by
    unfold denseCandidateThreshold denseCandidateRadius
    rw [Real.mul_rpow (Real.exp_pos _).le (coverRadius_pos _ _).le]
    calc
      _ = (b * Real.exp (-1) ^ dimension κ * coverRadius T i.2 ^ dimension κ) *
          ((c / 2) ^ codimension κ * (Real.log (n : ℝ)) ^ (codimension κ / 2)) := by
        dsimp only [L]
        ring
      _ ≤ (b * Real.exp (-1) ^ dimension κ * coverRadius T i.2 ^ dimension κ) *
          (coverMultiplicity c n : ℝ) ^ codimension κ :=
        mul_le_mul_of_nonneg_left hmass
          (mul_nonneg (mul_nonneg hb.le (Real.rpow_nonneg (Real.exp_pos _).le _))
            (Real.rpow_nonneg (coverRadius_pos _ _).le _))
      _ = _ := by ring
  have hreal : h (8 * denseCandidateRadius T i) ≤ (C : ℝ) * denseCandidateThreshold κ T b c n i := by
    calc
      _ = h (8 * Real.exp (-1) * coverRadius T i.2) := by congr 1; simp only [denseCandidateRadius]; ring
      _ ≤ A * coverRadius T i.2 ^ dimension κ * (Real.log (n : ℝ)) ^ (codimension κ / 2) := hg
      _ = (C : ℝ) * (L * (coverRadius T i.2 ^ dimension κ *
          (Real.log (n : ℝ)) ^ (codimension κ / 2))) := by
        change _ = A / L * _
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale C.2
  calc
    _ ≤ ENNReal.ofReal (h (8 * denseCandidateRadius T i)) := by
      have he : 2 * (4 * denseCandidateRadius T i) = 8 * denseCandidateRadius T i := by ring
      simpa only [he] using extendedGauge_closedBall_le hh (denseCandidateCenter T n i)
        (r := 4 * denseCandidateRadius T i) (by positivity [denseCandidateRadius_pos T i])
    _ ≤ ENNReal.ofReal ((C : ℝ) * denseCandidateThreshold κ T b c n i) := ENNReal.ofReal_le_ofReal hreal
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (denseCandidateThreshold κ T b c n i) := by
      have hC : ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
      exact (ENNReal.ofReal_mul C.2).trans (congrArg
        (fun t : ℝ≥0∞ => t * ENNReal.ofReal (denseCandidateThreshold κ T b c n i)) hC)
    _ ≤ _ := mul_le_mul' le_rfl (denseCandidate_mem hi).2.2

/-- The cost of each fine cleanup cell has the matching explicit-gauge
factor, independent of the cell center. -/
theorem denseFineCell_eventual_gauge_bound
    {κ T : ℝ} (hκ8 : κ < 8) (hT : 0 < T)
    {h : ℝ → ℝ} (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ ij : ℤ × ℤ,
      extendedGauge h (ediam (denseFineCell T n ij)) ≤
        ENNReal.ofReal (A * coverRadius T n ^ dimension κ *
          (Real.log (n : ℝ)) ^ (codimension κ / 2)) := by
  obtain ⟨A, hA, hbound⟩ := CoverGaugeBounds.eventual_window_bound hκ8 (by norm_num : (0 : ℝ) < 4) hT hf
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound] with n hn
  intro ij
  have hg := hn n (by have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) le_rfl
  change h (4 * coverRadius T n) ≤ _ at hg
  have he : 2 * (2 * coverRadius T n) = 4 * coverRadius T n := by ring
  have hd : extendedGauge h (ediam (denseFineCell T n ij)) ≤
      ENNReal.ofReal (h (4 * coverRadius T n)) := by
    simpa only [denseFineCell, he] using
      (extendedGauge_closedBall_le hh (coverGridCenter (coverRadius T n) ij)
        (r := 2 * coverRadius T n) (by positivity [coverRadius_pos T n]))
  exact hd.trans (ENNReal.ofReal_le_ofReal hg)

/-- The six concrete geometric hypotheses of the expected-cover reduction,
with one constant and one sufficiently late cutoff for every path and mesh. -/
theorem dense_candidate_cover_geometry
    {κ R T b c : ℝ} (hκ8 : κ < 8) (hR : 0 ≤ R) (hT : 0 < T)
    (hb : 0 < b) (hc : 0 < c) {K : Set ℂ} (hK : K ⊆ closedBall 0 R)
    {h : ℝ → ℝ} (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ (v : ℝ) (γ : ℝ≥0 → ℂ),
      (∀ i ∈ denseCandidateIndices R T K κ b c v n γ, denseCandidateRadius T i ≤ R + 3) ∧
      (∀ i ∈ denseCandidateIndices R T K κ b c v n γ,
        closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i) ⊆ closedBall 0 (R + 3)) ∧
      (∀ i ∈ denseCandidateIndices R T K κ b c v n γ,
        extendedGauge h (ediam (closedBall (denseCandidateCenter T n i) (4 * denseCandidateRadius T i))) ≤
          (C : ℝ≥0∞) * wholeSausageCharge κ γ v
            (closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i))) ∧
      (∀ i ∈ denseCandidateIndices R T K κ b c v n γ,
        ediam (closedBall (denseCandidateCenter T n i) (4 * denseCandidateRadius T i)) ≤ denseCoverDiameter T n) ∧
      (∀ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
        ediam (denseFineCell T n ij) ≤ denseCoverDiameter T n) ∧
      (∀ z ∈ K ∩ range γ,
        (∃ i ∈ denseCandidateIndices R T K κ b c v n γ,
          z ∈ closedBall (denseCandidateCenter T n i) (denseCandidateRadius T i)) ∨
        ∃ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
          denseMissedCell κ T b c v n ij γ ∧ z ∈ denseFineCell T n ij) := by
  obtain ⟨C, hC, hcharge⟩ := denseCandidate_eventual_gauge_charge hκ8 hT hb hc hh hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcharge, dense_candidates_and_missed_cover hR hT hK κ b c] with n hn hcover
  intro v γ
  refine ⟨?_, ?_, hn R K v γ, ?_, ?_, hcover v γ⟩
  · intro i _
    exact (denseCandidateRadius_le_one hT.le i).trans (by linarith)
  · exact fun _ hi => denseCandidate_disk_subset hT.le hK hi
  · exact fun _ hi => denseCandidate_enlarged_diameter hT.le hi
  · exact fun ij _ => denseFineCell_diameter T n ij

end SLEExactGauge

end

end OAI
