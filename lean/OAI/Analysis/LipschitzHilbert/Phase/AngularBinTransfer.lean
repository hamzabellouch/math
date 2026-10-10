import OAI.Analysis.LipschitzHilbert.Phase.AngularBinOverlap

namespace OAI

/-!
# Angular-bin transfer for a separated list

These are the quantitative bin-width and enlargement calculations used
after transferring a popularity witness to a reference line in §6.
-/

noncomputable section

namespace LipschitzHilbert.AngularBins

theorem baseBin_width_le_relative (s : ℝ) {M : ℕ} (hM : 0 < M)
    {B rho a : ℝ} (hB : 0 < B) (hMB : (M : ℝ) = B ^ 2)
    {b : Bin M} (ha : a ∈ baseBin s b) (hrelative : |a - s| ≤ B * rho) :
    width M b.2.1 ≤ rho / B := by
  have hs := (baseBin_radial_bounds s hM ha).1
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    width M b.2.1 ≤ (B * rho) / M :=
      div_le_div_of_nonneg_right (hs.trans hrelative) hm.le
    _ = rho / B := by rw [hMB]; field_simp [ne_of_gt hB]

theorem baseBin_width_lt_separation (s : ℝ) {M : ℕ} (hM : 0 < M)
    {B rho a : ℝ} (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2)
    {b : Bin M} (ha : a ∈ baseBin s b) (hrelative : |a - s| ≤ B * rho) :
    width M b.2.1 < rho := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  refine (baseBin_width_le_relative s hM hB0 hMB ha hrelative).trans_lt ?_
  exact (div_lt_iff₀ hB0).mpr (by nlinarith)

/-- The bins chosen for a separated list are distinct, since their
widths are at most `rho/B` with `B>1`. -/
theorem separated_annulus_bins_injective {ι : Type*} (s : ℝ) {M : ℕ} (hM : 0 < M)
    {B rho : ℝ} (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2)
    (frequency : ι → ℝ) (bin : ι → Bin M)
    (hsep : PhaseCombinatorics.Separated frequency rho)
    (hmem : ∀ i, frequency i ∈ baseBin s (bin i))
    (hrelative : ∀ i, |frequency i - s| ≤ B * rho) : Function.Injective bin :=
  assigned_bins_injective s frequency bin hsep hmem (fun i =>
    baseBin_width_lt_separation s hM hB hrho hMB (hmem i) (hrelative i))

theorem enlargedBin_mono (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c c' : ℝ} (hcc' : c ≤ c') (b : Bin M) :
    enlargedBin s c b ⊆ enlargedBin s c' b := by
  intro a ha
  change |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
    c * width M b.2.1 / 2 at ha
  change |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
    c' * width M b.2.1 / 2
  exact ha.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcc' (width_pos hM b.2.1).le) (by norm_num))

/-- The transferred witness error is at most `(c0+1) Delta/M`.
The annulus relation `Delta<2*2^h` makes a fixed concentric enlargement
sufficient for every scale and every separated list. -/
theorem transferred_slope_mem_enlarged (s : ℝ) {M : ℕ} (hM : 0 < M)
    {c0 c a a' : ℝ} (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    {b : Bin M} (ha : a ∈ baseBin s b)
    (herror : |a' - a| ≤ (c0 + 1) * |a - s| / M) :
    a' ∈ enlargedBin s c b := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hrad := (baseBin_radial_bounds s hM ha).2.le
  have herror' : |a' - a| ≤ 2 * (c0 + 1) * width M b.2.1 := by
    calc
      |a' - a| ≤ (c0 + 1) * |a - s| / M := herror
      _ ≤ (c0 + 1) * (2 * DyadicLineGrid.scale b.2.1) / M :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrad (by linarith)) hm.le
      _ = 2 * (c0 + 1) * width M b.2.1 := by unfold width; ring
  apply enlargedBin_mono s hM hc b
  apply nearby_mem_enlargedBin s b ha
  convert herror' using 1
  ring

end LipschitzHilbert.AngularBins

end

end OAI
