import OAI.Probability.InvariantIsing.Cavity.CavityWeakApproximation

namespace OAI

/-! Continuous upper and lower approximations to a hard radial cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

def cavityBoundaryUpper (r B x : ℝ) : ℝ := cavityRadialCutoff 0 (r*(x-B))
def cavityBoundaryLower (r B x : ℝ) : ℝ := cavityRadialCutoff 0 (r*(x-B)+1)
def cavityBoundaryGap (r B x : ℝ) : ℝ := cavityBoundaryUpper r B x-cavityBoundaryLower r B x

lemma cavityBoundaryUpper_one {r B x : ℝ} (hr : 0 ≤ r) (hx : x ≤ B) :
    cavityBoundaryUpper r B x = 1 :=
  cavityRadialCutoff_eq_one (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hx))

lemma cavityBoundaryLower_zero {r B x : ℝ} (hr : 0 ≤ r) (hx : B ≤ x) :
    cavityBoundaryLower r B x = 0 :=
  cavityRadialCutoff_eq_zero (by
    have := mul_nonneg hr (sub_nonneg.mpr hx)
    linarith)

lemma cavityBoundaryGap_mem {r B x : ℝ} (hr : 0 ≤ r) :
    cavityBoundaryGap r B x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx : x ≤ B
  · rw [cavityBoundaryGap, cavityBoundaryUpper_one hr hx]
    have hh := cavityRadialCutoff_mem 0 (r*(x-B)+1)
    change 0 ≤ 1-cavityRadialCutoff 0 (r*(x-B)+1) ∧
      1-cavityRadialCutoff 0 (r*(x-B)+1) ≤ 1
    constructor <;> linarith [hh.1,hh.2]
  · rw [cavityBoundaryGap, cavityBoundaryLower_zero hr (le_of_not_ge hx), sub_zero]
    exact cavityRadialCutoff_mem 0 (r*(x-B))

lemma cavityBoundaryUpper_error {r B x a : ℝ} (hr : 0 ≤ r) :
    |(if x ≤ B then a else 0)-a*cavityBoundaryUpper r B x| ≤
      |a| *cavityBoundaryGap r B x := by
  by_cases hx : x ≤ B
  · rw [ite_eq_left hx, cavityBoundaryUpper_one hr hx, mul_one, sub_self, abs_zero]
    exact mul_nonneg (abs_nonneg _) (cavityBoundaryGap_mem hr).1
  · rw [ite_eq_right hx, zero_sub, abs_neg, abs_mul, cavityBoundaryGap,
      cavityBoundaryLower_zero hr (le_of_not_ge hx), sub_zero]
    change |a| * |cavityRadialCutoff 0 (r*(x-B))| ≤ |a| * cavityRadialCutoff 0 (r*(x-B))
    rw [abs_of_nonneg (cavityRadialCutoff_mem 0 (r*(x-B))).1]

lemma cavityBoundaryGap_tendsto {B x : ℝ} (hx : x ≠ B) :
    Tendsto (fun n : ℕ => cavityBoundaryGap ((n : ℝ)+1) B x) atTop (𝓝 0) := by
  have he : ∀ᶠ n : ℕ in atTop, cavityBoundaryGap ((n : ℝ)+1) B x = 0 := by
    rcases lt_or_gt_of_ne hx with hx | hx
    · have hg : 0 < B-x := sub_pos.mpr hx
      have hn : ∀ᶠ n : ℕ in atTop, 1/(B-x) < (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
      filter_upwards [hn] with n hn
      have hp : 1 < (n : ℝ)*(B-x) := (div_lt_iff₀ hg).mp hn
      have hu := cavityBoundaryUpper_one (by positivity : 0 ≤ (n : ℝ)+1) hx.le
      have hl : cavityBoundaryLower ((n : ℝ)+1) B x = 1 :=
        cavityRadialCutoff_eq_one (by nlinarith)
      rw [cavityBoundaryGap,hu,hl,sub_self]
    · have hg : 0 < x-B := sub_pos.mpr hx
      have hn : ∀ᶠ n : ℕ in atTop, 1/(x-B) < (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
      filter_upwards [hn] with n hn
      have hp : 1 < (n : ℝ)*(x-B) := (div_lt_iff₀ hg).mp hn
      have hu : cavityBoundaryUpper ((n : ℝ)+1) B x = 0 :=
        cavityRadialCutoff_eq_zero (by nlinarith)
      have hl := cavityBoundaryLower_zero (by positivity : 0 ≤ (n : ℝ)+1) hx.le
      rw [cavityBoundaryGap,hu,hl,sub_self]
  exact (tendsto_congr' he).mpr tendsto_const_nhds

end InvariantIsing

end

end OAI
