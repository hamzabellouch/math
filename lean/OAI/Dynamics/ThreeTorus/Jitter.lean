import Mathlib

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

/-- The manuscript's distribution function, without a normalization convention
for non-probability inputs. -/
def cumulative (ρ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ x in Iic y, ρ x

lemma cumulative_sub (ρ : ℝ → ℝ) (hi : Integrable ρ) (x y : ℝ) :
    cumulative ρ y - cumulative ρ x = ∫ t in x..y, ρ t :=
  intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn

lemma cumulative_eq_primitive (ρ : ℝ → ℝ) (hi : Integrable ρ) :
    cumulative ρ = fun y => cumulative ρ 0 + ∫ t in 0..y, ρ t := by
  funext y
  linarith [cumulative_sub ρ hi 0 y]

lemma hasDerivAt_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ) (y : ℝ) :
    HasDerivAt (cumulative ρ) (ρ y) y := by
  rw [cumulative_eq_primitive ρ hi]
  convert (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 y)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (cumulative ρ 0) using 1

lemma contDiff_cumulative {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cumulative ρ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun y => (hasDerivAt_cumulative hρ.continuous hi y).differentiableAt, ?_⟩
  have hd : deriv (cumulative ρ) = ρ := funext fun y =>
    (hasDerivAt_cumulative hρ.continuous hi y).deriv
  rw [hd]
  exact hρ

lemma strictMono_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) : StrictMono (cumulative ρ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_cumulative hc hi) hp

lemma cumulative_atBot {ρ : ℝ → ℝ} :
    Tendsto (cumulative ρ) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

lemma cumulative_atTop {ρ : ℝ → ℝ} (hi : Integrable ρ) (hm : ∫ y, ρ y = 1) :
    Tendsto (cumulative ρ) atTop (𝓝 1) := by
  change Tendsto (fun y : ℝ => ∫ x in Iic y, ρ x) atTop (𝓝 1)
  simpa only [hm, id_eq] using
    (aecover_Iic (μ := (volume : Measure ℝ)) tendsto_id).integral_tendsto_of_countably_generated hi

lemma cumulative_mem_Ioo {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (y : ℝ) :
    cumulative ρ y ∈ Ioo (0 : ℝ) 1 := by
  have hs := strictMono_cumulative hc hi hp
  constructor
  · exact (hs.monotone.le_of_tendsto cumulative_atBot (y-1)).trans_lt
      (hs (by linarith : y-1 < y))
  · exact (hs (by linarith : y < y+1)).trans_le
      (hs.monotone.ge_of_tendsto (cumulative_atTop hi hm) (y+1))

lemma range_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    range (cumulative ρ) = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨y,rfl⟩
    exact cumulative_mem_Ioo hc hi hp hm y
  · intro z hz
    obtain ⟨a,ha⟩ := (cumulative_atBot.eventually (gt_mem_nhds hz.1)).exists
    obtain ⟨b,hb⟩ := ((cumulative_atTop hi hm).eventually (lt_mem_nhds hz.2)).exists
    exact intermediate_value_univ a b
      (continuous_iff_continuousAt.mpr fun y => (hasDerivAt_cumulative hc hi y).continuousAt)
      ⟨ha.le,hb.le⟩

/-- The inverse is only used on (0,1); its arbitrary values elsewhere are killed
by a smooth compactly supported cutoff. -/
def quantile (ρ : ℝ → ℝ) : ℝ → ℝ := invFun (cumulative ρ)

lemma cumulative_quantile {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    cumulative ρ (quantile ρ a) = a := by
  apply invFun_eq
  change a ∈ range (cumulative ρ)
  rw [range_cumulative hc hi hp hm]
  exact ha

lemma quantile_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (y : ℝ) :
    quantile ρ (cumulative ρ y) = y :=
  leftInverse_invFun (strictMono_cumulative hc hi hp).injective y

lemma contDiffAt_invFun_of_deriv_ne_zero {F : ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hinj : Injective F)
    {x d : ℝ} (hd : HasDerivAt F d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFun F) (F x) := by
  let e := hF.contDiffAt.toOpenPartialHomeomorph F (hd.hasFDerivAt_equiv hd0) (by simp)
  have hx : x ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = F := rfl
  have hy : F x ∈ e.target := by simpa only [he] using e.map_source hx
  have hs : e.symm (F x) = x := by simpa only [he] using e.left_inv hx
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (F x) := by
    apply e.contDiffAt_symm_deriv hd0 hy
    · simpa only [he, hs] using hd
    · simpa only [he, hs] using hF.contDiffAt (x := x)
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hy] with y hy'
  apply hinj
  have hr : F (e.symm y) = y := by simpa only [he] using e.right_inv hy'
  rw [invFun_eq ⟨e.symm y,hr⟩, hr]

lemma contDiffOn_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (quantile ρ) (Ioo (0 : ℝ) 1) := by
  intro a ha
  have hh := contDiffAt_invFun_of_deriv_ne_zero (contDiff_cumulative hρ hi)
    (strictMono_cumulative hρ.continuous hi hp).injective
    (hasDerivAt_cumulative hρ.continuous hi (quantile ρ a)) (hp _).ne'
  rw [cumulative_quantile hρ.continuous hi hp hm ha] at hh
  exact hh.contDiffWithinAt

lemma hasDerivAt_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (quantile ρ) (ρ (quantile ρ a))⁻¹ a := by
  apply HasDerivAt.of_local_left_inverse
    ((contDiffOn_quantile hρ hi hp hm).contDiffAt (isOpen_Ioo.mem_nhds ha)).continuousAt
    (hasDerivAt_cumulative hρ.continuous hi _) (hp _).ne'
  filter_upwards [isOpen_Ioo.mem_nhds ha] with y hy
  exact cumulative_quantile hρ.continuous hi hp hm hy

/-- Periodize by a locally finite sum. Unlike a raw `fract` expression this
also makes smoothness at the identified endpoints explicit. -/
def periodize (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑ᶠ k : ℤ, f (x + k)

lemma periodize_periodic (f : ℝ → ℝ) : Periodic (periodize f) 1 := by
  intro x
  have hh := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => f (x + k))
  simpa [periodize, add_comm, add_left_comm, add_assoc] using hh

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

lemma periodize_eq_on_unit {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : periodize f x = f x := by
  unfold periodize
  convert finsum_eq_single (fun k : ℤ => f (x+k)) 0 ?_ using 1
  · simp
  · intro k hk
    by_contra hn
    have hh := hs (show x+(k : ℝ) ∈ support f from hn)
    have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2, hh.1]
    have h2 : (k : ℝ) < (1 : ℝ) := by linarith [hx.1, hh.2]
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega

lemma periodize_eq_fract {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1) (x : ℝ) :
    periodize f x = f (Int.fract x) := by
  have hh := (periodize_periodic f).sub_zsmul_eq (x := x) ⌊x⌋
  have he : periodize f (Int.fract x) = periodize f x := by
    simpa only [Int.fract, zsmul_eq_mul, mul_one] using hh
  rw [← he]
  exact periodize_eq_on_unit hs ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

lemma contDiff_cutoff_quantile {ρ ξ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hs : tsupport ξ ⊆ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => ξ a * quantile ρ a) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  by_cases ha : a ∈ tsupport ξ
  · exact hξ.contDiffAt.mul ((contDiffOn_quantile hρ hi hp hm).contDiffAt
      (isOpen_Ioo.mem_nhds (hs ha)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ha] with b hb
    simp only [Pi.zero_apply] at hb
    simp only [hb, zero_mul]

/-- The two actual smooth cutoffs used by the manuscript's quantile construction. -/
structure LawCutoffs (δ : ℝ) where
  ξ : ℝ → ℝ
  ψ : ℝ → ℝ
  ξ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ
  ψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ
  ξ_compact : HasCompactSupport ξ
  ψ_compact : HasCompactSupport ψ
  ξ_support : tsupport ξ ⊆ Ioo (0 : ℝ) 1
  ψ_support : tsupport ψ ⊆ Ioo δ (1-δ)
  ξ_one : ∀ a ∈ Icc δ (1-δ), ξ a = 1
  ψ_one : ∀ a ∈ Icc (2*δ) (1-2*δ), ψ a = 1
  ψ_nonneg : ∀ a, 0 ≤ ψ a
  ψ_le_one : ∀ a, ψ a ≤ 1

def lawCutoffs (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1/8) : LawCutoffs δ := by
  let ξ : ContDiffBump (1/2 : ℝ) :=
    ⟨1/2-δ, 1/2-3*δ/4, by linarith, by linarith⟩
  let ψ : ContDiffBump (1/2 : ℝ) :=
    ⟨1/2-2*δ, 1/2-3*δ/2, by linarith, by linarith⟩
  refine ⟨ξ, ψ, ξ.contDiff, ψ.contDiff, ξ.hasCompactSupport, ψ.hasCompactSupport,
    ?_, ?_, ?_, ?_, fun _ => ψ.nonneg, fun _ => ψ.le_one⟩
  · intro a ha
    rw [ξ.tsupport_eq] at ha
    change |a-1/2| ≤ 1/2-3*δ/4 at ha
    have hh := abs_le.mp ha
    constructor <;> linarith
  · intro a ha
    rw [ψ.tsupport_eq] at ha
    change |a-1/2| ≤ 1/2-3*δ/2 at ha
    have hh := abs_le.mp ha
    constructor <;> linarith
  · intro a ha
    apply ξ.one_of_mem_closedBall
    change |a-1/2| ≤ 1/2-δ
    rw [abs_le]
    constructor <;> linarith [ha.1,ha.2]
  · intro a ha
    apply ψ.one_of_mem_closedBall
    change |a-1/2| ≤ 1/2-2*δ
    rw [abs_le]
    constructor <;> linarith [ha.1,ha.2]

def lawJitter (ρ : ℝ → ℝ) {δ : ℝ} (c : LawCutoffs δ) : ℝ → ℝ :=
  periodize (fun a => c.ξ a * quantile ρ a)

def lawPsi {δ : ℝ} (c : LawCutoffs δ) : ℝ → ℝ := periodize c.ψ

def lawDensity (ρ : ℝ → ℝ) {δ : ℝ} (c : LawCutoffs δ) (y : ℝ) : ℝ :=
  ρ y * c.ψ (cumulative ρ y) ^ 2

lemma lawJitter_smooth {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawJitter ρ c) :=
  contDiff_periodize (contDiff_cutoff_quantile hρ hi hp hm c.ξ_smooth c.ξ_support)
    c.ξ_compact.mul_right

lemma lawJitter_eq_quantile {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hδ : 0 < δ) {a : ℝ} (ha : a ∈ Icc δ (1-δ)) :
    lawJitter ρ c a = quantile ρ a := by
  rw [lawJitter, periodize_eq_on_unit, c.ξ_one a ha, one_mul]
  · exact (support_mul_subset_left _ _).trans ((subset_tsupport _).trans c.ξ_support)
  · constructor <;> linarith [ha.1,ha.2]

lemma lawJitter_deriv_pos {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Ioo δ (1-δ)) :
    HasDerivAt (lawJitter ρ c) (ρ (quantile ρ a))⁻¹ a ∧
      0 < (ρ (quantile ρ a))⁻¹ := by
  refine ⟨?_, inv_pos.mpr (hp _)⟩
  apply (hasDerivAt_quantile hρ hi hp hm
    (show a ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ha.1], by linarith [ha.2]⟩)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩

lemma lawPsi_smooth {δ : ℝ} (c : LawCutoffs δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawPsi c) :=
  contDiff_periodize c.ψ_smooth c.ψ_compact

lemma lawPsi_eq {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : lawPsi c a = c.ψ a := by
  apply periodize_eq_on_unit _ ha
  intro x hx
  have hh := c.ψ_support (subset_tsupport _ hx)
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma lawPsi_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (a : ℝ) :
    0 ≤ lawPsi c a ∧ lawPsi c a ≤ 1 := by
  have hs : support c.ψ ⊆ Ioo (0 : ℝ) 1 := fun x hx => by
    have hh := c.ψ_support (subset_tsupport _ hx)
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [lawPsi, periodize_eq_fract hs]
  exact ⟨c.ψ_nonneg _, c.ψ_le_one _⟩

lemma lawDensity_smooth {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawDensity ρ c) :=
  hρ.mul ((c.ψ_smooth.comp (contDiff_cumulative hρ hi)).pow 2)

lemma lawDensity_bounds {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hp : ∀ y, 0 < ρ y) (y : ℝ) :
    0 ≤ lawDensity ρ c y ∧ lawDensity ρ c y ≤ ρ y := by
  have hh : c.ψ (cumulative ρ y)^2 ≤ 1 := by
    nlinarith [c.ψ_nonneg (cumulative ρ y), c.ψ_le_one (cumulative ρ y)]
  exact ⟨mul_nonneg (hp y).le (sq_nonneg _), by
    simpa only [lawDensity, mul_one] using mul_le_mul_of_nonneg_left hh (hp y).le⟩

lemma lawDensity_compact {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    HasCompactSupport (lawDensity ρ c) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := quantile ρ δ) (b := quantile ρ (1-δ)))
  intro y hy
  have hn : c.ψ (cumulative ρ y) ≠ 0 := by
    intro hh
    exact hy (by simp only [lawDensity, hh, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero])
  have hh := c.ψ_support (subset_tsupport _ hn)
  have hs := strictMono_cumulative hρ.continuous hi hp
  have hleft : cumulative ρ (quantile ρ δ) = δ :=
    cumulative_quantile hρ.continuous hi hp hm ⟨hδ, by linarith⟩
  have hright : cumulative ρ (quantile ρ (1-δ)) = 1-δ :=
    cumulative_quantile hρ.continuous hi hp hm ⟨by linarith, by linarith⟩
  constructor
  · apply hs.le_iff_le.mp
    rw [hleft]
    exact hh.1.le
  · apply hs.le_iff_le.mp
    rw [hright]
    exact hh.2.le

lemma lawDensity_integrable {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) : Integrable (lawDensity ρ c) := by
  apply hi.mono' (lawDensity_smooth c hρ hi).continuous.aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (lawDensity_bounds c hp y).1]
  exact (lawDensity_bounds c hp y).2

lemma integral_lawDensity {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    (∫ y, lawDensity ρ c y) = ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
  have hh := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (hasDerivAt_cumulative hρ.continuous hi y).hasDerivWithinAt)
    (strictMono_cumulative hρ.continuous hi hp).injective.injOn (fun a => c.ψ a^2)
  rw [image_univ, range_cumulative hρ.continuous hi hp hm, Measure.restrict_univ] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [lawDensity, abs_of_pos (hp y), smul_eq_mul]

lemma integral_cutoff_lower {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    1-4*δ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
  have hs : HasCompactSupport (fun a : ℝ => c.ψ a^2) :=
    c.ψ_compact.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hi : Integrable (fun a : ℝ => c.ψ a^2) :=
    (c.ψ_smooth.continuous.pow 2).integrable_of_hasCompactSupport hs
  calc
    1-4*δ = ∫ a in Icc (2*δ) (1-2*δ), (1 : ℝ) := by
      simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
        Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-2*δ-2*δ)]
      ring
    _ = ∫ a in Icc (2*δ) (1-2*δ), c.ψ a^2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro a ha
      change 1 = c.ψ a^2
      rw [c.ψ_one a ha, one_pow]
    _ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
      apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      exact Eventually.of_forall fun a ha => ⟨by linarith [ha.1], by linarith [ha.2]⟩

lemma lawDensity_error {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ y, |ρ y - lawDensity ρ c y|) = 1-∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 ∧
      (∫ y, |ρ y - lawDensity ρ c y|) ≤ 4*δ := by
  have he : (∫ y, |ρ y - lawDensity ρ c y|) = 1-∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
    rw [integral_congr_ae (Eventually.of_forall fun y =>
      abs_of_nonneg (sub_nonneg.mpr (lawDensity_bounds c hp y).2))]
    rw [integral_sub hi (lawDensity_integrable c hρ hi hp), hm,
      integral_lawDensity c hρ hi hp hm]
  refine ⟨he, ?_⟩
  rw [he]
  linarith [integral_cutoff_lower c hδ hδ']

/-- Exact weighted pushforward, in a unit-interval representative of the circle.
The cutoff is not renormalized. -/
lemma lawDensity_pushforward {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) :
    Measure.map (lawJitter ρ c)
      ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun a => ENNReal.ofReal (c.ψ a^2))) =
      volume.withDensity (fun y => ENNReal.ofReal (lawDensity ρ c y)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  have hj : Measurable (lawJitter ρ c) := (lawJitter_smooth c hρ hi hp hm).continuous.measurable
  have hψ : Measurable (fun a : ℝ => ENNReal.ofReal (c.ψ a^2)) :=
    (c.ψ_smooth.continuous.pow 2).measurable.ennreal_ofReal
  have hc : Measurable (fun a => g (lawJitter ρ c a)) := hg.comp hj
  have hd : Measurable (fun y => ENNReal.ofReal (lawDensity ρ c y)) :=
    (lawDensity_smooth c hρ hi).continuous.measurable.ennreal_ofReal
  rw [lintegral_map hg hj, lintegral_withDensity_eq_lintegral_mul _ hψ hc,
    lintegral_withDensity_eq_lintegral_mul _ hd hg]
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun y _ => (hasDerivAt_cumulative hρ.continuous hi y).hasDerivWithinAt)
    (strictMono_cumulative hρ.continuous hi hp).injective.injOn
    (fun a => ENNReal.ofReal (c.ψ a^2) * g (lawJitter ρ c a))
  rw [image_univ, range_cumulative hρ.continuous hi hp hm, Measure.restrict_univ] at hh
  change (∫⁻ a in Ioo (0 : ℝ) 1, ENNReal.ofReal (c.ψ a^2) * g (lawJitter ρ c a)) = _
  rw [hh]
  apply lintegral_congr_ae
  filter_upwards [] with y
  change ENNReal.ofReal |ρ y| * (ENNReal.ofReal (c.ψ (cumulative ρ y)^2) *
    g (lawJitter ρ c (cumulative ρ y))) = ENNReal.ofReal (lawDensity ρ c y) * g y
  rw [lawDensity, ENNReal.ofReal_mul (hp y).le, abs_of_pos (hp y), mul_assoc]
  by_cases hz : c.ψ (cumulative ρ y) = 0
  · simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero, zero_mul, mul_zero]
  · have ha := c.ψ_support (subset_tsupport _ hz)
    rw [lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩,
      quantile_cumulative hρ.continuous hi hp y]

lemma missing_cutoff_mass {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ a in Ioo (0 : ℝ) 1, (1-c.ψ a^2)) ≤ 4*δ := by
  have hs : HasCompactSupport (fun a : ℝ => c.ψ a^2) :=
    c.ψ_compact.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hψ : Integrable (fun a : ℝ => c.ψ a^2) :=
    (c.ψ_smooth.continuous.pow 2).integrable_of_hasCompactSupport hs
  have hunit : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [integral_sub hunit hψ.integrableOn]
  have he : (∫ a in Ioo (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
  rw [he]
  linarith [integral_cutoff_lower c hδ hδ']

/-- Source Lemma `law-approx`, using a compactly supported representative ψ of
its circle cutoff on (0,1). Its smooth periodic extension is `periodize ψ`;
`periodize_eq_on_unit` proves that this does not change the weighted measure.
The output density is deliberately a subprobability, not normalized. -/
theorem realize_jitter_law (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (J ψ ρ' : ℝ → ℝ),
      0 < δ ∧ δ < 1/8 ∧ 2*δ < ε ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J ∧ Periodic J 1 ∧
      (∀ a ∈ Ioo δ (1-δ), 0 < deriv J a) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo δ (1-δ) ∧ (∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ' ∧ HasCompactSupport ρ' ∧
      (∀ y, 0 ≤ ρ' y ∧ ρ' y ≤ ρ y) ∧ Integrable ρ' ∧
      Measure.map J ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity
        (fun a => ENNReal.ofReal (ψ a^2))) =
        volume.withDensity (fun y => ENNReal.ofReal (ρ' y)) ∧
      (∫ y, |ρ y-ρ' y|) < ε ∧ (∫ a in Ioo (0 : ℝ) 1, (1-ψ a^2)) < ε := by
  obtain ⟨δ,hδ,hδb⟩ := exists_between
    (show (0 : ℝ) < min (1/8) (ε/4) from lt_min (by norm_num) (by positivity))
  have hδ' : δ < 1/8 := hδb.trans_le (min_le_left _ _)
  have hδε : 4*δ < ε := by have := hδb.trans_le (min_le_right _ _); linarith
  let c := lawCutoffs δ hδ hδ'
  refine ⟨δ,lawJitter ρ c,c.ψ,lawDensity ρ c,hδ,hδ',by linarith,
    lawJitter_smooth c hρ hi hp hm, periodize_periodic _, ?_, c.ψ_smooth,c.ψ_compact,
    c.ψ_support,fun a => ⟨c.ψ_nonneg a,c.ψ_le_one a⟩,
    lawDensity_smooth c hρ hi,lawDensity_compact c hρ hi hp hm hδ hδ',
    lawDensity_bounds c hp,lawDensity_integrable c hρ hi hp,
    lawDensity_pushforward c hρ hi hp hm hδ,
    (lawDensity_error c hρ hi hp hm hδ hδ').2.trans_lt hδε,
    (missing_cutoff_mass c hδ hδ').trans_lt hδε⟩
  intro a ha
  obtain ⟨hd,hdp⟩ := lawJitter_deriv_pos c hρ hi hp hm hδ ha
  rw [hd.deriv]
  exact hdp

end ThreeTorus

namespace ThreeTorus
open Set Function MeasureTheory
open scoped Topology

/-- A bounded smooth periodic jitter that is exactly affine on the fixed
large good arc. The cutoff and good arc do not depend on the slope. -/
def neutralJitterReal {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) : ℝ → ℝ :=
  periodize (fun a => c.ξ a*(L*a+β))

lemma neutralJitterReal_smooth {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (neutralJitterReal c L β) :=
  contDiff_periodize (c.ξ_smooth.mul (contDiff_const.mul contDiff_id |>.add contDiff_const))
    c.ξ_compact.mul_right

lemma neutralJitterReal_periodic {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    Periodic (neutralJitterReal c L β) 1 := periodize_periodic _

lemma neutralJitterReal_affine {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (L β : ℝ)
    {a : ℝ} (ha : a ∈ Icc δ (1-δ)) : neutralJitterReal c L β a = L*a+β := by
  unfold neutralJitterReal
  rw [periodize_eq_on_unit (fun x hx => c.ξ_support (subset_tsupport _ (left_ne_zero_of_mul hx)))
    (show a ∈ Icc (0:ℝ) 1 from ⟨by linarith [ha.1],by linarith [ha.2]⟩),c.ξ_one a ha,one_mul]

lemma neutralJitterReal_deriv {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (L β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo δ (1-δ)) : deriv (neutralJitterReal c L β) a = L := by
  have he : neutralJitterReal c L β =ᶠ[𝓝 a] (fun x => L*x+β) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact neutralJitterReal_affine c hδ L β ⟨hb.1.le,hb.2.le⟩
  rw [he.deriv_eq]
  simp

def neutralJitter {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) : UnitAddCircle → ℝ :=
  (neutralJitterReal_periodic c L β).lift

lemma neutralJitter_coe {δ : ℝ} (c : LawCutoffs δ) (L β a : ℝ) :
    neutralJitter c L β (a : UnitAddCircle) = neutralJitterReal c L β a := rfl

lemma continuous_neutralJitter {δ : ℝ} (c : LawCutoffs δ) (L β : ℝ) :
    Continuous (neutralJitter c L β) :=
by
  apply Continuous.quotient_lift
  exact (neutralJitterReal_smooth c L β).continuous

def neutralCircleCutoff {δ : ℝ} (c : LawCutoffs δ) : UnitAddCircle → ℝ :=
  (periodize_periodic c.ψ).lift

lemma neutralCircleCutoff_coe {δ : ℝ} (c : LawCutoffs δ) (a : ℝ) :
    neutralCircleCutoff c (a : UnitAddCircle) = lawPsi c a := rfl

lemma continuous_neutralCircleCutoff {δ : ℝ} (c : LawCutoffs δ) :
    Continuous (neutralCircleCutoff c) :=
by
  apply Continuous.quotient_lift
  exact (lawPsi_smooth c).continuous

lemma neutralCircleCutoff_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    (a : UnitAddCircle) : 0 ≤ neutralCircleCutoff c a ∧ neutralCircleCutoff c a ≤ 1 := by
  induction a using Quotient.inductionOn with
  | h a => exact lawPsi_bounds c hδ a

lemma neutralCircleCutoff_error {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ a, (1-neutralCircleCutoff c a^2) ∂AddCircle.haarAddCircle) ≤ 4*δ := by
  have he := AddCircle.integral_preimage 1 0 (fun a => (1-neutralCircleCutoff c a^2))
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he]
  change (∫ a in Ioc (0:ℝ) 1, (1-lawPsi c a^2)) ≤ 4*δ
  have hi : (∫ a in Ioc (0:ℝ) 1, (1-lawPsi c a^2)) =
      ∫ a in Ioo (0:ℝ) 1, (1-c.ψ a^2) := by
    rw [integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro a ha
    dsimp only
    rw [lawPsi_eq c hδ ⟨ha.1.le,ha.2.le⟩]
  rw [hi]
  exact missing_cutoff_mass c hδ hδ'

end ThreeTorus

end

end

end OAI
