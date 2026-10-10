import OAI.Analysis.SignedDisk.LocalCancellation5

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace DiskScales

def errorGapConstant (Cs : ℝ) : ℝ :=
  2*(1+216*Cs)+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ))

def directionGapConstant (Cs κ : ℝ) : ℝ :=
  (16+4538*Cs)+4*(errorGapConstant Cs/κ)+14+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ))

lemma errorGapConstant_pos {Cs : ℝ} (hCs : 0 ≤ Cs) : 0 < errorGapConstant Cs := by
  have hden : 0 < 1-(1/2 : ℝ)^(1/10 : ℝ) := by linarith [norm_geometric_rpow_lt (by norm_num : (0 : ℝ) < 1/10)]
  unfold errorGapConstant
  positivity

lemma directionGapConstant_ge {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    16+4538*Cs ≤ directionGapConstant Cs κ := by
  have hden : 0 < 1-(1/2 : ℝ)^(1/10 : ℝ) := by linarith [norm_geometric_rpow_lt (by norm_num : (0 : ℝ) < 1/10)]
  have he : 0 ≤ errorGapConstant Cs/κ := div_nonneg (errorGapConstant_pos hCs).le hκ.le
  have hn : 0 ≤ (16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by positivity
  unfold directionGapConstant
  linarith

lemma directionGapConstant_pos {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    0 < directionGapConstant Cs κ := by
  have hh := directionGapConstant_ge hCs hκ
  linarith

lemma direction_cap_scale {Cs κ δ t : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t) :
    4*δ^(1/5 : ℝ)*((errorGapConstant Cs*t*δ^(-(1/50 : ℝ)))/κ)+14*(t*δ^(1/10 : ℝ))+
      (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤
      directionGapConstant Cs κ*t*δ^(1/10 : ℝ) := by
  have hp : δ^(1/5 : ℝ)*δ^(-(1/50 : ℝ)) ≤ δ^(1/10 : ℝ) := by
    rw [← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hb := mul_le_mul_of_nonneg_left hp
    (by exact mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (errorGapConstant_pos hCs).le hκ.le)) ht :
      0 ≤ 4*(errorGapConstant Cs/κ)*t)
  have hb' : 4*δ^(1/5 : ℝ)*((errorGapConstant Cs*t*δ^(-(1/50 : ℝ)))/κ) ≤
      4*(errorGapConstant Cs/κ)*t*δ^(1/10 : ℝ) := by
    calc
      _ = 4*(errorGapConstant Cs/κ)*t*(δ^(1/5 : ℝ)*δ^(-(1/50 : ℝ))) := by ring
      _ ≤ _ := hb
  have hnon : 0 ≤ (16+4538*Cs)*t*δ^(1/10 : ℝ) := by positivity
  calc
    _ ≤ 4*(errorGapConstant Cs/κ)*t*δ^(1/10 : ℝ)+14*(t*δ^(1/10 : ℝ))+
        (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by linarith
    _ ≤ (16+4538*Cs)*t*δ^(1/10 : ℝ)+
        (4*(errorGapConstant Cs/κ)*t*δ^(1/10 : ℝ)+14*(t*δ^(1/10 : ℝ))+
        (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := le_add_of_nonneg_left hnon
    _ = _ := by unfold directionGapConstant; ring

end DiskScales

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The full finite/infinite active-width argument at a fixed center. The cap
premise is exactly the already proved shell concentration output, not a radius
selection or a projection estimate. -/
lemma direction_sequence_point {Cs κ d t r : ℝ} {e : ℂ} (a : ConeDensity e κ)
    (b : ι → ErrorPiece Cs) (he : ‖e‖ = 1) (hκ : 0 < κ)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4) (hr : r ∈ Icc (1 : ℝ) 2)
    (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x : ℂ)
    (hM : ∀ n, (∫ y, star (y-x)*(kernel (k n) x y : ℂ)*a.density y)+
      (∑ v, ∫ y, star (y-x)*(kernel (k n) x y : ℂ)*(b v).density y) = 0)
    (hcap : ∀ j, t*(width d j)^(1/10 : ℝ) ≤ coarseMass b (width d j) (thinShell x r (width d j)) →
      (∫ y in Metric.ball x (r-width d j), ‖a.density y‖) ≤
        (errorGapConstant Cs/κ)*t*(width d j)^(-(1/50 : ℝ)) →
      ∃ z ∈ thinShell x r (width d j),
        (∫ y in thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)), ‖a.density y‖)+
        coarseMass b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) ≤
          2*(t*(width d j)^(1/10 : ℝ))) :
    max 0 (-inner ℝ e ((∫ y in Metric.ball x r, a.density y)+(∑ v, ∫ y in Metric.ball x r, (b v).density y))) ≤
      (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
      directionGapConstant Cs κ*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  classical
  have ht : 0 ≤ t := (errorPrice_nonneg b (1/100)).trans hAt
  have hd1 : d ≤ 1 := by linarith
  have hwp (i : ℕ) := width_pos hd i
  have hwq (i : ℕ) := (width_le hd.le i).trans hdq
  have hw1 (i : ℕ) := (width_le hd.le i).trans hd1
  have hrw (i : ℕ) : r+width d i ≤ 3 := by linarith [hwq i,hr.2]
  have hgpos := directionGapConstant_pos hCs hκ
  have hgle := directionGapConstant_ge hCs hκ
  let p (i : ℕ) := ∑ v, ∫ y, (kernel (k i) x y : ℂ)*(b v).density y
  let P (i : ℕ) := (∫ y, (kernel (k i) x y : ℂ)*a.density y)+p i
  let N (i : ℕ) := max 0 (-inner ℝ e (P i))
  let active (i : ℕ) := t*(width d i)^(1/10 : ℝ) ≤ coarseMass b (width d i) (thinShell x r (width d i))
  let inc (i : ℕ) := directionGapConstant Cs κ*t*(width d i)^(1/10 : ℝ)
  let B := (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)
  have hi0 (i : ℕ) : 0 ≤ inc i := mul_nonneg (mul_nonneg hgpos.le ht) (Real.rpow_nonneg (hwp i).le _)
  have hN0 (i : ℕ) : 0 ≤ N i := le_max_left _ _
  have hNerr (i : ℕ) : N i ≤ ‖p i‖ := cone_negative_le_error a he hκ.le
    (kernel_lipschitz (k i) x).continuous.aestronglyMeasurable
    (kernel_nonneg (k i) x) (kernel_le_one (k i) x) (p i)
  have hfirst (n : ℕ) (hn : ∀ i < n, ¬active i) : N n ≤ B+∑ i ∈ Finset.range n, inc i := by
    have hincr (i : ℕ) (hin : i < n) : dist (p i) (p (i+1)) ≤ inc i := by
      have hs : coarseMass b (width d i) (thinShell x r (width d i)) ≤ t*(width d i)^(1/10 : ℝ) :=
        le_of_lt (lt_of_not_ge (hn i hin))
      exact (inactive_kernel_distance b hCs hd hd1 hAt k x i hs).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgle ht) (Real.rpow_nonneg (hwp i).le _))
    have hh := dist_le_range_sum_of_dist_le n (fun {i} hin => hincr i hin)
    have hp0 : ‖p 0‖ ≤ B := by
      have h := kernel_error_bound b hCs (hwp 0) (hw1 0) (k 0) x
      simpa only [p,B,width,pow_zero,mul_one] using h
    have hp : ‖p n‖ ≤ ‖p 0‖+dist (p 0) (p n) := by
      calc
        ‖p n‖ = ‖p 0+(p n-p 0)‖ := by congr 1; abel
        _ ≤ ‖p 0‖+‖p n-p 0‖ := norm_add_le _ _
        _ = _ := by rw [dist_eq_norm,norm_sub_rev]
    linarith [hNerr n]
  have hgap (j n : ℕ) (hjn : j < n) (ha : active j)
      (hn : ∀ i, j < i → i < n → ¬active i) : N n ≤ N j+inc j := by
    by_cases hnn : N n ≤ N j
    · exact hnn.trans (le_add_of_nonneg_right (hi0 j))
    have hsmall (i : ℕ) (hji : j < i) (hin : i < n) :
        coarseMass b (width d i) (thinShell x r (width d i)) ≤ t*(width d i)^(1/10 : ℝ) :=
      le_of_lt (lt_of_not_ge (hn i hji hin))
    obtain ⟨hpj,hpn⟩ := kernel_gap_errors b hCs hd hd1 hAt k x hjn hsmall
    change ‖p j‖ ≤ errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)) at hpj
    change ‖p n‖ ≤ errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)) at hpn
    have hneg : inner ℝ e (P n) < 0 := by
      by_contra hh
      have hh' : N n = 0 := max_eq_left (by linarith [le_of_not_gt hh])
      exact hnn (by rw [hh']; exact hN0 j)
    have hmass := cone_mass_of_nonpositive a he hκ
      (kernel_lipschitz (k n) x).continuous.aestronglyMeasurable
      (kernel_nonneg (k n) x) (kernel_le_one (k n) x) hneg.le
    have hinterior : (∫ y in Metric.ball x (r-width d j), ‖a.density y‖) ≤
        (errorGapConstant Cs/κ)*t*(width d j)^(-(1/50 : ℝ)) := by
      calc
        _ ≤ ∫ y, kernel (k n) x y*‖a.density y‖ :=
          interior_mass_le_kernel a.integrable (k n) x (width_antitone hd.le hjn.le)
        _ ≤ ‖p n‖/κ := hmass
        _ ≤ (errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)))/κ := div_le_div_of_nonneg_right hpn hκ.le
        _ = _ := by ring
    obtain ⟨z,hz,hzc⟩ := hcap j ha hinterior
    have hzlo : (1 : ℝ)/2 ≤ ‖z-x‖ := by
      have hh := (abs_le.mp (show |‖z-x‖-r| ≤ width d j from hz)).1
      linarith [hr.1,hwq j]
    have hD3 : ∀ y ∈ thinShell x r (width d j), ‖y-x‖ ≤ 3 := by
      intro y hy
      have hh := (abs_le.mp (show |‖y-x‖-r| ≤ width d j from hy)).2
      linarith [hrw j]
    have hcapb : coarseMass b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) ≤
        2*(t*(width d j)^(1/10 : ℝ)) := by
      have hn : 0 ≤ ∫ y in thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)), ‖a.density y‖ :=
        integral_nonneg (fun y => norm_nonneg _)
      linarith
    have hcapa : (∫ y in thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)), ‖a.density y‖) ≤
        2*(t*(width d j)^(1/10 : ℝ)) := by
      linarith [coarseMass_nonneg b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ)))]
    let R := ∑ v, ∫ y, correction x z y*((kernel (k n) x y : ℂ)-kernel (k j) x y)*(b v).density y
    have hR : ‖R‖ ≤ (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) :=
      corrected_kernel_gap b hCs hd hdq hr hAt k x z hjn hzlo hcapb hsmall
    have hsupp : ∀ y, kernel (k n) x y-kernel (k j) x y ≠ 0 → y ∈ thinShell x r (width d j) := by
      intro y hy
      apply difference_support (k j) (k n) (width_antitone hd.le hjn.le) x y
      simpa only [← Complex.ofReal_sub,ne_eq,Complex.ofReal_eq_zero] using hy
    have hcor : P n-P j =
        (∫ y, correction x z y*((kernel (k n) x y : ℂ)-kernel (k j) x y)*a.density y)+R :=
      balanced_kernel_gap_identity b a.integrable (k j) (k n) x z (hrw j) (hrw n)
        (width_antitone hd.le hjn.le) (hM j) (hM n)
    have hh := negative_gap_cap a he hκ (Real.rpow_nonneg (hwp j).le (1/5))
      (kernel_lipschitz (k j) x).continuous.aestronglyMeasurable
      (kernel_lipschitz (k n) x).continuous.aestronglyMeasurable
      (kernel_nonneg (k j) x) (kernel_le_one (k j) x)
      (kernel_nonneg (k n) x) (kernel_le_one (k n) x)
      (measurableSet_thinShell x r (width d j)) hsupp x z hzlo hD3 hcapa hpj hpn hneg hcor
    change N n ≤ N j+4*(width d j)^(1/5 : ℝ)*((errorGapConstant Cs*t*(width d j)^(-(1/50 : ℝ)))/κ)+
      7*(2*(t*(width d j)^(1/10 : ℝ)))+‖R‖ at hh
    have hscale := direction_cap_scale hCs hκ (hwp j) (hw1 j) ht
    dsimp only [inc]
    linarith
  let Z := (∫ y in Metric.ball x r, a.density y)+(∑ v, ∫ y in Metric.ball x r, (b v).density y)
  have hlimP : Tendsto P atTop (𝓝 Z) :=
    (tendsto_kernel_pairing k (tendsto_width d) x a.integrable).add
      (tendsto_finsetSum Finset.univ (fun v _ => tendsto_kernel_pairing k (tendsto_width d) x (b v).integrable))
  have hlimN : Tendsto N atTop (𝓝 (max 0 (-inner ℝ e Z))) :=
    tendsto_const_nhds.max ((tendsto_const_nhds.inner hlimP).neg)
  have hsm : Summable inc := (summable_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)).mul_left _
  have hh := last_active_limit active N inc B _ hi0 hsm hlimN hfirst hgap
  dsimp only [inc] at hh
  rw [tsum_mul_left,tsum_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)] at hh
  convert hh using 1; dsimp only [B,Z]; ring

def directionShellBound {Cs : ℝ} (b : ι → ErrorPiece Cs) (κ t δ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
    (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*
      ENNReal.ofReal (coarseMass b δ univ)*ENNReal.ofReal (coarseMass b δ univ)) +
  (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
    ((ENNReal.ofReal (6*Real.pi)*
      ENNReal.ofReal (2*(200*δ/(δ^(1/5 : ℝ))^2)*
        (1+((errorGapConstant Cs/κ)*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)))))*
      ENNReal.ofReal (coarseMass b δ univ))

/-- Radius-independent exceptional union for the full directional sequence.
The cap property is produced by shell concentration for the actual densities. -/
theorem direction_sequence {e : ℂ} {κ Cs d t : ℝ} (a : ConeDensity e κ)
    (b : ι → ErrorPiece Cs) (he : ‖e‖ = 1) (hκ : 0 < κ)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, directionShellBound b κ t (width d n) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2,
        ∀ k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
          ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩,
        (∀ n, (∫ y, star (y-x)*(kernel (k n) x y : ℂ)*a.density y)+
          (∑ v, ∫ y, star (y-x)*(kernel (k n) x y : ℂ)*(b v).density y) = 0) →
        max 0 (-inner ℝ e ((∫ y in Metric.ball x r, a.density y)+
          (∑ v, ∫ y in Metric.ball x r, (b v).density y))) ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          directionGapConstant Cs κ*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have : IsFiniteMeasure (densityMeasure a.density) := densityMeasure_finite a.integrable
  have hd1 : d ≤ 1 := by linarith
  have hwp (n : ℕ) := width_pos hd n
  have hw1 (n : ℕ) := (width_le hd.le n).trans hd1
  have hρ (n : ℕ) : 0 < (width d n)^(1/5 : ℝ) := Real.rpow_pos_of_pos (hwp n) _
  have hρ1 (n : ℕ) : (width d n)^(1/5 : ℝ) ≤ 1 :=
    Real.rpow_le_one (hwp n).le (hw1 n) (by norm_num)
  have hs (n : ℕ) := shell_concentration (coarseMeasure b (width d n)) (densityMeasure a.density)
    (hρ n) (hρ1 n) (hwp n) (hgeom _ (hwp n) (width_le hd.le n))
    (mul_nonneg (mul_nonneg (div_nonneg (errorGapConstant_pos hCs).le hκ.le) ht.le)
      (Real.rpow_nonneg (hwp n).le (-(1/50 : ℝ))))
    (mul_pos ht (Real.rpow_pos_of_pos (hwp n) (1/10 : ℝ)))
  choose E hE hEv hEst using hs
  refine ⟨⋃ n, E n, MeasurableSet.iUnion hE,
    (measure_iUnion_le E).trans (ENNReal.tsum_le_tsum ?_), ?_⟩
  · intro n
    simpa only [directionShellBound,coarseMeasure_apply b (width d n) MeasurableSet.univ] using hEv n
  · intro x hx r hr k hM
    apply direction_sequence_point a b he hκ hCs hd hdq hr hAt k x hM
    intro j ha hi
    have hxE : x ∉ E j := fun hh => hx (mem_iUnion.mpr ⟨j,hh⟩)
    obtain ⟨z,hz,hcap⟩ := hEst j x hxE r hr
      (by rw [coarseMeasure_apply b (width d j) (measurableSet_thinShell x r (width d j))]; exact ENNReal.ofReal_le_ofReal ha)
      (by rw [densityMeasure_apply a.integrable measurableSet_ball]; exact ENNReal.ofReal_le_ofReal hi)
    refine ⟨z,hz,?_⟩
    have hD : MeasurableSet (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) :=
      (measurableSet_thinShell x r (width d j)).diff measurableSet_ball
    rw [Measure.add_apply, densityMeasure_apply a.integrable hD,
      coarseMeasure_apply b (width d j) hD, ← ENNReal.ofReal_add
        (integral_nonneg (fun _ => norm_nonneg _)) (coarseMass_nonneg b (width d j) _)] at hcap
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
      (mul_nonneg ht.le (Real.rpow_nonneg (hwp j).le _)))).mp hcap

end LocalCancellation

namespace DiskMoments
open DiskKernels

def NeighborhoodRadius (g : ℂ → ℝ) (x : ℂ) (r : ℝ) : Prop :=
  r ∈ Icc (1 : ℝ) 2 ∧ ∀ t : ℝ, 0 < t → |t-r| ≤ 1/4 →
    signedAverage g x t ≤ signedAverage g x r

lemma neighborhood_kernel {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {x : ℂ} {r δ : ℝ}
    (hr : NeighborhoodRadius g x r) (hδ : 0 < δ) (hδq : δ ≤ 1/4) :
    ∃ k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩,
      (∫ y, kernel k x y • (star (y-x)*gradient g y)) = 0 := by
  apply balanced_kernel hg x hr.1 hδ hδq
  · apply hr.2 _ (by linarith [hr.1.1])
    rw [abs_le]
    constructor <;> linarith
  · apply hr.2 _ (by linarith [hr.1.1])
    rw [abs_le]
    constructor <;> linarith

end DiskMoments

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma mixed_moment_pairing_decomposition {Cs r δ : ℝ} (b : ι → ErrorPiece Cs)
    {a : ℂ → ℂ} (ha : Integrable a) {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (x : ℂ) {h : ℂ → ℂ} (hr : r+δ ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → a y+∑ j, (b j).density y = h y) :
    (∫ y, star (y-x)*(kernel k x y : ℂ)*a y)+
      (∑ j, ∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) =
      ∫ y, kernel k x y • (star (y-x)*h y) := by
  rw [← integral_finsetSum _ (fun j _ => moment_pairing_integrable (b j) k x hr),
    ← integral_add (general_moment_integrable ha k x hr)
      (integrable_finsetSum _ (fun j _ => moment_pairing_integrable (b j) k x hr))]
  apply integral_congr_ae
  filter_upwards [hh] with y hy
  simp only [← Finset.mul_sum, ← mul_add]
  by_cases hmem : y ∈ Metric.ball x 3
  · rw [hy hmem, Complex.real_smul]
    ring
  · have hk : kernel k x y = 0 := kernel_zero k x (fun hb => hmem (lt_of_lt_of_le hb hr))
    rw [hk, Complex.ofReal_zero, mul_zero, zero_mul, zero_smul]

lemma mixed_ball_pairing_decomposition {Cs r : ℝ} (b : ι → ErrorPiece Cs)
    {a : ℂ → ℂ} (ha : Integrable a) (x : ℂ) {h : ℂ → ℂ} (hr : r ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → a y+∑ j, (b j).density y = h y) :
    (∫ y in Metric.ball x r, a y)+(∑ j, ∫ y in Metric.ball x r, (b j).density y) =
      ∫ y in Metric.ball x r, h y := by
  rw [← integral_finsetSum _ (fun j _ => (b j).integrable.integrableOn),
    ← integral_add ha.integrableOn (integrable_finsetSum _ (fun j _ => (b j).integrable.integrableOn))]
  apply setIntegral_congr_ae measurableSet_ball
  filter_upwards [hh] with y hy hyb
  exact hy (lt_of_lt_of_le hyb hr)

/-- Directional estimate at all genuine neighborhood-maximizing radii,
with only the original local density equality. -/
theorem direction_raw {e : ℂ} {κ Cs d t : ℝ} (a : ConeDensity e κ)
    (b : ι → ErrorPiece Cs) (he : ‖e‖ = 1) (hκ : 0 < κ)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, directionShellBound b κ t (width d n) ∧
      ∀ x ∉ E,
        (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
        ∀ r, NeighborhoodRadius g x r →
        max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y)) ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          directionGapConstant Cs κ*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  obtain ⟨E,hE,hEv,hEst⟩ := direction_sequence a b he hκ hCs hd hdq hgeom ht hAt
  refine ⟨E,hE,hEv,?_⟩
  intro x hx hh r hr
  choose k hk using fun n => neighborhood_kernel hg hr (width_pos hd n) ((width_le hd.le n).trans hdq)
  rw [← mixed_ball_pairing_decomposition b a.integrable x (by linarith [hr.1.2]) hh]
  apply hEst x hx r hr.1 k
  intro n
  rw [mixed_moment_pairing_decomposition b a.integrable (k n) x
    (by linarith [hr.1.2,(width_le hd.le n).trans hdq]) hh]
  exact hk n

end LocalCancellation

namespace DiskScales

lemma third_power_identity {δ : ℝ} (hδ : 0 < δ) :
    ((δ^(1/10 : ℝ))⁻¹ * (δ / (δ^(1/5 : ℝ))^2 * δ^(-(1/50 : ℝ)))) *
      (δ^(-(1/50 : ℝ))/δ^(1/10 : ℝ)) = δ^(9/25 : ℝ) := by
  rw [second_power_identity hδ, ← Real.rpow_sub hδ, ← Real.rpow_add hδ]
  norm_num

lemma direction_shell_tail_scaled {A t δ M H : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M) (hH : 0 ≤ H)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
      (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*ENNReal.ofReal M*ENNReal.ofReal M) +
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
      ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal
        (2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)))))*ENNReal.ofReal M) ≤
    ENNReal.ofReal ((1+H)*(156*(A/t)^2*δ^(14/25 : ℝ)+2424*Real.pi*(A/t)*δ^(9/25 : ℝ))) := by
  have hU : 0 < t*δ^(1/10 : ℝ) := mul_pos ht (Real.rpow_pos_of_pos hδ _)
  rw [← ENNReal.ofReal_inv_of_pos hU, ← ENNReal.ofReal_pow (inv_nonneg.mpr hU.le)]
  have hp : 0 ≤ 156*δ/δ^(1/5 : ℝ) := by positivity
  have hp' : 0 ≤ 2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ))) := by positivity
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (mul_nonneg hp hM0),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6*Real.pi by positivity),
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hp'),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hU.le),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hfirst : (t*δ^(1/10 : ℝ))⁻¹^2 * (156*δ/δ^(1/5 : ℝ)*M*M) ≤
      156*(A/t)^2*δ^(14/25 : ℝ) := by
    calc
      _ ≤ (t*δ^(1/10 : ℝ))⁻¹^2 *
          (156*δ/δ^(1/5 : ℝ)*(A*δ^(-(1/50 : ℝ)))*(A*δ^(-(1/50 : ℝ)))) := by gcongr
      _ = _ := by rw [← first_power_identity hδ]; simp only [mul_inv_rev]; ring
  have hratio : (H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)) = H*(δ^(-(1/50 : ℝ))/δ^(1/10 : ℝ)) := by
    field_simp
  have hsecond : (t*δ^(1/10 : ℝ))⁻¹ *
      (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ))))*M) ≤
      (1+H)*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
    calc
      _ ≤ (t*δ^(1/10 : ℝ))⁻¹ *
          (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2)*(1+(H*t*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ))))*(A*δ^(-(1/50 : ℝ)))) := by gcongr
      _ = 2400*Real.pi*(A/t)*δ^(12/25 : ℝ)+H*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
        rw [hratio, ← third_power_identity hδ, ← second_power_identity hδ]
        simp only [mul_inv_rev]
        ring
      _ ≤ 2400*Real.pi*(A/t)*δ^(9/25 : ℝ)+H*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num : (9/25 : ℝ) ≤ 12/25))
          (by positivity : 0 ≤ 2400*Real.pi*(A/t))) le_rfl
      _ = _ := by ring
  have hfirst' : 156*(A/t)^2*δ^(14/25 : ℝ) ≤ (1+H)*(156*(A/t)^2*δ^(14/25 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  have hextra : (1+H)*(2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) ≤
      (1+H)*(2424*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by gcongr; norm_num
  calc
    _ ≤ (1+H)*(156*(A/t)^2*δ^(14/25 : ℝ))+(1+H)*(2424*Real.pi*(A/t)*δ^(9/25 : ℝ)) :=
      add_le_add (hfirst.trans hfirst') (hsecond.trans hextra)
    _ = _ := by ring

lemma direction_start_identity {Cs κ A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (1+216*Cs)/(A/t)^(1/100 : ℝ)*A+
      directionGapConstant Cs κ*t*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) =
    t*((1+216*Cs)*(A/t)^(99/100 : ℝ)+
      directionGapConstant Cs κ*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
  have hq : 0 < A/t := div_pos hA ht
  have he : (A/t)/(A/t)^(1/100 : ℝ) = (A/t)^(99/100 : ℝ) := by
    have hh := Real.rpow_sub hq (1 : ℝ) (1/100 : ℝ)
    norm_num at hh
    exact hh.symm
  have hAt : t*(A/t) = A := by field_simp
  calc
    _ = t*((1+216*Cs)*((A/t)/(A/t)^(1/100 : ℝ))+
      directionGapConstant Cs κ*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
        rw [mul_add]
        congr 1
        · calc
            _ = (1+216*Cs)/(A/t)^(1/100 : ℝ)*(t*(A/t)) := by rw [hAt]
            _ = _ := by ring
        · ring
    _ = _ := by rw [he]

lemma exists_direction_parameters (Cs κ : ℝ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/4 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        (1+216*Cs)*δ^(99/100 : ℝ)+
          directionGapConstant Cs κ*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤ 1) := by
  obtain ⟨d,hd,hdq,hgeom⟩ := exists_admissible_width
  have ht : Tendsto (fun δ : ℝ => (1+216*Cs)*δ^(99/100 : ℝ)+
      directionGapConstant Cs κ*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) (𝓝 0) (𝓝 0) := by
    have h1 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 99/100)).tendsto 0
    have h2 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/10)).tendsto 0
    simpa using (h1.const_mul (1+216*Cs)).add ((h2.const_mul (directionGapConstant Cs κ)).div_const _)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let d₀ := min d (u/2)
  have hd0 : 0 < d₀ := lt_min hd (by linarith [hu.2])
  refine ⟨d₀,hd0,(min_le_left _ _).trans hdq,fun δ hδ hδd => hgeom δ hδ (hδd.trans (min_le_left _ _)), ?_⟩
  intro δ hδ hδd
  apply le_of_lt
  apply hs
  exact ⟨lt_trans hu.1 hδ, lt_of_le_of_lt hδd ((min_le_right _ _).trans_lt (by linarith [hu.2]))⟩

end DiskScales

end SignedDisk

end

end OAI
