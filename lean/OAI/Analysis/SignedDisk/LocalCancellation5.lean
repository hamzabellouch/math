import OAI.Analysis.SignedDisk.LocalCancellation4

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

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales

lemma cone_negative_le_error {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 ≤ κ) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) (p : ℂ) :
    max 0 (-inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p)) ≤ ‖p‖ := by
  have hh := cone_pairing a hK hK0 hK1
  have hi : 0 ≤ ∫ y, K y*‖a.density y‖ := integral_nonneg (fun y => mul_nonneg (hK0 y) (norm_nonneg _))
  have hproj : 0 ≤ inner ℝ e (∫ y, (K y : ℂ)*a.density y) := (mul_nonneg hκ hi).trans hh
  rw [inner_add_right]
  exact max_le (norm_nonneg _) (by linarith [(abs_le.mp (inner_unit_bound (p := p) he)).1])

lemma general_moment_integrable {a : ℂ → ℂ} (ha : Integrable a)
    {r δ : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x : ℂ) (hr : r+δ ≤ 3) :
    Integrable (fun y => star (y-x)*(kernel k x y : ℂ)*a y) := by
  apply integrable_bounded_pairing ha
    ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
      (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply position_bound (complex_kernel_bound k x) x (by norm_num : (0 : ℝ) ≤ 3)
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh, Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball, dist_eq_norm] using hyb).le.trans hr

lemma correcting_pairing {a F : ℂ → ℂ} (ha : Integrable a)
    (hF : AEStronglyMeasurable F) (hFb : ∀ y, ‖F y‖ ≤ 1) (x z : ℂ)
    (hsupp : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3) :
    (∫ y, correction x z y*F y*a y) = (∫ y, F y*a y) -
      (star (z-x))⁻¹*(∫ y, star (y-x)*F y*a y) := by
  have hi := integrable_bounded_pairing ha hF hFb
  have him : Integrable (fun y => star (y-x)*F y*a y) :=
    integrable_bounded_pairing ha
      ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).aestronglyMeasurable.mul hF)
      (position_bound hFb x (by norm_num : (0 : ℝ) ≤ 3) hsupp)
  have he : (fun y => correction x z y*F y*a y) =
      fun y => F y*a y-(star (z-x))⁻¹*(star (y-x)*F y*a y) := by
    ext y
    simp only [correction,div_eq_mul_inv]
    ring
  rw [he,integral_sub hi (him.const_mul _),integral_const_mul]

lemma general_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {u v u' v' : ℝ} {M N : ℝ≥0} (k : RadiusDensity u v M) (l : RadiusDensity u' v' N) (x : ℂ) :
    (∫ y, (kernel l x y : ℂ)*a y)-(∫ y, (kernel k x y : ℂ)*a y) =
      ∫ y, ((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub
    (integrable_bounded_pairing ha (complex_kernel_lipschitz l x).continuous.aestronglyMeasurable (complex_kernel_bound l x))
    (integrable_bounded_pairing ha (complex_kernel_lipschitz k x).continuous.aestronglyMeasurable (complex_kernel_bound k x))]
  congr 1
  ext y
  ring

lemma corrected_kernel_integrable {a : ℂ → ℂ} (ha : Integrable a)
    {r δ : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x z : ℂ)
    (hr : r+δ ≤ 3) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) :
    Integrable (fun y => correction x z y*(kernel k x y : ℂ)*a y) := by
  apply integrable_bounded_pairing ha
    ((by unfold correction; fun_prop : Continuous (correction x z)).mul (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply correction_kernel_bound (complex_kernel_bound k x) x z hz
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh,Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball,dist_eq_norm] using hyb).le.trans hr

lemma corrected_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M N : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (l : RadiusDensity (r-ε) (r+ε) N) (x z : ℂ)
    (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) :
    (∫ y, correction x z y*(kernel l x y : ℂ)*a y)-
      (∫ y, correction x z y*(kernel k x y : ℂ)*a y) =
      ∫ y, correction x z y*((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub (corrected_kernel_integrable ha l x z hrε hz)
    (corrected_kernel_integrable ha k x z hrδ hz)]
  congr 1
  ext y
  ring

lemma interior_mass_le_kernel {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-ε) (r+ε) M) (x : ℂ) (hεδ : ε ≤ δ) :
    (∫ y in Metric.ball x (r-δ), ‖a y‖) ≤ ∫ y, kernel k x y*‖a y‖ := by
  rw [← integral_indicator measurableSet_ball]
  apply integral_mono_ae (ha.norm.indicator measurableSet_ball)
    (ha.norm.bdd_mul (kernel_lipschitz k x).continuous.aestronglyMeasurable
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg k x y)]; exact kernel_le_one k x y)))
  filter_upwards with y
  by_cases hy : y ∈ Metric.ball x (r-δ)
  · have hk : kernel k x y = 1 := kernel_one k x (by
      simp only [Metric.mem_ball] at hy ⊢
      linarith)
    simp only [indicator_of_mem hy,hk,one_mul,le_refl]
  · simp only [indicator_of_notMem hy]
    exact mul_nonneg (kernel_nonneg k x y) (norm_nonneg _)

end LocalCancellation

namespace DiskScales

lemma width_add (d : ℝ) (j n : ℕ) : width d (j+n) = width (width d j) n := by
  simp only [width,pow_add]
  ring

lemma sum_width_tail {d p : ℝ} (hd : 0 ≤ d) (hp : 0 < p) (j n : ℕ) :
    (∑ i ∈ Finset.Ico j n, (width d i)^p) ≤ (width d j)^p/(1-(1/2 : ℝ)^p) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hs : Summable (fun i => (width (width d j) i)^p) :=
    summable_width_rpow (by dsimp [width]; positivity) hp
  have hh := hs.sum_le_tsum (Finset.range (n-j)) (fun i _ => Real.rpow_nonneg (by dsimp [width]; positivity) p)
  simp_rw [width_add]
  exact hh.trans_eq (tsum_width_rpow (by dsimp [width]; positivity) hp)

lemma dist_width_tail {α : Type*} [PseudoMetricSpace α] {d p C : ℝ} (hd : 0 ≤ d)
    (hp : 0 < p) (hC : 0 ≤ C) {f : ℕ → α} {j n : ℕ} (hjn : j ≤ n)
    (hincr : ∀ i, j ≤ i → i < n → dist (f i) (f (i+1)) ≤ C*(width d i)^p) :
    dist (f j) (f n) ≤ C*(width d j)^p/(1-(1/2 : ℝ)^p) := by
  have hh := dist_le_Ico_sum_of_dist_le hjn (fun {i} hi hin => hincr i hi hin)
  rw [← Finset.mul_sum] at hh
  exact hh.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (sum_width_tail hd hp j n) hC)

end DiskScales

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma moment_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M N : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (l : RadiusDensity (r-ε) (r+ε) N) (x : ℂ) (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3) :
    (∫ y, star (y-x)*(kernel l x y : ℂ)*a y)-
      (∫ y, star (y-x)*(kernel k x y : ℂ)*a y) =
      ∫ y, star (y-x)*((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub (general_moment_integrable ha l x hrε) (general_moment_integrable ha k x hrδ)]
  congr 1
  ext y
  ring

lemma total_correction {Cs : ℝ} (b : ι → ErrorPiece Cs) {a F : ℂ → ℂ} (ha : Integrable a)
    (hF : AEStronglyMeasurable F) (hFb : ∀ y, ‖F y‖ ≤ 1) (x z : ℂ)
    (hsupp : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3)
    (hzero : (∫ y, star (y-x)*F y*a y)+(∑ j, ∫ y, star (y-x)*F y*(b j).density y) = 0) :
    (∫ y, F y*a y)+(∑ j, ∫ y, F y*(b j).density y) =
      (∫ y, correction x z y*F y*a y)+(∑ j, ∫ y, correction x z y*F y*(b j).density y) := by
  rw [correcting_pairing ha hF hFb x z hsupp]
  simp_rw [correcting_pairing (b _).integrable hF hFb x z hsupp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination (star (z-x))⁻¹*hzero

lemma balanced_kernel_gap_identity {Cs : ℝ} (b : ι → ErrorPiece Cs) {a : ℂ → ℂ}
    (ha : Integrable a) {r δ ε : ℝ} {M N : ℝ≥0}
    (k : RadiusDensity (r-δ) (r+δ) M) (l : RadiusDensity (r-ε) (r+ε) N)
    (x z : ℂ) (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3) (hεδ : ε ≤ δ)
    (hMk : (∫ y, star (y-x)*(kernel k x y : ℂ)*a y)+
      (∑ j, ∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) = 0)
    (hMl : (∫ y, star (y-x)*(kernel l x y : ℂ)*a y)+
      (∑ j, ∫ y, star (y-x)*(kernel l x y : ℂ)*(b j).density y) = 0) :
    ((∫ y, (kernel l x y : ℂ)*a y)+(∑ j, ∫ y, (kernel l x y : ℂ)*(b j).density y))-
      ((∫ y, (kernel k x y : ℂ)*a y)+(∑ j, ∫ y, (kernel k x y : ℂ)*(b j).density y)) =
    (∫ y, correction x z y*((kernel l x y : ℂ)-kernel k x y)*a y)+
      (∑ j, ∫ y, correction x z y*((kernel l x y : ℂ)-kernel k x y)*(b j).density y) := by
  let F (y : ℂ) := (kernel l x y : ℂ)-kernel k x y
  have hsupp : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3 := by
    intro y hy
    have hh := (abs_le.mp (difference_support k l hεδ x y hy)).2
    linarith
  have hzero : (∫ y, star (y-x)*F y*a y)+
      (∑ j, ∫ y, star (y-x)*F y*(b j).density y) = 0 := by
    simp_rw [F, ← moment_kernel_pairing_sub ha k l x hrδ hrε,
      ← moment_kernel_pairing_sub (b _).integrable k l x hrδ hrε]
    rw [Finset.sum_sub_distrib]
    linear_combination hMl-hMk
  have hcorr := total_correction b ha
    ((complex_kernel_lipschitz l x).continuous.sub (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
    (difference_bound k l x) x z hsupp hzero
  calc
    _ = ((∫ y, (kernel l x y : ℂ)*a y)-(∫ y, (kernel k x y : ℂ)*a y))+
        ((∑ j, ∫ y, (kernel l x y : ℂ)*(b j).density y)-
          (∑ j, ∫ y, (kernel k x y : ℂ)*(b j).density y)) := by abel
    _ = (∫ y, F y*a y)+(∑ j, ∫ y, F y*(b j).density y) := by
      rw [general_kernel_pairing_sub ha k l x, ← Finset.sum_sub_distrib]
      simp_rw [general_kernel_pairing_sub (b _).integrable k l x]
      rfl
    _ = _ := hcorr

lemma kernel_error_bound {Cs δ r : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩) (x : ℂ) :
    ‖∑ j, ∫ y, (kernel k x y : ℂ)*(b j).density y‖ ≤
      (1+216*Cs)/δ^(1/100 : ℝ)*errorPrice b (1/100) := by
  exact total_pairing_discount b (by norm_num : (0 : ℝ) ≤ 1/100)
    (by norm_num : (1/100 : ℝ) ≤ 1) hδ hδ1 (by linarith)
    (complex_kernel_lipschitz k x) (complex_kernel_bound k x)
    (by change (216/δ)*Cs ≤ (1+216*Cs)/δ
        apply (le_div_iff₀ hδ).mpr
        field_simp [hδ.ne']
        linarith)

lemma coarse_bound_scaled {Cs δ : ℝ} (b : ι → ErrorPiece Cs) (hδ : 0 < δ) :
    coarseMass b δ univ ≤ errorPrice b (1/100)*δ^(-(1/50 : ℝ)) := by
  have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hδ
  norm_num at hh
  simpa only [Real.rpow_neg hδ.le,div_eq_mul_inv] using hh

lemma scaled_ordinary_inactive {Cs δ t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D)
    (hL : (L : ℝ) ≤ 648/δ) (hsmall : coarseMass b δ D ≤ t*δ^(1/10 : ℝ)) :
    ‖∑ j, ∫ y, F y*(b j).density y‖ ≤ (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have hi := increment_bound b hCs (by norm_num : (1/100 : ℝ) ≤ 1) hδ.le hδ1 hF hD hFb hFD
  have hs := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt hδ hδ1 (coarse_bound_scaled b hδ) hL
  have hM : 0 ≤ 2*δ^(1/5 : ℝ)*coarseMass b δ univ := by
    exact mul_nonneg (by positivity) (coarseMass_nonneg b δ univ)
  have hC : 0 ≤ 2*(3*(L : ℝ)+1)*Cs*δ^(2*(1-(1/100 : ℝ)))*errorPrice b (1/100) := by
    exact mul_nonneg (by positivity) (errorPrice_nonneg b (1/100))
  have hU : 0 ≤ t*δ^(1/10 : ℝ) := mul_nonneg ((errorPrice_nonneg b (1/100)).trans hAt) (by positivity)
  nlinarith

lemma scaled_corrected_inactive {Cs δ t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D)
    (hL : (L : ℝ) ≤ 648/δ) (hsmall : coarseMass b δ D ≤ t*δ^(1/10 : ℝ))
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ j, ∫ y, correction x z y*F y*(b j).density y‖ ≤
      (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have hi := corrected_inactive_bound b hCs (by norm_num : (1/100 : ℝ) ≤ 1) hδ.le hδ1 hF hD hFb hFD x z hz hD3
  have hs := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt hδ hδ1 (coarse_bound_scaled b hδ) hL
  have hM : 0 ≤ 2*δ^(1/5 : ℝ)*coarseMass b δ univ :=
    mul_nonneg (by positivity) (coarseMass_nonneg b δ univ)
  have hU : 0 ≤ t*δ^(1/10 : ℝ) := mul_nonneg ((errorPrice_nonneg b (1/100)).trans hAt) (by positivity)
  nlinarith

lemma scaled_corrected_active {Cs δ t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D)
    (hL : (L : ℝ) ≤ 648/δ) (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3)
    (hcap : coarseMass b δ (D \ Metric.ball z (δ^(1/5 : ℝ))) ≤ 2*(t*δ^(1/10 : ℝ))) :
    ‖∑ j, ∫ y, correction x z y*F y*(b j).density y‖ ≤
      (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have hi := corrected_error_bound b hCs (by norm_num : (1/100 : ℝ) ≤ 1) hδ.le hδ1
    (Real.rpow_nonneg hδ.le (1/5)) hF hD hFb hFD x z hz hD3
  have hs := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt hδ hδ1 (coarse_bound_scaled b hδ) hL
  linarith

end LocalCancellation

namespace DiskScales

lemma successor_discount {δ : ℝ} (hδ : 0 < δ) :
    (δ/2)⁻¹^(1/100 : ℝ) ≤ 2*δ⁻¹^(1/100 : ℝ) := by
  rw [inv_div,Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le,Real.inv_rpow hδ.le]
  have hh : (2 : ℝ)^(1/100 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1/100 : ℝ) ≤ 1)
  exact div_le_div_of_nonneg_right hh (by positivity)

lemma geometric_den_pos {p : ℝ} (hp : 0 < p) : 0 < 1-(1/2 : ℝ)^p := by
  linarith [norm_geometric_rpow_lt hp]

lemma coarse_error_scale {Cs A t δ : ℝ} (hCs : 0 ≤ Cs) (hA : 0 ≤ A)
    (hAt : A ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2*((1+216*Cs)/δ^(1/100 : ℝ)*A) +
      (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤
    (2*(1+216*Cs)+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)))*t*δ^(-(1/50 : ℝ)) := by
  have ht : 0 ≤ t := hA.trans hAt
  have hp1 : δ^(-(1/100 : ℝ)) ≤ δ^(-(1/50 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hp2 : δ^(1/10 : ℝ) ≤ δ^(-(1/50 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have h1 : 2*((1+216*Cs)/δ^(1/100 : ℝ)*A) ≤ 2*(1+216*Cs)*t*δ^(-(1/50 : ℝ)) := by
    rw [Real.rpow_neg hδ.le] at hp1
    calc
      _ = 2*(1+216*Cs)*A*(δ^(1/100 : ℝ))⁻¹ := by ring
      _ ≤ 2*(1+216*Cs)*t*δ^(-(1/50 : ℝ)) := mul_le_mul (by gcongr) hp1 (by positivity) (by positivity)
  have hd := geometric_den_pos (by norm_num : (0 : ℝ) < 1/10)
  have h2 := mul_le_mul_of_nonneg_left hp2
    (by positivity : 0 ≤ (16+4538*Cs)*t/(1-(1/2 : ℝ)^(1/10 : ℝ)))
  have h2' : (16+4538*Cs)*t*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤
      ((16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)))*t*δ^(-(1/50 : ℝ)) := by
    calc
      _ = ((16+4538*Cs)*t/(1-(1/2 : ℝ)^(1/10 : ℝ)))*δ^(1/10 : ℝ) := by ring
      _ ≤ ((16+4538*Cs)*t/(1-(1/2 : ℝ)^(1/10 : ℝ)))*δ^(-(1/50 : ℝ)) := h2
      _ = _ := by ring
  linarith

end DiskScales

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma inactive_kernel_distance {Cs d t r : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hd1 : d ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x : ℂ) (n : ℕ)
    (hsmall : coarseMass b (width d n) (thinShell x r (width d n)) ≤ t*(width d n)^(1/10 : ℝ)) :
    dist (∑ j, ∫ y, (kernel (k n) x y : ℂ)*(b j).density y)
      (∑ j, ∫ y, (kernel (k (n+1)) x y : ℂ)*(b j).density y) ≤
      (16+4538*Cs)*t*(width d n)^(1/10 : ℝ) := by
  rw [dist_eq_norm,norm_sub_rev,← Finset.sum_sub_distrib]
  simp_rw [general_kernel_pairing_sub (b _).integrable (k n) (k (n+1)) x]
  apply scaled_ordinary_inactive b hCs (width_pos hd n) ((width_le hd.le n).trans hd1) hAt
    ((complex_kernel_lipschitz (k (n+1)) x).sub (complex_kernel_lipschitz (k n) x))
    (measurableSet_thinShell x r (width d n)) (difference_bound (k n) (k (n+1)) x)
    (difference_support (k n) (k (n+1)) (width_antitone hd.le (Nat.le_succ n)) x) ?_ hsmall
  change 216/width d (n+1)+216/width d n ≤ 648/width d n
  rw [width_succ]
  exact le_of_eq (by ring)

lemma kernel_gap_errors {Cs d t r : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hd1 : d ≤ 1) (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x : ℂ) {j n : ℕ} (hjn : j < n)
    (hsmall : ∀ i, j < i → i < n → coarseMass b (width d i) (thinShell x r (width d i)) ≤
      t*(width d i)^(1/10 : ℝ)) :
    let B := (2*(1+216*Cs)+(16+4538*Cs)/(1-(1/2 : ℝ)^(1/10 : ℝ)))*t*(width d j)^(-(1/50 : ℝ))
    ‖∑ v, ∫ y, (kernel (k j) x y : ℂ)*(b v).density y‖ ≤ B ∧
    ‖∑ v, ∫ y, (kernel (k n) x y : ℂ)*(b v).density y‖ ≤ B := by
  have ht : 0 ≤ t := (errorPrice_nonneg b (1/100)).trans hAt
  have hwp (i : ℕ) := width_pos hd i
  have hw1 (i : ℕ) := (width_le hd.le i).trans hd1
  have hjpos : 0 < width d j := hwp j
  let P (i : ℕ) := ∑ v, ∫ y, (kernel (k i) x y : ℂ)*(b v).density y
  have hind (i : ℕ) : ‖P i‖ ≤ (1+216*Cs)/(width d i)^(1/100 : ℝ)*errorPrice b (1/100) :=
    kernel_error_bound b hCs (hwp i) (hw1 i) (k i) x
  have hsuc : ‖P (j+1)‖ ≤ 2*((1+216*Cs)/(width d j)^(1/100 : ℝ)*errorPrice b (1/100)) := by
    have hh := successor_discount (hwp j)
    have hi := hind (j+1)
    rw [width_succ] at hi
    have ha := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (show 0 ≤ 1+216*Cs by linarith) (errorPrice_nonneg b (1/100)))
    simp only [Real.inv_rpow (hwp j).le,Real.inv_rpow (by positivity : 0 ≤ width d j/2)] at ha
    exact hi.trans (by convert ha using 1 <;> ring)
  have htail := dist_width_tail hd.le (by norm_num : (0 : ℝ) < 1/10)
    (by positivity : 0 ≤ (16+4538*Cs)*t) (Nat.succ_le_of_lt hjn)
    (fun i hji hin => inactive_kernel_distance b hCs hd hd1 hAt k x i (hsmall i (by omega) hin))
  have hpow : (width d (j+1))^(1/10 : ℝ) ≤ (width d j)^(1/10 : ℝ) :=
    Real.rpow_le_rpow (hwp (j+1)).le (width_antitone hd.le (Nat.le_succ j)) (by norm_num)
  have hdg := geometric_den_pos (by norm_num : (0 : ℝ) < 1/10)
  have htail' : dist (P (j+1)) (P n) ≤
      (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) :=
    htail.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hdg.le)
  have hn : ‖P n‖ ≤ ‖P (j+1)‖+dist (P (j+1)) (P n) := by
    calc
      ‖P n‖ = ‖P (j+1)+(P n-P (j+1))‖ := by congr 1; abel
      _ ≤ ‖P (j+1)‖+‖P n-P (j+1)‖ := norm_add_le _ _
      _ = _ := by rw [dist_eq_norm,norm_sub_rev]
  have hscale := coarse_error_scale hCs (errorPrice_nonneg b (1/100)) hAt (hwp j) (hw1 j)
  constructor
  · have hnon : 0 ≤ (1+216*Cs)/(width d j)^(1/100 : ℝ)*errorPrice b (1/100) :=
      mul_nonneg (by positivity) (errorPrice_nonneg b (1/100))
    have htailnon : 0 ≤ (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by positivity
    exact (hind j).trans (by linarith)
  · change ‖P n‖ ≤ _
    linarith

lemma corrected_kernel_gap {Cs d t r : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4) (hr : r ∈ Icc (1 : ℝ) 2)
    (hAt : errorPrice b (1/100) ≤ t)
    (k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
      ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩) (x z : ℂ) {j n : ℕ} (hjn : j < n)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hcap : coarseMass b (width d j) (thinShell x r (width d j) \ Metric.ball z ((width d j)^(1/5 : ℝ))) ≤
      2*(t*(width d j)^(1/10 : ℝ)))
    (hsmall : ∀ i, j < i → i < n → coarseMass b (width d i) (thinShell x r (width d i)) ≤
      t*(width d i)^(1/10 : ℝ)) :
    ‖∑ v, ∫ y, correction x z y*((kernel (k n) x y : ℂ)-kernel (k j) x y)*(b v).density y‖ ≤
      (16+4538*Cs)*t*(width d j)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have ht : 0 ≤ t := (errorPrice_nonneg b (1/100)).trans hAt
  have hd1 : d ≤ 1 := by linarith
  have hwp (i : ℕ) := width_pos hd i
  have hw1 (i : ℕ) := (width_le hd.le i).trans hd1
  have hrw (i : ℕ) : r+width d i ≤ 3 := by linarith [width_le hd.le i,hr.2]
  let R (i : ℕ) := ∑ v, ∫ y, correction x z y*(kernel (k i) x y : ℂ)*(b v).density y
  have hid (i l : ℕ) : R l-R i =
      ∑ v, ∫ y, correction x z y*((kernel (k l) x y : ℂ)-kernel (k i) x y)*(b v).density y := by
    dsimp only [R]
    rw [← Finset.sum_sub_distrib]
    simp_rw [corrected_kernel_pairing_sub (b _).integrable (k i) (k l) x z (hrw i) (hrw l) hz]
  have hincr (i : ℕ) (hji : j ≤ i) (hin : i < n) :
      dist (R i) (R (i+1)) ≤ (16+4538*Cs)*t*(width d i)^(1/10 : ℝ) := by
    rw [dist_eq_norm,norm_sub_rev,hid]
    have hD3 : ∀ y ∈ thinShell x r (width d i), ‖y-x‖ ≤ 3 := by
      intro y hy
      have hh := (abs_le.mp (show |‖y-x‖-r| ≤ width d i from hy)).2
      linarith [hrw i]
    have hL : (216/width d (i+1)+216/width d i : ℝ) ≤ 648/width d i := by rw [width_succ]; exact le_of_eq (by ring)
    have hF := (complex_kernel_lipschitz (k (i+1)) x).sub (complex_kernel_lipschitz (k i) x)
    have hs := difference_support (k i) (k (i+1)) (width_antitone hd.le (Nat.le_succ i)) x
    by_cases hij : i = j
    · subst i
      exact scaled_corrected_active b hCs (hwp j) (hw1 j) hAt hF
        (measurableSet_thinShell x r (width d j)) (difference_bound (k j) (k (j+1)) x) hs hL x z hz hD3 hcap
    · exact scaled_corrected_inactive b hCs (hwp i) (hw1 i) hAt hF
        (measurableSet_thinShell x r (width d i)) (difference_bound (k i) (k (i+1)) x) hs hL
        (hsmall i (by omega) hin) x z hz hD3
  have hh := dist_width_tail hd.le (by norm_num : (0 : ℝ) < 1/10)
    (by positivity : 0 ≤ (16+4538*Cs)*t) hjn.le hincr
  rw [dist_eq_norm,norm_sub_rev,hid] at hh
  exact hh

end LocalCancellation

end SignedDisk

end

end OAI
