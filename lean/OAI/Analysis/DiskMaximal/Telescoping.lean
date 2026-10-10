import OAI.Analysis.DiskMaximal.LocalPrices

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real

noncomputable section

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

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

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

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

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

namespace DiskScales

def directionTailConstant (Cs κ : ℝ) : ℝ := (1+errorGapConstant Cs/κ)*sizeTailConstant

lemma directionTailConstant_pos {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    0 < directionTailConstant Cs κ := by
  unfold directionTailConstant
  have hh := errorGapConstant_pos hCs
  exact mul_pos (by positivity) sizeTailConstant_pos

end DiskScales

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales

/-- A genuine superlevel bound with exponent 34/25 > 1 for all neighborhood
maxima, independent of the number of positive or cancelling pieces. -/
theorem direction_tail {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
      (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
      0 < errorPrice b (1/100) → ∀ t : ℝ, L*errorPrice b (1/100) ≤ t →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      ∃ E : Set ℂ, MeasurableSet E ∧
        volume E ≤ ENNReal.ofReal (directionTailConstant Cs κ*(errorPrice b (1/100)/t)^(34/25 : ℝ)) ∧
        ∀ x ∉ E,
          (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
          ∀ r, NeighborhoodRadius g x r →
            max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y)) ≤ t := by
  obtain ⟨d₀,hd0,hdq,hgeom,hsmall⟩ := exists_direction_parameters Cs κ
  have hL : 1 ≤ (1 : ℝ)/d₀ := (le_div_iff₀ hd0).mpr (by linarith)
  refine ⟨1/d₀,hL,?_⟩
  intro ι _ e a b he hA t ht g hg
  let A := errorPrice b (1/100)
  let H := errorGapConstant Cs/κ
  have hH : 0 ≤ H := div_nonneg (errorGapConstant_pos hCs).le hκ.le
  have hH1 : 0 ≤ 1+H := by linarith
  have hAt : A ≤ t := (le_mul_of_one_le_left hA.le hL).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le hA hAt
  have hqd : A/t ≤ d₀ := by
    apply (div_le_iff₀ ht0).mpr
    have hh : A/d₀ ≤ t := by simpa only [A,one_div, div_eq_mul_inv, mul_comm, mul_one] using ht
    have hh' := (div_le_iff₀ hd0).mp hh
    linarith
  have hq0 : 0 < A/t := div_pos hA ht0
  have hq1 : A/t ≤ 1 := by linarith
  have hqq : A/t ≤ 1/4 := hqd.trans hdq
  obtain ⟨E,hE,hEv,hEst⟩ := direction_raw a b he hκ hCs hq0 hqq
    (fun δ hδ hδq => hgeom δ hδ (hδq.trans hqd)) ht0 hAt hg
  refine ⟨E,hE,?_,?_⟩
  · apply hEv.trans
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (1+H)*ENNReal.ofReal
          (156*(A/t)^2*(width (A/t) n)^(14/25 : ℝ)+
            2424*Real.pi*(A/t)*(width (A/t) n)^(9/25 : ℝ)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [← ENNReal.ofReal_mul hH1]
        apply direction_shell_tail_scaled hA.le ht0 (width_pos hq0 n)
          ((width_le hq0.le n).trans hq1) (coarseMass_nonneg b _ _) hH
        have hw0 := width_pos hq0 n
        have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hw0
        norm_num at hh
        rw [Real.rpow_neg hw0.le]
        exact hh
      _ = ENNReal.ofReal (1+H)*ENNReal.ofReal
          ((156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
            (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ)) := by
        rw [ENNReal.tsum_mul_left,geometric_tail_sum hA.le ht0 hq0.le, starting_width_tail hA ht0]
      _ ≤ ENNReal.ofReal (1+H)*ENNReal.ofReal (sizeTailConstant*(A/t)^(34/25 : ℝ)) := by
        gcongr
        exact collapse_size_tail hq0 hq1
      _ = _ := by rw [← ENNReal.ofReal_mul hH1]; congr 1; dsimp only [directionTailConstant,H,A]; ring
  · intro x hx hh r hr
    apply (hEst x hx hh r hr).trans
    rw [direction_start_identity hA ht0]
    exact (mul_le_mul_of_nonneg_left (hsmall _ hq0 hqd) ht0.le).trans_eq (mul_one t)

lemma cone_ball_nonneg {e : ℂ} {κ : ℝ} (a : ConeDensity e κ) (hκ : 0 ≤ κ) (x : ℂ) (r : ℝ) :
    0 ≤ inner ℝ e (∫ y in Metric.ball x r, a.density y) := by
  rw [← integral_inner a.integrable.integrableOn e]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_of_ae a.cone] with y hy
  exact (mul_nonneg hκ (norm_nonneg _)).trans hy

/-- Full Borel integrable directional price. This is the hard local
cancellation estimate, not an assumed maximal-operator endpoint. -/
theorem direction_majorant {Cs κ : ℝ} (hCs : 0 ≤ Cs) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {e : ℂ} (a : ConeDensity e κ)
      (b : ι → ErrorPiece Cs), ‖e‖ = 1 →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
      ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
        (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
        ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → a.density y+∑ j, (b j).density y = gradient g y) →
          ∀ r, NeighborhoodRadius g x r →
            ENNReal.ofReal (max 0 (-inner ℝ e (∫ y in Metric.ball x r, gradient g y))) ≤ F x := by
  obtain ⟨L,hL,hdir⟩ := direction_tail hCs hκ
  let c : ℝ := (1/2 : ℝ)^(34/25 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : 2*c < 1 := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 34/25)
    norm_num at hh
    linarith
  let C := L*(1+2*directionTailConstant Cs κ/(1-2*c))
  have hD := directionTailConstant_pos hCs hκ
  have hC : 0 < C := mul_pos (by linarith) (by
    have := sub_pos.mpr hc1
    positivity)
  refine ⟨C,hC,?_⟩
  intro ι _ e a b he g hg Q hQ
  let A := errorPrice b (1/100)
  by_cases hAz : A = 0
  · refine ⟨0,measurable_const,?_,?_⟩
    · simp only [Pi.zero_apply, lintegral_zero, A, hAz, mul_zero, ENNReal.ofReal_zero, le_refl]
    · intro x hh r hr
      have hz := errorPrice_zero b hAz
      have hs : (∑ j, ∫ y in Metric.ball x r, (b j).density y) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact integral_eq_zero_of_ae (ae_restrict_of_ae (hz j))
      have hb := mixed_ball_pairing_decomposition b a.integrable x (by linarith [hr.1.2] : r ≤ 3) hh
      rw [← hb,hs,add_zero,max_eq_left (neg_nonpos.mpr (cone_ball_nonneg a hκ.le x r)),ENNReal.ofReal_zero]
      exact le_refl _
  · have hA : 0 < A := lt_of_le_of_ne (errorPrice_nonneg b _) (Ne.symm hAz)
    have ht : 0 < L*A := mul_pos (by linarith) hA
    have hts (n : ℕ) : L*A ≤ L*A*2^n := le_mul_of_one_le_right ht.le (one_le_pow₀ (by norm_num))
    choose E hE hEv hbound using fun n : ℕ => hdir a b he hA (L*A*2^n) (hts n) g hg
    refine ⟨DyadicMajorant.price (L*A) E, DyadicMajorant.measurable_price _ hE,?_,?_⟩
    · have htail (n : ℕ) : volume (E n) ≤ ENNReal.ofReal (directionTailConstant Cs κ*c^n) := by
        apply (hEv n).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hD.le
        calc
          _ ≤ ((1/2 : ℝ)^n)^(34/25 : ℝ) := Real.rpow_le_rpow (by positivity) (dyadic_ratio hA hL n) (by norm_num)
          _ = c^n := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ),
              Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have hi := DyadicMajorant.lintegral_price_geometric volume (by norm_num : (0 : ℝ) ≤ 1) hQ ht.le
        hD.le hc hc1 hE htail
      convert hi using 1
      congr 1
      dsimp [C,A]
      ring
    · intro x hh r hr
      apply DyadicMajorant.majorizes ht
      intro n hn
      exact hbound n x hn hh r hr

end LocalCancellation

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
noncomputable section

end
end

end OAI
