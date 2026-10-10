import Mathlib
import OAI.Probability.SLE.IntervalDensity

namespace OAI

/-! Strip Kernels for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
lemma integrable_mul_compact_test {μ : Measure ℂ} {f g : ℂ → ℝ}
    (hf : Integrable f μ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun z => f z * g z) μ := by
  obtain ⟨C, hC⟩ := (hgc.isCompact_range hg).isBounded.exists_norm_le
  exact hf.mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall fun z => hC _ ⟨z,rfl⟩)

lemma weak_gradient_pairing {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) {X Y : ℂ → ℝ}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (hcX : HasCompactSupport X) (hcY : HasCompactSupport Y)
    (hsX : tsupport X ⊆ openUnitStrip) (hsY : tsupport Y ⊆ openUnitStrip) :
    (∫ z in openUnitStrip, u z * ((fderiv ℝ X z) 1 + (fderiv ℝ Y z) Complex.I)) =
      -(∫ z in openUnitStrip, (D z).re * X z + (D z).im * Y z) := by
  have hui := hu.1.integrable (by norm_num)
  have hDi := hu.2.1.integrable (by norm_num)
  have hx := integrable_mul_compact_test hui
    ((hX.continuous_fderiv (by simp)).clm_apply continuous_const) (hcX.fderiv_apply ℝ 1)
  have hy := integrable_mul_compact_test hui
    ((hY.continuous_fderiv (by simp)).clm_apply continuous_const) (hcY.fderiv_apply ℝ Complex.I)
  have hdx := integrable_mul_compact_test (Complex.reCLM.integrable_comp hDi) hX.continuous hcX
  have hdy := integrable_mul_compact_test (Complex.imCLM.integrable_comp hDi) hY.continuous hcY
  change Integrable (fun z => (D z).re * X z) _ at hdx
  change Integrable (fun z => (D z).im * Y z) _ at hdy
  simp_rw [mul_add]
  rw [integral_add hx hy, (hu.2.2 X hX hcX hsX).1, (hu.2.2 Y hY hcY hsY).2,
    integral_add hdx hdy]
  ring

lemma complex_pairing_abs_le (D : ℂ) (X Y : ℝ) :
    |D.re * X + D.im * Y| ≤ ‖D‖ * (|X|+|Y|) := by
  calc
    _ ≤ |D.re * X| + |D.im * Y| := abs_add_le _ _
    _ ≤ ‖D‖ * |X| + ‖D‖ * |Y| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm D) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm D) (abs_nonneg _))
    _ = _ := by ring

lemma integral_nonneg_cauchy {μ : Measure ℂ} {f g : ℂ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) :
    (∫ z, f z * g z ∂μ) ≤
      Real.sqrt (∫ z, (f z)^2 ∂μ) * Real.sqrt (∫ z, (g z)^2 ∂μ) := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hh

lemma integral_pairing_le {D : ℂ → ℂ}
    (hD : MemLp D 2 (volume.restrict openUnitStrip)) {X Y : ℂ → ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hcX : HasCompactSupport X) (hcY : HasCompactSupport Y) :
    |∫ z in openUnitStrip, (D z).re * X z + (D z).im * Y z| ≤
      Real.sqrt (stripDirichletEnergy D) *
        Real.sqrt (∫ z in openUnitStrip, (|X z|+|Y z|)^2) := by
  have hDi := hD.integrable (by norm_num)
  have hdx := integrable_mul_compact_test (Complex.reCLM.integrable_comp hDi) hX hcX
  have hdy := integrable_mul_compact_test (Complex.imCLM.integrable_comp hDi) hY hcY
  have hK : MemLp (fun z => |X z|+|Y z|) 2 (volume.restrict openUnitStrip) :=
    (hX.abs.add hY.abs).memLp_of_hasCompactSupport (hcX.abs.add hcY.abs)
  calc
    _ ≤ ∫ z in openUnitStrip, |(D z).re * X z + (D z).im * Y z| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => (D z).re * X z + (D z).im * Y z)
    _ ≤ ∫ z in openUnitStrip, ‖D z‖ * (|X z|+|Y z|) :=
      integral_mono (hdx.add hdy).abs (hD.norm.integrable_mul hK)
        (fun z => complex_pairing_abs_le ..)
    _ ≤ _ := integral_nonneg_cauchy hD.norm hK (fun _ => norm_nonneg _)
      (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

noncomputable def chainDensity (t s : ℝ) (j n : ℕ) : ℂ → ℝ :=
  rectangleDensity (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j)) n
noncomputable def chainX (t s : ℝ) (j n : ℕ) : ℂ → ℝ :=
  rectangleTransportX (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n
noncomputable def chainY (t s : ℝ) (j n : ℕ) : ℂ → ℝ :=
  rectangleTransportY (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n
noncomputable def chainKernel (t s : ℝ) (j n : ℕ) (z : ℂ) : ℝ :=
  |chainX t s j n z|+|chainY t s j n z|

lemma chainX_smooth (t s : ℝ) (j n : ℕ) : ContDiff ℝ ∞ (chainX t s j n) :=
  rectangleTransportX_contDiff ..
lemma chainY_smooth (t s : ℝ) (j n : ℕ) : ContDiff ℝ ∞ (chainY t s j n) :=
  rectangleTransportY_contDiff ..
lemma chainX_compact {t : ℝ} (s : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (j n : ℕ) :
    HasCompactSupport (chainX t s j n) :=
  rectangleTransportX_compact _ _ _ _ _ _ _ _
    (scaleOrigin_step ht j) (scaleOrigin_right_step ht1 j) n
lemma chainY_compact (t : ℝ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    HasCompactSupport (chainY t s j n) := by
  apply rectangleTransportY_compact
  · exact mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le
  · have hh := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
    nlinarith

lemma chainX_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    tsupport (chainX t s j n) ⊆ openUnitStrip := by
  have hh := rectangleTransportX_support (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (scaleOrigin_step ht j) (scaleOrigin_right_step ht1 j)
    (mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
        nlinarith) n
  intro z hz
  obtain ⟨h1,h2,h3,h4⟩ := hh hz
  have h5 := scaleOrigin_nonneg ht j
  have h6 := scaleOrigin_add_le_one ht1 j
  have h7 := mul_nonneg Real.pi_pos.le (scaleOrigin_nonneg hs j)
  have h8 := mul_le_mul_of_nonneg_left (scaleOrigin_add_le_one hs1 j) Real.pi_pos.le
  exact ⟨by linarith, by linarith, by linarith, by nlinarith⟩

lemma chainY_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    tsupport (chainY t s j n) ⊆ openUnitStrip := by
  have hh := rectangleTransportY_support (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
        nlinarith) n
  intro z hz
  obtain ⟨h1,h2,h3,h4⟩ := hh hz
  have h5 := scaleOrigin_nonneg ht j
  have h6 := scaleOrigin_add_le_one ht1 j
  have h7 := mul_nonneg Real.pi_pos.le (scaleOrigin_nonneg hs j)
  have h8 := mul_le_mul_of_nonneg_left (scaleOrigin_add_le_one hs1 j) Real.pi_pos.le
  exact ⟨by linarith, by linarith, by linarith, by nlinarith⟩

lemma chain_divergence (t s : ℝ) (j n : ℕ) (z : ℂ) :
    (fderiv ℝ (chainX t s j n) z) 1 + (fderiv ℝ (chainY t s j n) z) Complex.I =
      chainDensity t s (j+1) n z - chainDensity t s j n z := by
  unfold chainX chainY chainDensity
  rw [rectangleTransport_divergence]
  simp only [scaleLength_succ, mul_div_assoc]

lemma chainKernel_continuous (t s : ℝ) (j n : ℕ) : Continuous (chainKernel t s j n) :=
  (chainX_smooth t s j n).continuous.abs.add (chainY_smooth t s j n).continuous.abs
lemma chainKernel_compact {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    HasCompactSupport (chainKernel t s j n) :=
  (chainX_compact s ht ht1 j n).abs.add (chainY_compact t hs hs1 j n).abs
lemma chainKernel_nonneg (t s : ℝ) (j n : ℕ) (z : ℂ) : 0 ≤ chainKernel t s j n z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma chainKernel_bound (t s : ℝ) (j n : ℕ) (z : ℂ) :
    ‖chainKernel t s j n z‖ ≤ 12 * (2:ℝ)^j := by
  rw [Real.norm_of_nonneg (chainKernel_nonneg ..)]
  have hx := rectangleTransportX_bound (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n z
  have hy := rectangleTransportY_bound (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n z
  have hp : scaleLength j ≤ Real.pi*scaleLength j := by
    nlinarith [scaleLength_pos j, Real.pi_gt_three]
  have hx' := hx.trans (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8)
    (scaleLength_pos j) hp)
  change |chainX t s j n z| + |chainY t s j n z| ≤ _
  calc
    _ ≤ 8/scaleLength j + 4/scaleLength j := add_le_add hx' hy
    _ = _ := by unfold scaleLength; field_simp; ring

lemma chainKernel_integral_bound {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    (∫ z, ‖chainKernel t s j n z‖) ≤ 10 / (2:ℝ)^j := by
  have hx := rectangleTransportX_integral_abs (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (scaleOrigin_step ht j) (scaleOrigin_right_step ht1 j) n
  have hy := rectangleTransportY_integral_abs (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
        nlinarith) n
  have hiX := (chainX_smooth t s j n).continuous.integrable_of_hasCompactSupport (μ := volume)
    (chainX_compact s ht ht1 j n)
  have hiY := (chainY_smooth t s j n).continuous.integrable_of_hasCompactSupport (μ := volume)
    (chainY_compact t hs hs1 j n)
  simp_rw [Real.norm_of_nonneg (chainKernel_nonneg ..)]
  change (∫ z, |chainX t s j n z| + |chainY t s j n z|) ≤ _
  rw [integral_add hiX.abs hiY.abs]
  change (∫ z, |chainX t s j n z|) ≤ _ at hx
  change (∫ z, |chainY t s j n z|) ≤ _ at hy
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (scaleLength_pos j).le
  have hh : 10*scaleLength j = 10/(2:ℝ)^j := by simp [scaleLength, div_eq_mul_inv]
  nlinarith

lemma compact_sum_range {f : ℕ → ℂ → ℝ} (hf : ∀ j, HasCompactSupport (f j)) (k : ℕ) :
    HasCompactSupport (fun z => ∑ j ∈ Finset.range k, f j z) := by
  induction k with
  | zero => simp [HasCompactSupport]
  | succ k ih =>
    simp only [Finset.sum_range_succ]
    exact (ih.union (hf k)).of_isClosed_subset (isClosed_tsupport _) (tsupport_add _ _)

lemma support_sum_range {f : ℕ → ℂ → ℝ} {S : Set ℂ}
    (hf : ∀ j, tsupport (f j) ⊆ S) (k : ℕ) :
    tsupport (fun z => ∑ j ∈ Finset.range k, f j z) ⊆ S := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.sum_range_succ]
    exact (tsupport_add _ _).trans (union_subset ih (hf k))

noncomputable def aggregateX (t s : ℝ) (k n : ℕ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range k, chainX t s j n z
noncomputable def aggregateY (t s : ℝ) (k n : ℕ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range k, chainY t s j n z

lemma aggregateX_smooth (t s : ℝ) (k n : ℕ) : ContDiff ℝ ∞ (aggregateX t s k n) :=
  ContDiff.sum (fun j _ => chainX_smooth t s j n)
lemma aggregateY_smooth (t s : ℝ) (k n : ℕ) : ContDiff ℝ ∞ (aggregateY t s k n) :=
  ContDiff.sum (fun j _ => chainY_smooth t s j n)
lemma aggregateX_compact {t : ℝ} (s : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (k n : ℕ) :
    HasCompactSupport (aggregateX t s k n) :=
  compact_sum_range (fun j => chainX_compact s ht ht1 j n) k
lemma aggregateY_compact (t : ℝ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    HasCompactSupport (aggregateY t s k n) :=
  compact_sum_range (fun j => chainY_compact t hs hs1 j n) k
lemma aggregateX_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    tsupport (aggregateX t s k n) ⊆ openUnitStrip :=
  support_sum_range (fun j => chainX_support ht ht1 hs hs1 j n) k
lemma aggregateY_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    tsupport (aggregateY t s k n) ⊆ openUnitStrip :=
  support_sum_range (fun j => chainY_support ht ht1 hs hs1 j n) k

lemma aggregate_divergence (t s : ℝ) (k n : ℕ) (z : ℂ) :
    (fderiv ℝ (aggregateX t s k n) z) 1 + (fderiv ℝ (aggregateY t s k n) z) Complex.I =
      chainDensity t s k n z - chainDensity t s 0 n z := by
  unfold aggregateX aggregateY
  rw [fderiv_fun_sum (fun j _ => ((chainX_smooth t s j n).differentiable (by simp)) z),
    fderiv_fun_sum (fun j _ => ((chainY_smooth t s j n).differentiable (by simp)) z)]
  simp only [sum_apply, ← Finset.sum_add_distrib]
  simp_rw [chain_divergence]
  exact Finset.sum_range_sub (fun j => chainDensity t s j n z) k

lemma aggregate_kernel_bound {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    (∫ z in openUnitStrip, (|aggregateX t s k n z|+|aggregateY t s k n z|)^2) ≤ 360*k := by
  have hsum : (∫ z in openUnitStrip, ‖∑ j ∈ Finset.range k, chainKernel t s j n z‖^2) ≤
      3*12*10*k := by
    apply integral_sum_kernel_sq_le (fun j => chainKernel t s j n) 12 10 k
      (by norm_num) (by norm_num)
    · intro j _
      exact ((chainKernel_continuous t s j n).integrable_of_hasCompactSupport
        (chainKernel_compact ht ht1 hs hs1 j n)).integrableOn
    · intro j _ z
      exact chainKernel_bound t s j n z
    · intro j _
      refine (setIntegral_le_integral ?_ (Eventually.of_forall (fun _ => norm_nonneg _))).trans
        (chainKernel_integral_bound ht ht1 hs hs1 j n)
      exact ((chainKernel_continuous t s j n).integrable_of_hasCompactSupport
        (chainKernel_compact ht ht1 hs hs1 j n)).norm
  have hI : Integrable (fun z => (|aggregateX t s k n z|+|aggregateY t s k n z|)^2)
      (volume.restrict openUnitStrip) := by
    apply MemLp.integrable_sq
    exact ((aggregateX_smooth t s k n).continuous.abs.add
      (aggregateY_smooth t s k n).continuous.abs).memLp_of_hasCompactSupport
      ((aggregateX_compact s ht ht1 k n).abs.add (aggregateY_compact t hs hs1 k n).abs)
  have hJ : Integrable (fun z => ‖∑ j ∈ Finset.range k, chainKernel t s j n z‖^2)
      (volume.restrict openUnitStrip) := by
    have hc := continuous_finsetSum (Finset.range k) (fun j _ => chainKernel_continuous t s j n)
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).1
      (hc.memLp_of_hasCompactSupport
        (compact_sum_range (fun j => chainKernel_compact ht ht1 hs hs1 j n) k))
  refine (integral_mono hI hJ ?_).trans (by linarith)
  intro z
  have hh : |aggregateX t s k n z|+|aggregateY t s k n z| ≤
      ∑ j ∈ Finset.range k, chainKernel t s j n z := by
    unfold aggregateX aggregateY chainKernel
    rw [Finset.sum_add_distrib]
    exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).2
  exact hh.trans (le_abs_self _)

lemma chainDensity_continuous (t s : ℝ) (j n : ℕ) : Continuous (chainDensity t s j n) :=
  (complexTensor_contDiff (intervalDensity_smooth ..) (intervalDensity_smooth ..)).continuous
lemma chainDensity_compact (t s : ℝ) (j n : ℕ) : HasCompactSupport (chainDensity t s j n) :=
  complexTensor_compact (intervalDensity_compact ..) (intervalDensity_compact ..)

lemma smoothed_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    |(∫ z in openUnitStrip, u z * chainDensity t s k n z) -
      (∫ z in openUnitStrip, u z * chainDensity t s 0 n z)| ≤
      20 * Real.sqrt (((k:ℝ)+1)*stripDirichletEnergy D) := by
  have he := weak_gradient_pairing hu (aggregateX_smooth t s k n) (aggregateY_smooth t s k n)
    (aggregateX_compact s ht ht1 k n) (aggregateY_compact t hs hs1 k n)
    (aggregateX_support ht ht1 hs hs1 k n) (aggregateY_support ht ht1 hs hs1 k n)
  simp_rw [aggregate_divergence] at he
  have hi₁ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
    (chainDensity_continuous t s k n) (chainDensity_compact t s k n)
  have hi₀ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
    (chainDensity_continuous t s 0 n) (chainDensity_compact t s 0 n)
  simp_rw [mul_sub] at he
  rw [integral_sub hi₁ hi₀] at he
  rw [he, abs_neg]
  refine (integral_pairing_le hu.2.1 (aggregateX_smooth t s k n).continuous
    (aggregateY_smooth t s k n).continuous (aggregateX_compact s ht ht1 k n)
    (aggregateY_compact t hs hs1 k n)).trans ?_
  have hE : 0 ≤ stripDirichletEnergy D := integral_nonneg (fun _ => sq_nonneg _)
  have hA : 0 ≤ ∫ z in openUnitStrip, (|aggregateX t s k n z|+|aggregateY t s k n z|)^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hb := aggregate_kernel_bound ht ht1 hs hs1 k n
  have hR : 0 ≤ ((k:ℝ)+1)*stripDirichletEnergy D := by positivity
  have hSqE := Real.sq_sqrt hE
  have hSqA := Real.sq_sqrt hA
  have hSqR := Real.sq_sqrt hR
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, hSqE, hSqA, mul_pow, hSqR]
  nlinarith [mul_le_mul_of_nonneg_left hb hE]

def stripRectangle (a b l : ℝ) : Set ℂ :=
  {w | a ≤ w.re ∧ w.re ≤ a+l ∧ b ≤ w.im ∧ w.im ≤ b+Real.pi*l}

lemma stripRectangle_eq_preimage (a b l : ℝ) :
    stripRectangle a b l = Complex.measurableEquivRealProd ⁻¹'
      (Icc a (a+l) ×ˢ Icc b (b+Real.pi*l)) := by
  ext z
  simp only [stripRectangle, mem_ofPred_eq, mem_preimage, mem_prod, mem_Icc,
    Complex.measurableEquivRealProd_apply]
  tauto

lemma stripRectangle_volume (a b l : ℝ) :
    volume (stripRectangle a b l) = ENNReal.ofReal l * ENNReal.ofReal (Real.pi*l) := by
  rw [stripRectangle_eq_preimage,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp only [Real.volume_Icc, add_sub_cancel_left]

lemma stripRectangle_integral_mul (a b l : ℝ) (f g : ℝ → ℝ) :
    (∫ z in stripRectangle a b l, f z.re * g z.im) =
      (∫ x in Icc a (a+l), f x) * (∫ y in Icc b (b+Real.pi*l), g y) := by
  rw [stripRectangle_eq_preimage]
  have he := (Complex.volume_preserving_equiv_real_prod.restrict_preimage
    (s := Icc a (a+l) ×ˢ Icc b (b+Real.pi*l))
    (measurableSet_Icc.prod measurableSet_Icc)).integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => f p.1 * g p.2)
  simp only [Complex.measurableEquivRealProd_apply] at he
  rw [he]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul f g

lemma stripRectangle_integral_re (a b l : ℝ) (hl : 0 ≤ l) :
    (∫ z in stripRectangle a b l, z.re) =
      (a*l+l^2/2)*(Real.pi*l) := by
  have h := stripRectangle_integral_mul a b l (fun x => x) (fun _ => 1)
  simp only [mul_one] at h
  rw [h, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : a ≤ a+l), integral_id]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    add_sub_cancel_left, smul_eq_mul, mul_one]
  rw [ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le hl)]
  ring

noncomputable def spatialAverage (u : ℂ → ℝ) (Q : Set ℂ) : ℝ :=
  (∫ z in Q, u z) / (volume Q).toReal

def openStripRectangle (a b l : ℝ) : Set ℂ :=
  {z | a < z.re ∧ z.re < a+l ∧ b < z.im ∧ z.im < b+Real.pi*l}

lemma openStripRectangle_eq_preimage (a b l : ℝ) :
    openStripRectangle a b l = Complex.measurableEquivRealProd ⁻¹'
      (Ioo a (a+l) ×ˢ Ioo b (b+Real.pi*l)) := by
  ext z
  simp only [openStripRectangle, mem_ofPred_eq, mem_preimage, mem_prod, mem_Ioo,
    Complex.measurableEquivRealProd_apply]
  tauto

lemma openStripRectangle_measurable (a b l : ℝ) : MeasurableSet (openStripRectangle a b l) := by
  rw [openStripRectangle_eq_preimage]
  exact (measurableSet_Ioo.prod measurableSet_Ioo).preimage
    Complex.measurableEquivRealProd.measurable

lemma openStripRectangle_ae_eq (a b l : ℝ) :
    openStripRectangle a b l =ᵐ[volume] stripRectangle a b l := by
  rw [openStripRectangle_eq_preimage, stripRectangle_eq_preimage]
  apply Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.preimage_ae_eq
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc

lemma rectangleDensity_nonneg (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (n : ℕ) (z : ℂ) : 0 ≤ rectangleDensity a b lx ly hx hy n z :=
  mul_nonneg (intervalDensity_nonneg ..) (intervalDensity_nonneg ..)
lemma rectangleDensity_bound (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (n : ℕ) (z : ℂ) : rectangleDensity a b lx ly hx hy n z ≤ 4/(lx*ly) := by
  calc
    _ ≤ (2/lx)*(2/ly) := mul_le_mul (intervalDensity_bound ..) (intervalDensity_bound ..)
      (intervalDensity_nonneg ..) (by positivity)
    _ = _ := by ring

lemma rectangleDensity_tendsto (a b l : ℝ) (hl : 0 < l) (z : ℂ) :
    Tendsto (fun n => rectangleDensity a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) n z)
      atTop (𝓝 ((openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z)) := by
  have hh := (intervalDensity_tendsto a l hl z.re).mul
    (intervalDensity_tendsto b (Real.pi*l) (mul_pos Real.pi_pos hl) z.im)
  have heq : (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z =
      (Ioo a (a+l)).indicator (fun _ => 1/l) z.re *
        (Ioo b (b+Real.pi*l)).indicator (fun _ => 1/(Real.pi*l)) z.im := by
    by_cases hx : z.re ∈ Ioo a (a+l) <;> by_cases hy : z.im ∈ Ioo b (b+Real.pi*l)
    · have hz : z ∈ openStripRectangle a b l := ⟨hx.1,hx.2,hy.1,hy.2⟩
      simp [hz,hx,hy,one_div]
      ring
    · have hz : z ∉ openStripRectangle a b l := fun hz => hy ⟨hz.2.2.1,hz.2.2.2⟩
      simp [hz,hx,hy]
    · have hz : z ∉ openStripRectangle a b l := fun hz => hx ⟨hz.1,hz.2.1⟩
      simp [hz,hx,hy]
    · have hz : z ∉ openStripRectangle a b l := fun hz => hx ⟨hz.1,hz.2.1⟩
      simp [hz,hx,hy]
  simpa only [rectangleDensity, complexTensor, heq] using hh

lemma rectangle_smoothed_mean_tendsto {u : ℂ → ℝ}
    (hu : MemLp u 2 (volume.restrict openUnitStrip)) (a b l : ℝ) (hl : 0 < l)
    (ha : 0 ≤ a) (ha1 : a+l ≤ 1) (hb : 0 ≤ b) (hb1 : b+Real.pi*l ≤ Real.pi) :
    Tendsto (fun n => ∫ z in openUnitStrip,
      u z * rectangleDensity a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) n z)
      atTop (𝓝 (spatialAverage u (stripRectangle a b l))) := by
  have hsub : openStripRectangle a b l ⊆ openUnitStrip := by
    intro z hz
    exact ⟨ha.trans_lt hz.1, hz.2.1.trans_le ha1, hb.trans_lt hz.2.2.1, hz.2.2.2.trans_le hb1⟩
  have hint := hu.integrable (by norm_num)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict openUnitStrip)
    (F := fun n z => u z * rectangleDensity a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) n z)
    (f := fun z => u z * (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z)
    (fun z => |u z| * (4/(l*(Real.pi*l))))
    (fun n => hu.aestronglyMeasurable.mul
      ((complexTensor_contDiff (intervalDensity_smooth ..) (intervalDensity_smooth ..)).continuous.aestronglyMeasurable))
    (hint.abs.mul_const _) (fun n => Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rectangleDensity_nonneg ..)]
      exact mul_le_mul_of_nonneg_left (rectangleDensity_bound ..) (abs_nonneg _))
    (Eventually.of_forall fun z => (rectangleDensity_tendsto a b l hl z).const_mul (u z))
  have heq : (∫ z in openUnitStrip,
      u z * (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z) =
      spatialAverage u (stripRectangle a b l) := by
    have hfun : (fun z => u z * (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z) =
        (openStripRectangle a b l).indicator (fun z => u z * (1/(l*(Real.pi*l)))) := by
      funext z
      by_cases hz : z ∈ openStripRectangle a b l <;> simp [hz]
    rw [hfun, integral_indicator (openStripRectangle_measurable a b l),
      Measure.restrict_restrict (openStripRectangle_measurable a b l), inter_eq_left.mpr hsub,
      integral_mul_const, setIntegral_congr_set (openStripRectangle_ae_eq a b l)]
    unfold spatialAverage
    rw [stripRectangle_volume, ENNReal.toReal_mul, ENNReal.toReal_ofReal hl.le,
      ENNReal.toReal_ofReal (mul_pos Real.pi_pos hl).le]
    ring
  rwa [heq] at hlim

def dyadicStripRectangle (j : ℤ) (k : ℕ) (i m : Fin (2^k)) : Set ℂ :=
  stripRectangle ((j:ℝ)+(i:ℝ)/(2:ℝ)^k)
    (Real.pi*((m:ℝ)/(2:ℝ)^k)) (1/(2:ℝ)^k)

 

def SourceCriticalStripMeansTarget : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (u : ℂ → ℝ) (D : ℂ → ℂ),
    SourceIsStripWeakGradient u D → ContinuousOn u (stripRectangle 0 0 1) →
    ∀ (k : ℕ) (i m : Fin (2^k)),
      |spatialAverage u (dyadicStripRectangle 0 k i m) -
        spatialAverage u (stripRectangle 0 0 1)| ≤
      K * Real.sqrt (((k:ℝ)+1)*stripDirichletEnergy D)

lemma chain_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) :
    |spatialAverage u (stripRectangle (scaleOrigin t k) (Real.pi*scaleOrigin s k) (scaleLength k)) -
      spatialAverage u (stripRectangle 0 0 1)| ≤
      20 * Real.sqrt (((k:ℝ)+1)*stripDirichletEnergy D) := by
  have hlim (j : ℕ) : Tendsto (fun n => ∫ z in openUnitStrip, u z * chainDensity t s j n z)
      atTop (𝓝 (spatialAverage u (stripRectangle (scaleOrigin t j)
        (Real.pi*scaleOrigin s j) (scaleLength j)))) := by
    apply rectangle_smoothed_mean_tendsto hu.1 _ _ _ (scaleLength_pos j)
      (scaleOrigin_nonneg ht j) (scaleOrigin_add_le_one ht1 j)
      (mul_nonneg Real.pi_pos.le (scaleOrigin_nonneg hs j))
    have hh := mul_le_mul_of_nonneg_left (scaleOrigin_add_le_one hs1 j) Real.pi_pos.le
    nlinarith
  have hzero := hlim 0
  simp only [scaleOrigin_zero, scaleLength_zero, mul_zero] at hzero
  exact le_of_tendsto ((hlim k).sub hzero).abs
    (Eventually.of_forall (fun n => smoothed_means_le hu ht ht1 hs hs1 k n))

theorem sourceCriticalStripMeans : SourceCriticalStripMeansTarget := by
  refine ⟨20, by norm_num, ?_⟩
  intro u D hu _ k i m
  by_cases hk : k = 0
  · subst k
    have hi : i = 0 := by apply Fin.ext; have := i.isLt; norm_num at this ⊢
    have hm : m = 0 := by apply Fin.ext; have := m.isLt; norm_num at this ⊢
    subst i; subst m
    simp [dyadicStripRectangle]
  · obtain ⟨t, ht, ht1, hit⟩ := dyadic_position_param k hk i
    obtain ⟨s, hs, hs1, hms⟩ := dyadic_position_param k hk m
    have hh := chain_means_le hu ht ht1 hs hs1 k
    simpa only [dyadicStripRectangle, Int.cast_zero, zero_add, hit, hms, scaleLength] using hh

lemma integral_pairing_local_le {D : ℂ → ℂ}
    (hD : MemLp D 2 (volume.restrict openUnitStrip)) {V : Set ℂ}
    (hV : V ⊆ openUnitStrip) {X Y : ℂ → ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hcX : HasCompactSupport X) (hcY : HasCompactSupport Y)
    (hsX : tsupport X ⊆ V) (hsY : tsupport Y ⊆ V) :
    |∫ z in openUnitStrip, (D z).re * X z + (D z).im * Y z| ≤
      Real.sqrt (∫ z in V, ‖D z‖^2) *
        Real.sqrt (∫ z in V, (|X z|+|Y z|)^2) := by
  have hm : volume.restrict V ≤ volume.restrict openUnitStrip :=
    Measure.restrict_mono hV le_rfl
  have hDl := hD.mono_measure hm
  have hDi := (hD.integrable (by norm_num)).mono_measure hm
  have hdx := integrable_mul_compact_test (Complex.reCLM.integrable_comp hDi) hX hcX
  have hdy := integrable_mul_compact_test (Complex.imCLM.integrable_comp hDi) hY hcY
  have hK : MemLp (fun z => |X z|+|Y z|) 2 (volume.restrict V) :=
    (hX.abs.add hY.abs).memLp_of_hasCompactSupport (hcX.abs.add hcY.abs)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero openUnitStrip_isOpen.measurableSet hV
    (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hsX h)),
        image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hsY h))]
      ring)]
  calc
    _ ≤ ∫ z in V, |(D z).re * X z + (D z).im * Y z| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => (D z).re * X z + (D z).im * Y z)
    _ ≤ ∫ z in V, ‖D z‖ * (|X z|+|Y z|) :=
      integral_mono (hdx.add hdy).abs (hDl.norm.integrable_mul hK)
        (fun z => complex_pairing_abs_le ..)
    _ ≤ _ := integral_nonneg_cauchy hDl.norm hK (fun _ => norm_nonneg _)
      (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

lemma rectangle_transport_L2_bound (a b l : ℝ) (hl : 0 < l) (a' b' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l)
    (hb : b ≤ b') (hb' : b'+(Real.pi*l)/2 ≤ b+Real.pi*l) (n : ℕ) (V : Set ℂ) :
    (∫ z in V, (|rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z| +
      |rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z|)^2) ≤ 120 := by
  let X := rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
  let Y := rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
  have hx := (rectangleTransportX_contDiff a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n).continuous
  have hy := (rectangleTransportY_contDiff a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n).continuous
  have hcx := rectangleTransportX_compact a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' ha ha' n
  have hcy := rectangleTransportY_compact a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' hb hb' n
  have hK : Continuous (fun z => |X z|+|Y z|) := hx.abs.add hy.abs
  have hcK : HasCompactSupport (fun z => |X z|+|Y z|) := hcx.abs.add hcy.abs
  have hKi := hK.integrable_of_hasCompactSupport (μ := volume) hcK
  have hKsq : Integrable (fun z => (|X z|+|Y z|)^2) volume :=
    (hK.memLp_of_hasCompactSupport (p := 2) hcK).integrable_sq
  have hK0 (z : ℂ) : 0 ≤ |X z|+|Y z| := by positivity
  have hKb (z : ℂ) : |X z|+|Y z| ≤ 12/l := by
    have hx' := rectangleTransportX_bound a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z
    have hy' := rectangleTransportY_bound a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z
    have hp : l ≤ Real.pi*l := by nlinarith [Real.pi_gt_three]
    have hx'' := hx'.trans (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8) hl hp)
    change |X z| ≤ _ at hx''
    change |Y z| ≤ _ at hy'
    calc
      _ ≤ 8/l+4/l := add_le_add hx'' hy'
      _ = 12/l := by ring
  have hKI : (∫ z, |X z|+|Y z|) ≤ 10*l := by
    rw [integral_add (hx.integrable_of_hasCompactSupport hcx).abs
      (hy.integrable_of_hasCompactSupport hcy).abs]
    have hx' := rectangleTransportX_integral_abs a b l (Real.pi*l) hl
      (mul_pos Real.pi_pos hl) a' b' ha ha' n
    have hy' := rectangleTransportY_integral_abs a b l (Real.pi*l) hl
      (mul_pos Real.pi_pos hl) a' b' hb hb' n
    change (∫ z, |X z|) ≤ _ at hx'
    change (∫ z, |Y z|) ≤ _ at hy'
    nlinarith [Real.pi_lt_four]
  change (∫ z in V, (|X z|+|Y z|)^2) ≤ _
  calc
    _ ≤ ∫ z, (|X z|+|Y z|)^2 :=
      setIntegral_le_integral hKsq (Eventually.of_forall (fun _ => sq_nonneg _))
    _ ≤ ∫ z, (12/l)*(|X z|+|Y z|) := integral_mono hKsq (hKi.const_mul _) (fun z => by
      nlinarith [mul_le_mul_of_nonneg_right (hKb z) (hK0 z)])
    _ = (12/l)*∫ z, |X z|+|Y z| := integral_const_mul ..
    _ ≤ (12/l)*(10*l) := mul_le_mul_of_nonneg_left hKI (by positivity)
    _ = 120 := by field_simp; ring

lemma openStripRectangle_subset_unit {a b l : ℝ}
    (ha : 0 ≤ a) (ha1 : a+l ≤ 1) (hb : 0 ≤ b) (hb1 : b+Real.pi*l ≤ Real.pi) :
    openStripRectangle a b l ⊆ openUnitStrip := by
  intro z hz
  exact ⟨ha.trans_lt hz.1, hz.2.1.trans_le ha1,
    hb.trans_lt hz.2.2.1, hz.2.2.2.trans_le hb1⟩

lemma local_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) (a b l : ℝ) (hl : 0 < l)
    (ha : 0 ≤ a) (ha1 : a+l ≤ 1) (hb : 0 ≤ b) (hb1 : b+Real.pi*l ≤ Real.pi)
    (a' b' : ℝ) (haa : a ≤ a') (haa' : a'+l/2 ≤ a+l)
    (hbb : b ≤ b') (hbb' : b'+(Real.pi*l)/2 ≤ b+Real.pi*l) :
    |spatialAverage u (stripRectangle a' b' (l/2)) -
      spatialAverage u (stripRectangle a b l)| ≤
      12 * Real.sqrt (∫ z in openStripRectangle a b l, ‖D z‖^2) := by
  have hsub := openStripRectangle_subset_unit ha ha1 hb hb1
  have hsmooth (n : ℕ) :
      |(∫ z in openUnitStrip, u z * rectangleDensity a' b' (l/2) (Real.pi*(l/2))
          (by positivity) (by positivity) n z) -
        (∫ z in openUnitStrip, u z * rectangleDensity a b l (Real.pi*l)
          hl (mul_pos Real.pi_pos hl) n z)| ≤
      12 * Real.sqrt (∫ z in openStripRectangle a b l, ‖D z‖^2) := by
    let X := rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
    let Y := rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
    have hx : ContDiff ℝ ∞ X := rectangleTransportX_contDiff ..
    have hy : ContDiff ℝ ∞ Y := rectangleTransportY_contDiff ..
    have hcx : HasCompactSupport X := rectangleTransportX_compact _ _ _ _ _ _ _ _ haa haa' n
    have hcy : HasCompactSupport Y := rectangleTransportY_compact _ _ _ _ _ _ _ _ hbb hbb' n
    have hsx : tsupport X ⊆ openStripRectangle a b l :=
      rectangleTransportX_support _ _ _ _ _ _ _ _ haa haa' hbb hbb' n
    have hsy : tsupport Y ⊆ openStripRectangle a b l :=
      rectangleTransportY_support _ _ _ _ _ _ _ _ hbb hbb' n
    have he := weak_gradient_pairing hu hx hy hcx hcy (hsx.trans hsub) (hsy.trans hsub)
    change (∫ z in openUnitStrip, u z *
      ((fderiv ℝ (rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n) z) 1 +
       (fderiv ℝ (rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n) z) Complex.I)) = _ at he
    simp_rw [rectangleTransport_divergence, show Real.pi*l/2 = Real.pi*(l/2) by ring, mul_sub] at he
    have hi₁ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
      (complexTensor_contDiff (intervalDensity_smooth a' (l/2) (by positivity) n)
        (intervalDensity_smooth b' (Real.pi*(l/2)) (by positivity) n)).continuous
      (complexTensor_compact (intervalDensity_compact ..) (intervalDensity_compact ..))
    have hi₀ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
      (complexTensor_contDiff (intervalDensity_smooth a l hl n)
        (intervalDensity_smooth b (Real.pi*l) (mul_pos Real.pi_pos hl) n)).continuous
      (complexTensor_compact (intervalDensity_compact ..) (intervalDensity_compact ..))
    dsimp only [rectangleDensity] at he ⊢
    rw [integral_sub hi₁ hi₀] at he
    rw [he, abs_neg]
    refine (integral_pairing_local_le hu.2.1 hsub hx.continuous hy.continuous hcx hcy hsx hsy).trans ?_
    have hbnd := rectangle_transport_L2_bound a b l hl a' b' haa haa' hbb hbb' n
      (openStripRectangle a b l)
    change (∫ z in openStripRectangle a b l, (|X z|+|Y z|)^2) ≤ 120 at hbnd
    have hE : 0 ≤ ∫ z in openStripRectangle a b l, ‖D z‖^2 := integral_nonneg (fun _ => sq_nonneg _)
    have hA : 0 ≤ ∫ z in openStripRectangle a b l, (|X z|+|Y z|)^2 := integral_nonneg (fun _ => sq_nonneg _)
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hA, mul_pow, Real.sq_sqrt hE]
    nlinarith [mul_le_mul_of_nonneg_left hbnd hE]
  have hlim₀ := rectangle_smoothed_mean_tendsto hu.1 a b l hl ha ha1 hb hb1
  have hlim₁ := rectangle_smoothed_mean_tendsto hu.1 a' b' (l/2) (by positivity)
    (ha.trans haa) (haa'.trans ha1) (hb.trans hbb) (by nlinarith)
  exact le_of_tendsto (hlim₁.sub hlim₀).abs (Eventually.of_forall hsmooth)

end SLEExactGauge
end
end

end OAI
