import OAI.Geometry.Perimeter.Regularity.GradientContDiff

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

def pairedCutTest {n : ℕ} (c : Euc n) (a b : ℝ)
    (V W : Euc n → Euc n) (x : Euc n) : Euc n :=
  V x + annularCutoff c a b x • (W x - V x)

theorem pairedCutTest_eq {n : ℕ} (c : Euc n) (a b : ℝ)
    (V W : Euc n → Euc n) (x : Euc n) :
    pairedCutTest c a b V W x =
      (1 - annularCutoff c a b x) • V x + annularCutoff c a b x • W x := by
  unfold pairedCutTest
  module

theorem pairedCutTest_admissible {n : ℕ} {U : Set (Euc n)}
    {V W : Euc n → Euc n} (hV : PerimeterAdmissible univ V)
    (hW : PerimeterAdmissible U W) {c : Euc n} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hB : Metric.closedBall c b ⊆ U) :
    PerimeterAdmissible U (pairedCutTest c a b V W) := by
  have hs : tsupport (pairedCutTest c a b V W) ⊆ Metric.closedBall c b ∪ tsupport W := by
    apply closure_minimal
    · intro x hx
      by_contra hh
      have hxb : b ≤ dist x c := le_of_lt (lt_of_not_ge (fun hb ↦ hh (Or.inl hb)))
      have hxW : x ∉ tsupport W := fun hw ↦ hh (Or.inr hw)
      exact hx (by simp [pairedCutTest, annularCutoff_one ha hab hxb,
        image_eq_zero_of_notMem_tsupport hxW])
    · exact Metric.isClosed_closedBall.union (isClosed_tsupport _)
  refine ⟨hV.1.add ((annularCutoff_contDiff c a b).smul (hW.1.sub hV.1)),
    ((isCompact_closedBall c b).union hW.2.1).of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (union_subset hB hW.2.2.1), ?_⟩
  intro x
  rw [pairedCutTest_eq]
  have hη := annularCutoff_mem_Icc c a b x
  calc
    _ ≤ ‖(1 - annularCutoff c a b x) • V x‖ + ‖annularCutoff c a b x • W x‖ := norm_add_le _ _
    _ = (1 - annularCutoff c a b x) * ‖V x‖ + annularCutoff c a b x * ‖W x‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη.1, abs_of_nonneg (sub_nonneg.mpr hη.2)]
    _ ≤ (1 - annularCutoff c a b x) * 1 + annularCutoff c a b x * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (hV.2.2.2 x) (sub_nonneg.mpr hη.2))
        (mul_le_mul_of_nonneg_left (hW.2.2.2 x) hη.1)
    _ = 1 := by ring

theorem divergence_sub {n : ℕ} {V W : Euc n → Euc n}
    (hV : Differentiable ℝ V) (hW : Differentiable ℝ W) :
    divergence (V - W) = divergence V - divergence W := by
  funext x
  simp only [divergence, fderiv_sub (hV x) (hW x), sub_apply,
    inner_sub_right, Finset.sum_sub_distrib, Pi.sub_apply]

theorem divergence_pairedCutTest {n : ℕ} {c : Euc n} {a b : ℝ}
    {V W : Euc n → Euc n} (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (x : Euc n) :
    divergence (pairedCutTest c a b V W) x =
      divergence V x + annularCutoff c a b x * (divergence W x - divergence V x) +
        inner ℝ (gradient (annularCutoff c a b) x) (W x - V x) := by
  have hdV := hV.differentiable (by norm_num)
  have hdW := hW.differentiable (by norm_num)
  have hdη := (annularCutoff_contDiff c a b).differentiable (by norm_num)
  change divergence (V + (fun y ↦ annularCutoff c a b y • (W - V) y)) x = _
  rw [divergence_add (W := fun y ↦ annularCutoff c a b y • (W - V) y)
    hdV (hdη.smul (hdW.sub hdV))]
  change divergence V x + divergence (fun y ↦ annularCutoff c a b y • (W y - V y)) x = _
  rw [divergence_smul (V := fun y ↦ W y - V y) hdη (hdW.sub hdV)]
  rw [show divergence (fun y ↦ W y - V y) x = divergence W x - divergence V x from
    congrFun (divergence_sub hdW hdV) x]
  ring

theorem integrable_annularCutoff_mul {n : ℕ} {f : Euc n → ℝ}
    (hf : Integrable f volume) (c : Euc n) (a b : ℝ) :
    Integrable (fun x ↦ annularCutoff c a b x * f x) volume := by
  apply hf.norm.mono' (((annularCutoff_contDiff c a b).continuous.aestronglyMeasurable).mul
    hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖annularCutoff c a b x * f x‖ ≤ ‖f x‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (annularCutoff_mem_Icc c a b x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (annularCutoff_mem_Icc c a b x).2

theorem integral_pairedCut_le {n : ℕ} {E U : Set (Euc n)}
    {V W : Euc n → Euc n} (hV : PerimeterAdmissible univ V)
    (hW : PerimeterAdmissible U W) {c : Euc n} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hB : Metric.closedBall c b ⊆ U)
    (hfin : perimeter E U ≠ ⊤) :
    (∫ x in E, divergence V x + annularCutoff c a b x * (divergence W x - divergence V x)) ≤
      (perimeter E U).toReal + 2 * ∫ x in E, ‖gradient (annularCutoff c a b) x‖ := by
  have hZ := pairedCutTest_admissible hV hW ha hab hB
  have hdV := integrable_divergence hV.1 hV.2.1
  have hdW := integrable_divergence hW.1 hW.2.1
  have hm : Integrable (fun x ↦ divergence V x +
      annularCutoff c a b x * (divergence W x - divergence V x)) volume :=
    hdV.add (integrable_annularCutoff_mul (hdW.sub hdV) c a b)
  have hg : Integrable (fun x ↦ ‖gradient (annularCutoff c a b) x‖) volume :=
    ((gradient_annularCutoff_continuous c a b).integrable_of_hasCompactSupport
    (gradient_annularCutoff_compact c ha hab)).norm
  have hinner : ∀ x, |inner ℝ (gradient (annularCutoff c a b) x) (W x - V x)| ≤
      2 * ‖gradient (annularCutoff c a b) x‖ := by
    intro x
    calc
      _ ≤ ‖gradient (annularCutoff c a b) x‖ * ‖W x - V x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖gradient (annularCutoff c a b) x‖ * 2 := by
        gcongr
        exact (norm_sub_le _ _).trans (by linarith [hV.2.2.2 x, hW.2.2.2 x])
      _ = _ := by ring
  have hi : Integrable (fun x ↦ inner ℝ (gradient (annularCutoff c a b) x) (W x - V x)) volume :=
    (hg.const_mul 2).mono'
      ((gradient_annularCutoff_continuous c a b).inner (hW.1.continuous.sub hV.1.continuous)).aestronglyMeasurable
      (Eventually.of_forall hinner)
  have hp : (∫ x in E, divergence (pairedCutTest c a b V W) x) ≤ (perimeter E U).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    rw [perimeter_eq_iSup_tests]
    exact le_iSup_of_le _ (le_iSup_of_le hZ le_rfl)
  simp_rw [divergence_pairedCutTest hV.1 hW.1] at hp
  rw [integral_add hm.integrableOn hi.integrableOn] at hp
  have herr : -(∫ x in E, inner ℝ (gradient (annularCutoff c a b) x) (W x - V x)) ≤
      2 * ∫ x in E, ‖gradient (annularCutoff c a b) x‖ := by
    rw [← integral_neg, ← integral_const_mul]
    exact integral_mono hi.integrableOn.neg (hg.const_mul 2).integrableOn
      (fun x ↦ (neg_le_abs _).trans (hinner x))
  linarith

theorem tendsto_integral_annularCutoff_mul {n : ℕ} {E : Set (Euc n)}
    {f : Euc n → ℝ} (hf : Integrable f volume) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun δ : ℝ ↦ ∫ x in E, annularCutoff c (r + δ) (r + 2 * δ) x * f x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in E \ Metric.closedBall c r, f x)) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict E) (l := 𝓝[>] (0 : ℝ))
    (F := fun δ x ↦ annularCutoff c (r + δ) (r + 2 * δ) x * f x)
    (f := (Metric.closedBall c r)ᶜ.indicator f) (fun x ↦ ‖f x‖)
    (Eventually.of_forall fun δ ↦ (integrable_annularCutoff_mul hf c _ _).integrableOn.aestronglyMeasurable)
    (Eventually.of_forall fun δ ↦ Eventually.of_forall fun x ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (annularCutoff_mem_Icc c _ _ x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (annularCutoff_mem_Icc c _ _ x).2)
    hf.norm.integrableOn (Eventually.of_forall fun x ↦ ?_)
  · simpa only [integral_indicator measurableSet_closedBall.compl,
      Measure.restrict_restrict measurableSet_closedBall.compl, inter_comm, ← sdiff_eq] using ht
  · convert (annularCutoff_tendsto c x hr).mul (tendsto_const_nhds (x := f x)) using 1
    by_cases hx : x ∈ (Metric.closedBall c r)ᶜ <;> simp [hx]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem nonnegative_perimeter_test_replacement {n : ℕ} (E U : Set (Euc n))
    {V : Euc n → Euc n} (hV : PerimeterAdmissible U V) :
    ∃ W : Euc n → Euc n, PerimeterAdmissible U W ∧
      0 ≤ ∫ x in E, divergence W x ∧
      ENNReal.ofReal (∫ x in E, divergence W x) = ENNReal.ofReal (∫ x in E, divergence V x) := by
  by_cases h : 0 ≤ ∫ x in E, divergence V x
  · exact ⟨V, hV, h, rfl⟩
  · refine ⟨fun _ ↦ 0, perimeterAdmissible_zero U, ?_, ?_⟩
    · simp [divergence]
    · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge h)]
      simp [divergence]

theorem perimeter_add_le_of_pair_integrals {n : ℕ} (E F U V : Set (Euc n)) (K : ℝ)
    (h : ∀ X Y : Euc n → Euc n, PerimeterAdmissible U X → PerimeterAdmissible V Y →
      (∫ x in E, divergence X x) + (∫ x in F, divergence Y x) ≤ K) :
    perimeter E U + perimeter F V ≤ ENNReal.ofReal K := by
  rw [perimeter_eq_iSup_tests, perimeter_eq_iSup_tests]
  apply ENNReal.biSup_add_biSup_le' ⟨_, perimeterAdmissible_zero U⟩ ⟨_, perimeterAdmissible_zero V⟩
  intro X hX Y hY
  obtain ⟨X', hX', hnX, hvalX⟩ := nonnegative_perimeter_test_replacement E U hX
  obtain ⟨Y', hY', hnY, hvalY⟩ := nonnegative_perimeter_test_replacement F V hY
  rw [← hvalX, ← hvalY, ← ENNReal.ofReal_add hnX hnY]
  exact ENNReal.ofReal_le_ofReal (h X' Y' hX' hY')

theorem controlled_radius_perimeter_cut {n : ℕ} {E U : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) {r B D L : ℝ}
    (hr : 0 < r) (hrB : r < B) (hBU : Metric.closedBall c B ⊆ U)
    (hcontrol : ∀ t ∈ Icc r B,
      volume.real (E ∩ Metric.closedBall c t) - volume.real (E ∩ Metric.closedBall c r) ≤
        D * (t - r))
    (hD : 0 ≤ D) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L)
    (hfin : perimeter E U ≠ ⊤) :
    perimeter (E ∩ Metric.closedBall c r) univ + perimeter (E \ Metric.closedBall c r) U ≤
      perimeter E U + ENNReal.ofReal (8 * L * D) := by
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)]
  apply perimeter_add_le_of_pair_integrals
  intro V W hV hW
  have hdV := integrable_divergence hV.1 hV.2.1
  have hdW := integrable_divergence hW.1 hW.2.1
  have ht : Tendsto (fun δ : ℝ ↦ ∫ x in E,
      divergence V x + annularCutoff c (r + δ) (r + 2 * δ) x * (divergence W x - divergence V x))
      (𝓝[>] (0 : ℝ)) (𝓝 ((∫ x in E ∩ Metric.closedBall c r, divergence V x) +
        (∫ x in E \ Metric.closedBall c r, divergence W x))) := by
    have hlim := (tendsto_const_nhds (x := ∫ x in E, divergence V x)).add
      (tendsto_integral_annularCutoff_mul (E := E) (hdW.sub hdV) c hr)
    have heq : (∫ x in E, divergence V x) +
        (∫ x in E \ Metric.closedBall c r, (divergence W - divergence V) x) =
        (∫ x in E ∩ Metric.closedBall c r, divergence V x) +
        (∫ x in E \ Metric.closedBall c r, divergence W x) := by
      simp only [Pi.sub_apply]
      rw [integral_sub hdW.integrableOn hdV.integrableOn]
      have hsplit := integral_inter_add_sdiff (s := E) (t := Metric.closedBall c r) measurableSet_closedBall hdV.integrableOn
      linarith
    rw [heq] at hlim
    convert hlim using 1
    ext δ
    exact integral_add hdV.integrableOn
      (integrable_annularCutoff_mul (hdW.sub hdV) c _ _).integrableOn
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < (B - r) / 2 by linarith))] with δ hδ hsmall
  change 0 < δ at hδ
  change δ < (B - r) / 2 at hsmall
  have hδB : r + 2 * δ ≤ B := by linarith
  have hp := integral_pairedCut_le hV hW (c := c)
    (show 0 < r + δ by positivity) (show r + δ < r + 2 * δ by linarith)
    ((Metric.closedBall_subset_closedBall hδB).trans hBU) hfin
  have hg := controlled_radius_gradient_bound hE c hr hδ hδB hcontrol hD hL hbound
  linarith

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem minimizing_controlled_radius_perimeter_le {n : ℕ} {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (c : Euc n) {r B D L : ℝ}
    (hr : 0 < r) (hrB : r < B)
    (hcontrol : ∀ t ∈ Icc r B,
      volume.real (E ∩ Metric.closedBall c t) - volume.real (E ∩ Metric.closedBall c r) ≤
        D * (t - r))
    (hD : 0 ≤ D) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) :
    perimeter (E ∩ Metric.closedBall c r) univ ≤ ENNReal.ofReal (8 * L * D) := by
  let U := Metric.ball c (B + 1)
  let F := E \ Metric.closedBall c r
  have hfin : perimeter E U ≠ ⊤ := (hmin.2.1 c (B + 1) (by linarith)).ne
  have hcut := controlled_radius_perimeter_cut hmin.1 c hr hrB
    (show Metric.closedBall c B ⊆ U from Metric.closedBall_subset_ball (by linarith))
    hcontrol hD hL hbound hfin
  have hcl : closure (symmDiff E F) ⊆ Metric.closedBall c r := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hc
    rcases hx with hx | hx
    · exact hx.2 ⟨hx.1, hc⟩
    · exact hx.2 hx.1.1
  have hcmp : perimeter E U ≤ perimeter F U :=
    hmin.2.2 c (B + 1) (by linarith) F (hmin.1.diff measurableSet_closedBall)
      ((isCompact_closedBall c r).of_isClosed_subset isClosed_closure hcl)
      (hcl.trans (Metric.closedBall_subset_ball (by linarith)))
  have hout : perimeter F U ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩)
    ((le_add_left le_rfl).trans hcut)
  have hlast := hcut.trans (add_le_add hcmp le_rfl)
  rw [add_comm (perimeter (E ∩ Metric.closedBall c r) univ)] at hlast
  exact (ENNReal.add_le_add_iff_left hout).mp hlast

theorem exists_minimizing_volume_cut {n : ℕ} {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (c : Euc n) {a b L : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hv : 0 < volume.real (E ∩ Metric.closedBall c b))
    (hL : 0 < L) (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) :
    ∃ r ∈ Ico a b, perimeter (E ∩ Metric.closedBall c r) univ ≤
      ENNReal.ofReal (16 * L * volume.real (E ∩ Metric.closedBall c b) / (b - a)) := by
  let D := 2 * volume.real (E ∩ Metric.closedBall c b) / (b - a)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDwidth : D * (b - a) = 2 * volume.real (E ∩ Metric.closedBall c b) := by
    dsimp [D]
    exact div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  obtain ⟨r, hr, hcontrol⟩ := exists_controlled_cut_radius E c ha hab
    (show volume.real (E ∩ Metric.closedBall c b) < D * (b - a) by rw [hDwidth]; linarith)
  refine ⟨r, hr, ?_⟩
  have h := minimizing_controlled_radius_perimeter_le hmin c (ha.trans_le hr.1) hr.2
    hcontrol hD.le hL hbound
  convert h using 1
  dsimp [D]
  congr 1
  ring

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem nonlinear_iteration_geometric_bound {u : ℕ → ℝ} {p C B A q : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hu : ∀ i, 0 ≤ u i) (hstart : u 0 ≤ A)
    (hstep : ∀ i, u (i + 1) ≤ C * B ^ i * (u i) ^ p)
    (hAstep : C * A ^ p ≤ A * q) (hqstep : B * q ^ p ≤ q) :
    ∀ i, u i ≤ A * q ^ i := by
  intro i
  induction i with
  | zero => simpa using hstart
  | succ i ih =>
    have hpow : (q ^ i) ^ p = (q ^ p) ^ i := by
      rw [← Real.rpow_natCast_mul hq, mul_comm (i : ℝ), Real.rpow_mul_natCast hq]
    calc
      u (i + 1) ≤ C * B ^ i * (u i) ^ p := hstep i
      _ ≤ C * B ^ i * (A * q ^ i) ^ p := by gcongr; exact hu i
      _ = (C * A ^ p) * (B * q ^ p) ^ i := by
        rw [Real.mul_rpow hA (pow_nonneg hq _), hpow, mul_pow]
        ring
      _ ≤ (A * q) * q ^ i := by
        exact mul_le_mul hAstep (pow_le_pow_left₀ (mul_nonneg hB (Real.rpow_nonneg hq _)) hqstep i)
          (pow_nonneg (mul_nonneg hB (Real.rpow_nonneg hq _)) _) (mul_nonneg hA hq)
      _ = A * q ^ (i + 1) := by rw [pow_succ]; ring

theorem exists_nonlinear_iteration_threshold {p C B : ℝ}
    (hp : 1 < p) (hC : 0 < C) (hB : 1 < B) :
    ∃ A q : ℝ, 0 < A ∧ 0 < q ∧ q < 1 ∧
      C * A ^ p ≤ A * q ∧ B * q ^ p ≤ q := by
  let q := (1 / (2 * B)) ^ (p - 1)⁻¹
  have he : 0 < p - 1 := by linarith
  have hbase : 0 < 1 / (2 * B) := by positivity
  have hq : 0 < q := Real.rpow_pos_of_pos hbase _
  have hq1 : q < 1 := by
    apply Real.rpow_lt_one hbase.le _ (inv_pos.mpr he)
    rw [div_lt_one (by linarith : 0 < 2 * B)]
    linarith
  have hqpow : q ^ (p - 1) = 1 / (2 * B) := by
    dsimp [q]
    rw [← Real.rpow_mul hbase.le, inv_mul_cancel₀ he.ne', Real.rpow_one]
  let A := (q / (2 * C)) ^ (p - 1)⁻¹
  have hbaseA : 0 < q / (2 * C) := by positivity
  have hA : 0 < A := Real.rpow_pos_of_pos hbaseA _
  have hApow : A ^ (p - 1) = q / (2 * C) := by
    dsimp [A]
    rw [← Real.rpow_mul hbaseA.le, inv_mul_cancel₀ he.ne', Real.rpow_one]
  have hrewrite : p = (p - 1) + 1 := by ring
  refine ⟨A, q, hA, hq, hq1, ?_, ?_⟩
  · rw [hrewrite, Real.rpow_add hA, hApow, Real.rpow_one]
    have heq : C * (q / (2 * C) * A) = A * q / 2 := by field_simp
    rw [heq]
    nlinarith
  · rw [hrewrite, Real.rpow_add hq, hqpow, Real.rpow_one]
    have heq : B * (1 / (2 * B) * q) = q / 2 := by field_simp
    rw [heq]
    linarith

theorem nonlinear_iteration_tendsto_zero {p C B : ℝ}
    (hp : 1 < p) (hC : 0 < C) (hB : 1 < B) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℕ → ℝ, (∀ i, 0 ≤ u i) → u 0 ≤ A →
      (∀ i, u (i + 1) ≤ C * B ^ i * (u i) ^ p) → Tendsto u atTop (𝓝 0) := by
  obtain ⟨A, q, hA, hq, hq1, hAstep, hqstep⟩ := exists_nonlinear_iteration_threshold hp hC hB
  refine ⟨A, hA, ?_⟩
  intro u hu hstart hstep
  have hmajor := nonlinear_iteration_geometric_bound (by linarith : 0 ≤ p) hC.le
    (by linarith : 0 ≤ B) hA.le hq.le hu hstart hstep hAstep hqstep
  apply squeeze_zero hu hmajor
  simpa using (tendsto_const_nhds (x := A)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem minimizing_volume_recursion {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (c : Euc n) {a b L : ℝ}
    (ha : 0 < a) (hab : a < b) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) :
    volume.real (E ∩ Metric.closedBall c a) ≤
      (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p : ℝ) *
        (16 * L * volume.real (E ∩ Metric.closedBall c b) / (b - a)) ^ p := by
  have hv : 0 ≤ volume.real (E ∩ Metric.closedBall c b) := ENNReal.toReal_nonneg
  by_cases hz : volume.real (E ∩ Metric.closedBall c b) = 0
  · have hm : volume.real (E ∩ Metric.closedBall c a) ≤ 0 := by
      rw [← hz]
      exact measureReal_mono
        (inter_subset_inter_right E (Metric.closedBall_subset_closedBall hab.le))
        (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c b).measure_ne_top)
    exact hm.trans (by positivity)
  obtain ⟨r, hr, hcut⟩ := exists_minimizing_volume_cut hmin c ha hab
    (lt_of_le_of_ne hv (Ne.symm hz)) hL hbound
  have hiso := raw_perimeter_isoperimetric hp (hmin.1.inter measurableSet_closedBall)
    (((isCompact_closedBall c r).isBounded).subset inter_subset_right)
  have hvol : volume (E ∩ Metric.closedBall c a) ≤
      (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p : ℝ≥0∞) *
        (ENNReal.ofReal (16 * L * volume.real (E ∩ Metric.closedBall c b) / (b - a))) ^ p := by
    calc
      _ ≤ volume (E ∩ Metric.closedBall c r) := measure_mono
        (inter_subset_inter_right E (Metric.closedBall_subset_closedBall hr.1))
      _ ≤ _ := hiso.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hcut hp.symm.pos.le) _)
  have hQ : 0 ≤ 16 * L * volume.real (E ∩ Metric.closedBall c b) / (b - a) := by positivity
  have hne : (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p : ℝ≥0∞) *
      (ENNReal.ofReal (16 * L * volume.real (E ∩ Metric.closedBall c b) / (b - a))) ^ p ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.coe_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg hp.symm.pos.le ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hne hvol
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hQ] at hreal
  simpa only [measureReal_def, ENNReal.coe_toReal] using hreal

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

def clearingRadius (R : ℝ) (i : ℕ) : ℝ := R / 2 + R / (2 * (2 : ℝ) ^ i)

theorem clearingRadius_zero (R : ℝ) : clearingRadius R 0 = R := by
  simp [clearingRadius]

theorem clearingRadius_sub_succ (R : ℝ) (i : ℕ) :
    clearingRadius R i - clearingRadius R (i + 1) = R / (4 * (2 : ℝ) ^ i) := by
  unfold clearingRadius
  rw [pow_succ]
  field_simp
  ring

theorem clearingRadius_pos {R : ℝ} (hR : 0 < R) (i : ℕ) : 0 < clearingRadius R i := by
  unfold clearingRadius
  positivity

theorem clearingRadius_half_le {R : ℝ} (hR : 0 ≤ R) (i : ℕ) : R / 2 ≤ clearingRadius R i := by
  unfold clearingRadius
  exact le_add_of_nonneg_right (div_nonneg hR (by positivity))

theorem clearingRadius_succ_lt {R : ℝ} (hR : 0 < R) (i : ℕ) :
    clearingRadius R (i + 1) < clearingRadius R i := by
  have hpos : 0 < clearingRadius R i - clearingRadius R (i + 1) := by
    rw [clearingRadius_sub_succ]
    positivity
  linarith

theorem minimizing_clearing_out {n : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (n : ℝ) p) {R : ℝ} (hR : 0 < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ c : Euc n, volume.real (E ∩ Metric.closedBall c R) ≤ ε →
        volume (E ∩ Metric.closedBall c (R / 2)) = 0 := by
  obtain ⟨L, hL, hbound⟩ := exists_smoothTransition_deriv_bound
  let S : ℝ := lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc n)) p
  let K : ℝ := 64 * L / R
  let C : ℝ := (S + 1) * K ^ p
  let B : ℝ := (2 : ℝ) ^ p
  have hS : 0 ≤ S := NNReal.coe_nonneg _
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hp1 : 1 < p := hp.symm.lt
  have hB : 1 < B := Real.one_lt_rpow (by norm_num) (by linarith)
  obtain ⟨ε, hε, hiteration⟩ := nonlinear_iteration_tendsto_zero hp1 hC hB
  refine ⟨ε, hε, ?_⟩
  intro E hmin c hsmall
  let u : ℕ → ℝ := fun i ↦ volume.real (E ∩ Metric.closedBall c (clearingRadius R i))
  have hu : ∀ i, 0 ≤ u i := fun _ ↦ ENNReal.toReal_nonneg
  have hstart : u 0 ≤ ε := by simpa only [u, clearingRadius_zero] using hsmall
  have hstep : ∀ i, u (i + 1) ≤ C * B ^ i * (u i) ^ p := by
    intro i
    have hm := minimizing_volume_recursion hp hmin c (clearingRadius_pos hR (i + 1))
      (clearingRadius_succ_lt hR i) hL hbound
    have heq : 16 * L * u i / (clearingRadius R i - clearingRadius R (i + 1)) = K * (2 : ℝ) ^ i * u i := by
      rw [clearingRadius_sub_succ]
      dsimp [K]
      field_simp
      ring
    change u (i + 1) ≤ S * (16 * L * u i /
      (clearingRadius R i - clearingRadius R (i + 1))) ^ p at hm
    rw [heq] at hm
    have hpow : ((2 : ℝ) ^ i) ^ p = ((2 : ℝ) ^ p) ^ i := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
        mul_comm (i : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      u (i + 1) ≤ S * (K * (2 : ℝ) ^ i * u i) ^ p := hm
      _ = (S * K ^ p) * B ^ i * (u i) ^ p := by
        rw [Real.mul_rpow (by positivity) (hu i),
          Real.mul_rpow hK.le (by positivity), hpow]
        dsimp [B]
        ring
      _ ≤ C * B ^ i * (u i) ^ p := by
        unfold C
        gcongr
        linarith
  have ht := hiteration u hu hstart hstep
  have hzero : volume.real (E ∩ Metric.closedBall c (R / 2)) = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun i ↦ measureReal_mono
      (inter_subset_inter_right E (Metric.closedBall_subset_closedBall (clearingRadius_half_le hR.le i)))
      (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c (clearingRadius R i)).measure_ne_top)
  exact ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right
    (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c (R / 2)).measure_ne_top)

end RPISingularHarnack

end

end OAI
