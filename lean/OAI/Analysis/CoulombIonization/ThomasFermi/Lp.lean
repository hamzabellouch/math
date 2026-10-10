import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfWeight

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
abbrev TFLp (μ : Measure α) := Lp ℝ (5 / 3) μ

def NonnegDensity (f : TFLp μ) : Prop := ∀ᵐ x ∂μ, 0 ≤ f x

def densityWeight (f g : TFLp μ) : ℝ := ∫ x, tfWeight (f x) (g x) ∂μ

lemma tfLp_norm_rpow (f : TFLp μ) :
    ‖f‖ ^ (5 / 3 : ℝ) = ∫ x, |f x| ^ (5 / 3 : ℝ) ∂μ := by
  have he := (Lp.memLp f).eLpNorm_eq_integral_rpow_norm
    (by norm_num : (5 / 3 : ENNReal) ≠ 0) (ENNReal.div_ne_top (by norm_num) (by norm_num))
  rw [Lp.norm_def, he, ENNReal.toReal_ofReal (by positivity)]
  norm_num
  rw [← Real.rpow_mul (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
  norm_num

lemma tfLp_norm_rpow_nonneg {f : TFLp μ} (hf : NonnegDensity f) :
    ‖f‖ ^ (5 / 3 : ℝ) = ∫ x, f x ^ (5 / 3 : ℝ) ∂μ := by
  rw [tfLp_norm_rpow]
  exact integral_congr_ae (hf.mono fun x hx => by dsimp only; rw [abs_of_nonneg hx])

lemma nonnegDensity_add {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    NonnegDensity (f + g) := by
  filter_upwards [Lp.coeFn_add f g, hf, hg] with x he hx hy
  rw [he]
  exact add_nonneg hx hy

lemma densityWeight_nonneg {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    0 ≤ densityWeight f g := by
  apply integral_nonneg_of_ae
  filter_upwards [hf, hg] with x hx hy
  exact tfWeight_nonneg hx hy

lemma tfLp_interpolation {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    ‖f - g‖ ^ (5 / 3 : ℝ) ≤
      densityWeight f g ^ (5 / 6 : ℝ) * ‖f + g‖ ^ (5 / 18 : ℝ) := by
  have hi := tfWeight_integral_interpolation (Lp.memLp f) (Lp.memLp g) hf hg
  have hd : ‖f - g‖ ^ (5 / 3 : ℝ) = ∫ x, |f x - g x| ^ (5 / 3 : ℝ) ∂μ := by
    rw [tfLp_norm_rpow]
    exact integral_congr_ae (Lp.coeFn_sub f g |>.mono fun x hx => by dsimp only; rw [hx]; rfl)
  have hs : ‖f + g‖ ^ (5 / 3 : ℝ) = ∫ x, (f x + g x) ^ (5 / 3 : ℝ) ∂μ := by
    rw [tfLp_norm_rpow_nonneg (nonnegDensity_add hf hg)]
    exact integral_congr_ae (Lp.coeFn_add f g |>.mono fun x hx => by dsimp only; rw [hx]; rfl)
  rw [← hd, ← hs, ← Real.rpow_mul (norm_nonneg _)] at hi
  norm_num at hi
  exact hi

lemma isClosed_nonnegDensity : IsClosed ({f | NonnegDensity (μ := μ) f}) := by
  apply isClosed_of_closure_subset
  intro f hf
  obtain ⟨u, hu, huf⟩ := mem_closure_iff_seq_limit.mp hf
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp huf).exists_seq_tendsto_ae
  have hnn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ (u (ns n)) x := ae_all_iff.mpr fun n => hu (ns n)
  filter_upwards [hns, hnn] with x hx hn
  exact ge_of_tendsto hx (Eventually.of_forall hn)

theorem exists_minimizer_of_tf_gap {C : Set (TFLp μ)} (hC : IsClosed C) (hne : C.Nonempty)
    (hn : ∀ f ∈ C, NonnegDensity f)
    (hm : ∀ f ∈ C, ∀ g ∈ C, (1 / 2 : ℝ) • (f + g) ∈ C)
    {F : TFLp μ → ℝ} (hF : ContinuousOn F C) (hbelow : BddBelow (F '' C))
    (hcoercive : ∀ a : ℝ, ∃ B : ℝ, ∀ f ∈ C, F f ≤ a → ‖f‖ ≤ B)
    {T : ℝ} (hT : 0 < T)
    (hgap : ∀ f ∈ C, ∀ g ∈ C,
      T * densityWeight f g ≤ (F f + F g) / 2 - F ((1 / 2 : ℝ) • (f + g))) :
    ∃ f ∈ C, ∀ g ∈ C, F f ≤ F g := by
  obtain ⟨v, hvmono, hvlim, hv⟩ := exists_seq_tendsto_sInf (hne.image F) hbelow
  choose u hu huv using hv
  have hulim : Tendsto (fun n => F (u n)) atTop (𝓝 (sInf (F '' C))) := by
    simpa only [huv] using hvlim
  obtain ⟨B, hB⟩ := hcoercive (v 0)
  have hub (n : ℕ) : ‖u n‖ ≤ B := hB _ (hu n) (by rw [huv]; exact hvmono (Nat.zero_le n))
  have hB0 : 0 ≤ B := (norm_nonneg (u 0)).trans (hub 0)
  have hlow (f) (hf : f ∈ C) : sInf (F '' C) ≤ F f := csInf_le hbelow ⟨f, hf, rfl⟩
  have hvnonneg (n : ℕ) : 0 ≤ v n - sInf (F '' C) := by rw [← huv]; exact sub_nonneg.mpr (hlow _ (hu n))
  have hlim : Tendsto (fun n => ((v n - sInf (F '' C)) / T) ^ (5 / 6 : ℝ) *
      (2 * B) ^ (5 / 18 : ℝ)) atTop (𝓝 0) := by
    have hh := ((hvlim.sub_const (sInf (F '' C))).div_const T).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 5 / 6))
    simpa using hh.mul_const ((2 * B) ^ (5 / 18 : ℝ))
  have huc : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hεp : 0 < ε ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos hε _
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hεp)
    refine ⟨N, fun m hm' n hn' => ?_⟩
    have hw := hgap (u m) (hu m) (u n) (hu n)
    have hmid := hlow _ (hm (u m) (hu m) (u n) (hu n))
    have hvm := hvmono hm'
    have hvn := hvmono hn'
    rw [huv, huv] at hw
    have hweight : densityWeight (u m) (u n) ≤ (v N - sInf (F '' C)) / T := by
      apply (le_div_iff₀ hT).mpr
      nlinarith
    have hib := tfLp_interpolation (hn _ (hu m)) (hn _ (hu n))
    have hsum : ‖u m + u n‖ ≤ 2 * B := (norm_add_le _ _).trans (by linarith [hub m, hub n])
    have hmul : densityWeight (u m) (u n) ^ (5 / 6 : ℝ) * ‖u m + u n‖ ^ (5 / 18 : ℝ) ≤
        ((v N - sInf (F '' C)) / T) ^ (5 / 6 : ℝ) * (2 * B) ^ (5 / 18 : ℝ) := by
      exact mul_le_mul
        (Real.rpow_le_rpow (densityWeight_nonneg (hn _ (hu m)) (hn _ (hu n))) hweight (by norm_num))
        (Real.rpow_le_rpow (norm_nonneg _) hsum (by norm_num))
        (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (div_nonneg (hvnonneg N) hT.le) _)
    rw [dist_eq_norm]
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le (by norm_num : (0 : ℝ) < 5 / 3)).mp
      (hib.trans hmul |>.trans_lt (hN N le_rfl))
  obtain ⟨f, huf⟩ := cauchySeq_tendsto_of_complete huc
  have hf : f ∈ C := hC.mem_of_tendsto huf (Eventually.of_forall hu)
  have hfe : F f = sInf (F '' C) := by
    apply tendsto_nhds_unique _ hulim
    exact (hF.continuousWithinAt hf).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨huf, Eventually.of_forall hu⟩)
  exact ⟨f, hf, fun g hg => hfe ▸ hlow g hg⟩

end

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

abbrev TFSpace := EuclideanSpace ℝ (Fin 3)
def ballMeasure (R : ℝ) : Measure TFSpace := volume.restrict (ball 0 R)
instance (R : ℝ) : IsFiniteMeasure (ballMeasure R) := by
  apply isFiniteMeasure_restrict.mpr
  exact (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
    (isCompact_closedBall (0 : TFSpace) R).measure_lt_top).ne

lemma norm_inv_power_integrable_ball (R : ℝ) :
    IntegrableOn (fun x : TFSpace => ‖x‖ ^ (-5 / 2 : ℝ)) (ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp [TFSpace])
    (show (5 / 2 : ℝ) < Module.finrank ℝ TFSpace by simp [TFSpace]; norm_num)
    (C := 1)
  · exact Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; simp [neg_div]
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma coulomb_power_integrable (R : ℝ) :
    Integrable (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖ ^ (-5 / 2 : ℝ))
      ((ballMeasure R).prod (ballMeasure R)) := by
  have h1 := (norm_inv_power_integrable_ball (2 * R)).integrable_indicator measurableSet_ball
  have h2 : Integrable ((ball (0 : TFSpace) R).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (isFiniteMeasure_restrict.mp
      (inferInstance : IsFiniteMeasure (ballMeasure R)))).integrable_indicator measurableSet_ball
  have hm := h1.mul_prod h2
  have ht := (measurePreserving_sub_prod (volume : Measure TFSpace) volume).integrable_comp
    hm.aestronglyMeasurable |>.mpr hm
  rw [ballMeasure, Measure.prod_restrict]
  apply (ht.restrict).mono'
    ((measurable_fst.sub measurable_snd).norm.pow_const _).aestronglyMeasurable
  rw [ae_restrict_iff' (measurableSet_ball.prod measurableSet_ball)]
  exact Eventually.of_forall fun p hp => by
    have hn : p.1 - p.2 ∈ ball (0 : TFSpace) (2 * R) := by
      rw [mem_ball_zero_iff]
      exact (norm_sub_le _ _).trans_lt (by
        have hpx := mem_ball_zero_iff.mp hp.1
        have hpy := mem_ball_zero_iff.mp hp.2
        linarith)
    change ‖‖p.1 - p.2‖ ^ (-5 / 2 : ℝ)‖ ≤
      (ball (0 : TFSpace) (2 * R)).indicator (fun x => ‖x‖ ^ (-5 / 2 : ℝ)) (p.1 - p.2) *
        (ball (0 : TFSpace) R).indicator (fun _ => (1 : ℝ)) p.2
    simp [hn, hp.2, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

lemma coulomb_memLp (R : ℝ) :
    MemLp (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖⁻¹) (5 / 2)
      ((ballMeasure R).prod (ballMeasure R)) := by
  have hm : AEStronglyMeasurable (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖⁻¹)
      ((ballMeasure R).prod (ballMeasure R)) :=
    ((measurable_fst.sub measurable_snd).norm.inv).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, norm_inv, norm_norm,
    Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _), neg_div] using coulomb_power_integrable R

lemma nuclear_memLp (R : ℝ) : MemLp (fun x : TFSpace => ‖x‖⁻¹) (5 / 2) (ballMeasure R) := by
  have hm : AEStronglyMeasurable (fun x : TFSpace => ‖x‖⁻¹) (ballMeasure R) :=
    measurable_norm.inv.aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm
    (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, norm_inv, norm_norm,
    Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _), neg_div, ballMeasure, IntegrableOn] using
      norm_inv_power_integrable_ball R

end CoulombAnalysis

end

end OAI
