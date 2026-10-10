import Mathlib
import OAI.Analysis.MumfordShah.TestablePotential
import OAI.Analysis.MumfordShah.Cutoffs

namespace OAI

/-! MumfordShah variations. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

lemma integrable_mul_compact_of_continuousOn {f g : ℂ → ℝ} {O : Set ℂ}
    (hf : ContinuousOn f O) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ O) : Integrable (fun x => f x * g x) volume := by
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport g)
  · exact ((hf.mono hs).mul hg.continuousOn).integrableOn_compact hc
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

lemma sobolevOn_of_contDiffOn {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hL : MemLp u 2 (volume.restrict U))
    (hgL : MemLp (gradient u) 2 (volume.restrict U)) :
    SobolevOn u (gradient u) U := by
  refine ⟨hL, hgL, ?_⟩
  intro ψ hψ hc ht a
  have hd : ContinuousOn (fun x => fderiv ℝ u x a) U :=
    (hu.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  have hψd : Continuous (fun x => fderiv ℝ ψ x a) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := u) (g := ψ) (v := a)
    (integrable_mul_compact_of_continuousOn hd hψ.continuous hc ht)
    (integrable_mul_compact_of_continuousOn hu.continuousOn hψd
      (hc.fderiv_apply ℝ a) ((tsupport_fderiv_apply_subset ℝ a).trans ht))
    (integrable_mul_compact_of_continuousOn hu.continuousOn hψ.continuous hc ht)
    (fun x hx => ((hu x (ht hx)).contDiffAt (hU.mem_nhds (ht hx))).differentiableAt (by norm_num))
    (fun x _ => hψ.differentiable (by norm_num) x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ (fun hn => hx (ht hn))]; simp)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun hn => hx (ht hn))]; simp)]
  simpa only [inner_gradient_left] using hh

lemma volume_eq_zero_of_finite_length {H : Set ℂ}
    (hH : Measure.hausdorffMeasure 1 H < ⊤) : volume H = 0 := by
  have htwo : Measure.hausdorffMeasure 2 H = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1:ℝ) < 2) H).resolve_right hH.ne
  have himg := (Complex.equivRealProdCLM.toContinuousLinearMap.lipschitzWith).hausdorffMeasure_image_le
    (by norm_num : (0:ℝ) ≤ 2) H
  rw [htwo, mul_zero, nonpos_iff_eq_zero] at himg
  rw [hausdorffMeasure_prod_real] at himg
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (Complex.equivRealProdCLM '' H)
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Complex.equivRealProdCLM '' H) = H :=
    Set.preimage_image_eq H Complex.measurableEquivRealProd.injective
  rw [hpre] at he
  exact he.trans himg

lemma volume_eq_zero_of_locally_finite_length {H : Set ℂ}
    (hH : ∀ R : ℝ, 0 < R → Measure.hausdorffMeasure 1 (H ∩ ball 0 R) < ⊤) :
    volume H = 0 := by
  have hh : ∀ n : ℕ, volume (H ∩ ball (0:ℂ) (n+1:ℝ)) = 0 := by
    intro n
    exact volume_eq_zero_of_finite_length (hH _ (by positivity))
  have hcover : (⋃ n : ℕ, H ∩ ball (0:ℂ) (n+1:ℝ)) = H := by
    apply Subset.antisymm
    · exact iUnion_subset (fun _ => inter_subset_left)
    · intro x hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      exact mem_iUnion.mpr ⟨n, hx, by simpa using (by linarith : ‖x‖ < (n:ℝ)+1)⟩
  rw [← hcover]
  exact measure_iUnion_null hh

lemma SobolevOn.add {u v : ℂ → ℝ} {m n : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (hv : SobolevOn v n U) :
    SobolevOn (u+v) (m+n) U := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, ?_⟩
  intro ψ hψ hc ht a
  have hd : MemLp (fun x => fderiv ℝ ψ x a) 2 (volume.restrict U) :=
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ a)
  have htL : MemLp ψ 2 (volume.restrict U) := hψ.continuous.memLp_of_hasCompactSupport hc
  have him : Integrable (fun x => inner ℝ (m x) a * ψ x) (volume.restrict U) :=
    (hu.2.1.inner_const (𝕜 := ℝ) a).integrable_mul htL
  have hin : Integrable (fun x => inner ℝ (n x) a * ψ x) (volume.restrict U) :=
    (hv.2.1.inner_const (𝕜 := ℝ) a).integrable_mul htL
  have hiu : Integrable (fun x => u x * fderiv ℝ ψ x a) (volume.restrict U) := hu.1.integrable_mul hd
  have hiv : Integrable (fun x => v x * fderiv ℝ ψ x a) (volume.restrict U) := hv.1.integrable_mul hd
  simp only [Pi.add_apply, inner_add_left, add_mul]
  rw [integral_add hiu hiv, integral_add him hin,
    hu.2.2 ψ hψ hc ht a, hv.2.2 ψ hψ hc ht a]
  ring

lemma SobolevOn.const_smul {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (c : ℝ) : SobolevOn (c • u) (c • m) U := by
  refine ⟨hu.1.const_smul c, hu.2.1.const_smul c, ?_⟩
  intro ψ hψ hc ht a
  simp only [Pi.smul_apply, smul_eq_mul, real_inner_smul_left, mul_assoc]
  rw [integral_const_mul, integral_const_mul, hu.2.2 ψ hψ hc ht a]
  ring

lemma essentialSupport_subset_tsupport (u : ℂ → ℝ) : essentialSupport u ⊆ tsupport u := by
  intro x hx
  by_contra hn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((isClosed_tsupport u).isOpen_compl.mem_nhds hn)
  apply hx r hr
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  exact image_eq_zero_of_notMem_tsupport (hball hy)

lemma smooth_variation_admissible {p : Pair} (hp : GlobalAdmissible p)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (s : ℝ) :
    GlobalAdmissible ⟨fun x => p.u x + s * ψ x, p.K,
      fun x => p.grad x + s • gradient ψ x⟩ := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_⟩
  intro U hU hb
  have hS : SobolevOn ψ (gradient ψ) (U \ p.K) :=
    sobolevOn_of_contDiffOn (hU.sdiff hp.1) (hψ.of_le (by norm_num)).contDiffOn
      (hψ.continuous.memLp_of_hasCompactSupport hc)
      ((continuous_gradient_of_smooth hψ).memLp_of_hasCompactSupport (compactSupport_gradient hc))
  exact (hp.2.2.2 U hU hb).add (hS.const_smul s)

lemma smooth_variation_comparison {p : Pair} {ψ : ℂ → ℝ}
    (hc : HasCompactSupport ψ) {V : Set ℂ} (ht : tsupport ψ ⊆ V) (s : ℝ) :
    IsCompactComparison p ⟨fun x => p.u x + s * ψ x, p.K,
      fun x => p.grad x + s • gradient ψ x⟩ V := by
  have hsub : essentialSupport (fun x => p.u x + s * ψ x - p.u x) ⊆ tsupport ψ := by
    have he : (fun x => p.u x + s * ψ x - p.u x) = (fun x => s * ψ x) := by
      funext x; ring
    rw [he]
    exact (essentialSupport_subset_tsupport _).trans tsupport_mul_subset_right
  change IsCompact (closure (_ ∪ _)) ∧ closure (_ ∪ _) ⊆ V
  simp only [symmDiff_self, bot_eq_empty, empty_union]
  exact ⟨hc.closure_of_subset hsub, (closure_minimal hsub (isClosed_tsupport ψ)).trans ht⟩

lemma restrict_diff_null_set {H U : Set ℂ} (hH : volume H = 0) :
    volume.restrict (U \ H) = volume.restrict U := by
  apply Measure.restrict_congr_set
  have hn : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ H := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hH
  filter_upwards [hn] with x hx
  apply propext
  simp [hx]

lemma global_minimizer_smooth_energy {p : Pair} (hp : GlobalAbsoluteMinimizer p)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {R : ℝ} (hR : 0 < R) (ht : tsupport ψ ⊆ ball 0 R) (s : ℝ) :
    (∫ x in ball (0 : ℂ) R, ‖p.grad x‖^2) ≤
      ∫ x in ball (0 : ℂ) R, ‖p.grad x + s • gradient ψ x‖^2 := by
  have harea := volume_eq_zero_of_locally_finite_length hp.1.2.2.1
  have hμ := restrict_diff_null_set (U := ball (0 : ℂ) R) harea
  have hL : MemLp p.grad 2 (volume.restrict (ball (0 : ℂ) R)) := by
    rw [← hμ]
    exact (hp.1.2.2.2 _ isOpen_ball isBounded_ball).2.1
  have hgL : MemLp (gradient ψ) 2 (volume.restrict (ball (0 : ℂ) R)) :=
    (continuous_gradient_of_smooth hψ).memLp_of_hasCompactSupport (compactSupport_gradient hc)
  have hi : Integrable (fun x => ‖p.grad x‖^2) (volume.restrict (ball (0 : ℂ) R)) :=
    hL.integrable_norm_pow (by norm_num)
  have hj : Integrable (fun x => ‖p.grad x + s • gradient ψ x‖^2)
      (volume.restrict (ball (0 : ℂ) R)) :=
    (hL.add (hgL.const_smul s)).integrable_norm_pow (by norm_num)
  have hcomp := hp.2 (ball 0 R) isOpen_ball isBounded_ball
    ⟨fun x => p.u x + s * ψ x, p.K, fun x => p.grad x + s • gradient ψ x⟩
    (smooth_variation_admissible hp.1 hψ hc s) (smooth_variation_comparison hc ht s)
  change (_ + lengthMeasure (p.K ∩ ball 0 R)) ≤ (_ + lengthMeasure (p.K ∩ ball 0 R)) at hcomp
  have hlen := hp.1.2.2.1 R hR
  have he := (ENNReal.add_le_add_iff_right hlen.ne).mp hcomp
  change (∫⁻ x in ball (0 : ℂ) R \ p.K, ENNReal.ofReal (‖p.grad x‖^2)) ≤
    (∫⁻ x in ball (0 : ℂ) R \ p.K, ENNReal.ofReal (‖p.grad x + s • gradient ψ x‖^2)) at he
  rw [hμ, ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hj (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at he
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp he

lemma linear_coefficient_eq_zero {a b : ℝ}
    (h : ∀ σ : ℝ, 0 ≤ 2 * σ * a + σ ^ 2 * b) : a = 0 := by
  have hd : discrim b (2 * a) 0 ≤ 0 := discrim_le_zero (by
    intro σ
    nlinarith [h σ])
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg a]

theorem global_minimizer_divergence_free {p : Pair} (hp : GlobalAbsoluteMinimizer p)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => inner ℝ (p.grad x) (gradient ψ x)) volume ∧
      (∫ x : ℂ, inner ℝ (p.grad x) (gradient ψ x)) = 0 := by
  obtain ⟨R, hR, ht⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hμ := restrict_diff_null_set (U := ball (0 : ℂ) R)
    (volume_eq_zero_of_locally_finite_length hp.1.2.2.1)
  have hL : MemLp p.grad 2 (volume.restrict (ball (0 : ℂ) R)) := by
    rw [← hμ]
    exact (hp.1.2.2.2 _ isOpen_ball isBounded_ball).2.1
  have hgL : MemLp (gradient ψ) 2 (volume.restrict (ball (0 : ℂ) R)) :=
    (continuous_gradient_of_smooth hψ).memLp_of_hasCompactSupport (compactSupport_gradient hc)
  have hi := integrable_inner_memLp_measure hL hgL
  have hz (x : ℂ) (hx : x ∉ ball 0 R) : inner ℝ (p.grad x) (gradient ψ x) = 0 := by
    have hn : x ∉ tsupport ψ := fun hn => hx (ht hn)
    simp [gradient, fderiv_of_notMem_tsupport ℝ hn]
  refine ⟨IntegrableOn.integrable_of_forall_notMem_eq_zero hi hz, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply linear_coefficient_eq_zero (b := ∫ x in ball (0 : ℂ) R, ‖gradient ψ x‖^2)
  intro s
  have hm := global_minimizer_smooth_energy hp hψ hc hR ht s
  have hi0 := hL.integrable_norm_pow (p := 2) (by norm_num)
  have hi1 := hi.const_mul (2*s)
  have hi2 := (hgL.integrable_norm_pow (p := 2) (by norm_num)).const_mul (s^2)
  have heq (x : ℂ) : ‖p.grad x + s • gradient ψ x‖^2 =
      ‖p.grad x‖^2 + (2*s)*inner ℝ (p.grad x) (gradient ψ x) + s^2*‖gradient ψ x‖^2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp_rw [heq] at hm
  have hi01 : Integrable (fun x : ℂ => ‖p.grad x‖^2 + (2*s)*inner ℝ (p.grad x) (gradient ψ x))
      (volume.restrict (ball (0 : ℂ) R)) := hi0.add hi1
  rw [integral_add hi01 hi2, integral_add hi0 hi1,
    integral_const_mul, integral_const_mul] at hm
  linarith

open Filter
lemma sobolev_bounded_cutoff_of_product_tests {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hLu : MemLp u 2 (volume.restrict U)) (hLm : MemLp m 2 (volume.restrict U))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχL : MemLp χ ∞ (volume.restrict U))
    (hχgL : MemLp (gradient χ) ∞ (volume.restrict U))
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ a : ℂ, (∫ x in U, u x * fderiv ℝ (χ*ψ) x a) =
        -(∫ x in U, inner ℝ (m x) a * (χ*ψ) x)) :
    SobolevOn (fun x => χ x * u x)
      (fun x => χ x • m x + u x • gradient χ x) U := by
  refine ⟨hχL.fun_mul (r := 2) hLu, (hχL.smul hLm).add (hLu.smul hχgL), ?_⟩
  intro ψ hψ hψc ht a
  have hprod := hweak ψ hψ hψc ht a
  have hχdL : MemLp (fun x => fderiv ℝ χ x a) ∞ (volume.restrict U) := by
    simpa only [inner_gradient_left] using hχgL.inner_const (𝕜 := ℝ) a
  have hψL : MemLp ψ 2 (volume.restrict U) := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hψdL : MemLp (fun x => fderiv ℝ ψ x a) 2 (volume.restrict U) :=
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hψc.fderiv_apply ℝ a)
  have hi : Integrable (fun x => χ x * u x * fderiv ℝ ψ x a) (volume.restrict U) :=
    (hχL.fun_mul (r := 2) hLu).integrable_mul hψdL
  have hj : Integrable (fun x => u x * fderiv ℝ χ x a * ψ x) (volume.restrict U) := by
    have hL : MemLp (fun x => u x * fderiv ℝ χ x a) 2 (volume.restrict U) := by
      exact hLu.fun_mul hχdL
    exact hL.integrable_mul hψL
  have hk : Integrable (fun x => χ x * inner ℝ (m x) a * ψ x) (volume.restrict U) :=
    (hχL.fun_mul (r := 2) (hLm.inner_const (𝕜 := ℝ) a)).integrable_mul hψL
  have hd (x : ℂ) : u x * fderiv ℝ (χ * ψ) x a =
      χ x * u x * fderiv ℝ ψ x a + u x * fderiv ℝ χ x a * ψ x := by
    rw [fderiv_mul (hχ.differentiable (by norm_num) x) (hψ.differentiable (by norm_num) x)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  simp_rw [hd] at hprod
  rw [integral_add hi hj] at hprod
  have hright (x : ℂ) : inner ℝ (χ x • m x + u x • gradient χ x) a * ψ x =
      χ x * inner ℝ (m x) a * ψ x + u x * fderiv ℝ χ x a * ψ x := by
    simp only [inner_add_left, real_inner_smul_left, inner_gradient_left, add_mul]
  simp_rw [hright]
  rw [integral_add hk hj]
  have hh : (∫ x in U, inner ℝ (m x) a * (χ * ψ) x) =
      ∫ x in U, χ x * inner ℝ (m x) a * ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  rw [hh] at hprod
  linarith

lemma SobolevOn.congr_restrict {u v : ℂ → ℝ} {m n : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (hv : u =ᵐ[volume.restrict U] v)
    (hm : m =ᵐ[volume.restrict U] n) : SobolevOn v n U := by
  refine ⟨MemLp.ae_eq hv hu.1, MemLp.ae_eq hm hu.2.1, ?_⟩
  intro ψ hψ hc ht a
  have hl : (∫ x in U, v x * fderiv ℝ ψ x a) = ∫ x in U, u x * fderiv ℝ ψ x a := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hr : (∫ x in U, inner ℝ (n x) a * ψ x) = ∫ x in U, inner ℝ (m x) a * ψ x := by
    apply integral_congr_ae
    filter_upwards [hm] with x hx
    rw [hx]
  rw [hl, hr]
  exact hu.2.2 ψ hψ hc ht a

lemma SobolevOn.mul_smooth_bounded_extend {u : ℂ → ℝ} {m : ℂ → ℂ} {U V : Set ℂ}
    (hu : SobolevOn u m V) (hU : MeasurableSet U) (hV : MeasurableSet V)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχL : MemLp χ ∞ (volume.restrict U))
    (hχgL : MemLp (gradient χ) ∞ (volume.restrict U))
    (ht : tsupport χ ∩ U ⊆ V) :
    SobolevOn (fun x => χ x * u x)
      (fun x => χ x • m x + u x • gradient χ x) U := by
  classical
  let u0 := V.indicator u
  let m0 := V.indicator m
  have hu0 : MemLp u0 2 volume := (memLp_indicator_iff_restrict hV).mpr hu.1
  have hm0 : MemLp m0 2 volume := (memLp_indicator_iff_restrict hV).mpr hu.2.1
  have hs := sobolev_bounded_cutoff_of_product_tests (hu0.restrict U) (hm0.restrict U) hχ hχL hχgL ?_
  · apply hs.congr_restrict
    · filter_upwards [ae_restrict_mem hU] with x hx
      by_cases hxV : x ∈ V
      · simp [u0, hxV]
      · have hxχ : x ∉ tsupport χ := fun hh => hxV (ht ⟨hh,hx⟩)
        simp [image_eq_zero_of_notMem_tsupport hxχ]
    · filter_upwards [ae_restrict_mem hU] with x hx
      by_cases hxV : x ∈ V
      · simp [u0,m0,hxV]
      · have hxχ : x ∉ tsupport χ := fun hh => hxV (ht ⟨hh,hx⟩)
        have hgχ : gradient χ x = 0 := by simp [gradient, fderiv_of_notMem_tsupport ℝ hxχ]
        simp [image_eq_zero_of_notMem_tsupport hxχ,hgχ]
  intro ψ hψ hψc hψt a
  have htt : tsupport (χ*ψ) ⊆ U := tsupport_mul_subset_right.trans hψt
  have htV : tsupport (χ*ψ) ⊆ V := by
    intro x hx
    exact ht ⟨tsupport_mul_subset_left hx, htt hx⟩
  have hlU : (∫ x in U, u0 x * fderiv ℝ (χ*ψ) x a) =
      ∫ x, u0 x * fderiv ℝ (χ*ψ) x a :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ (fun hn => hx (htt hn))]; simp)
  have hrU : (∫ x in U, inner ℝ (m0 x) a * (χ*ψ) x) =
      ∫ x, inner ℝ (m0 x) a * (χ*ψ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hn => hx (htt hn))]; simp)
  have hlV : (fun x => u0 x * fderiv ℝ (χ*ψ) x a) =
      V.indicator (fun x => u x * fderiv ℝ (χ*ψ) x a) := by
    funext x
    by_cases hx : x ∈ V <;> simp [u0,hx]
  have hrV : (fun x => inner ℝ (m0 x) a * (χ*ψ) x) =
      V.indicator (fun x => inner ℝ (m x) a * (χ*ψ) x) := by
    funext x
    by_cases hx : x ∈ V <;> simp [m0,hx]
  rw [hlU,hrU,hlV,hrV,integral_indicator hV, integral_indicator hV]
  exact hu.2.2 (χ*ψ) (hχ.mul hψ) (hψc.mul_left) htV a

lemma cutoff_sobolev_decomposition {p : Pair} (hp : GlobalAdmissible p)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hH : p.K = A ∪ B)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ht : tsupport χ ⊆ Bᶜ) (hχ1 : ∀ x ∈ A, χ =ᶠ[𝓝 x] 1) :
    SobolevOn (fun x => χ x * p.u x)
      (fun x => χ x • p.grad x + p.u x • gradient χ x) Aᶜ ∧
    IsCompact (essentialSupport (fun x => χ x * p.u x)) ∧
    (∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
      SobolevOn (fun x => (1-χ x)*p.u x)
        (fun x => (1-χ x) • p.grad x - p.u x • gradient χ x) (S \ B)) := by
  have hκ : ContDiff ℝ ∞ (fun x => 1-χ x) := contDiff_const.sub hχ
  have hκg (x : ℂ) : gradient (fun y => 1 - χ y) x = -gradient χ x := by
    simp only [gradient, fderiv_const_sub (1:ℝ), map_neg]
  have hκge : gradient (fun y => 1 - χ y) = -gradient χ := funext hκg
  have hκL (U : Set ℂ) : MemLp (fun x => 1-χ x) ∞ (volume.restrict U) :=
    (memLp_top_const (1 : ℝ)).sub (hχ.continuous.memLp_of_hasCompactSupport hc)
  have hκgL (U : Set ℂ) : MemLp (gradient (fun x => 1-χ x)) ∞ (volume.restrict U) := by
    rw [hκge]
    exact
      ((continuous_gradient_of_smooth hχ).memLp_of_hasCompactSupport (compactSupport_gradient hc)
        (μ := volume.restrict U) (p := ∞)).neg
  have hκA : Disjoint A (tsupport (fun x => 1-χ x)) := by
    rw [disjoint_left]
    intro x hx hxt
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hxt
    filter_upwards [hχ1 x hx] with y hy
    simp only [Pi.one_apply] at hy
    simp [hy]
  obtain ⟨R, hR⟩ := hc.isBounded.subset_ball (0 : ℂ)
  have hh := (hp.2.2.2 (ball 0 R) isOpen_ball isBounded_ball).mul_smooth_bounded_extend
    (U := Aᶜ) hA.isClosed.measurableSet.compl
    ((isOpen_ball.sdiff hp.1).measurableSet) hχ
    (hχ.continuous.memLp_of_hasCompactSupport hc)
    ((continuous_gradient_of_smooth hχ).memLp_of_hasCompactSupport (compactSupport_gradient hc))
    (by
      intro x hx
      refine ⟨hR hx.1, ?_⟩
      rw [hH]
      rintro (hxA | hxB)
      · exact hx.2 hxA
      · exact ht hx.1 hxB)
  refine ⟨hh, ?_, ?_⟩
  · have hs : essentialSupport (fun x => χ x * p.u x) ⊆ tsupport χ :=
      (essentialSupport_subset_tsupport _).trans tsupport_mul_subset_left
    
    have hclosed : IsClosed (essentialSupport (fun x => χ x * p.u x)) := by
      apply isOpen_compl_iff.mp
      rw [Metric.isOpen_iff]
      intro x hx
      change ¬ (∀ r : ℝ, 0 < r → ¬ (∀ᵐ y ∂volume.restrict (ball x r), χ y * p.u y = 0)) at hx
      push Not at hx
      obtain ⟨r,hr,hz⟩ := hx
      refine ⟨r,hr,?_⟩
      intro y hy
      change ¬ (∀ s : ℝ, 0 < s → ¬ (∀ᵐ z ∂volume.restrict (ball y s), χ z * p.u z = 0))
      intro h
      apply h (r - dist y x) (sub_pos.mpr hy)
      exact ae_restrict_of_ae_restrict_of_subset (ball_subset_ball' (by linarith)) hz
    exact hc.of_isClosed_subset hclosed hs
  · intro S hS hb
    have hv := (hp.2.2.2 S hS hb).mul_smooth_bounded_extend
      (U := S \ B) (hS.sdiff hB).measurableSet (hS.sdiff hp.1).measurableSet
      hκ (hκL _) (hκgL _) (by
        intro x hx
        refine ⟨hx.2.1, ?_⟩
        rw [hH]
        rintro (hxA | hxB)
        · exact Set.disjoint_left.mp hκA hxA hx.1
        · exact hx.2.2 hxB)
    rw [hκge] at hv
    simpa only [Pi.neg_apply, smul_neg, sub_eq_add_neg] using hv

end MumfordShah
end

end OAI
