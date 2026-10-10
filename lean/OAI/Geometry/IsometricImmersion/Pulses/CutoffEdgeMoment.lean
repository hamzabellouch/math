import OAI.Geometry.IsometricImmersion.Pulses.FiniteOscillatoryMoment
import OAI.Geometry.IsometricImmersion.Pulses.PulseDerivativeBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse

def cutoffEdgeWeight (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := axisBump a x*f x

theorem cutoffEdgeWeight_contDiff {a : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) :
    ContDiff ℝ ∞ (cutoffEdgeWeight a f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ I
  · exact (axisBump_contDiff a).contDiffAt.mul (hf.contDiffAt (hI.mem_nhds hx))
  · have hnot : x ∉ tsupport (axisBump a) := fun ht => hx (hsub (axisBump_tsupport_subset ha ht))
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hnot
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    change axisBump a y*f y = 0
    change axisBump a y = (0 : ℝ) at hy
    rw [hy,zero_mul]

theorem cutoffEdgeWeight_hasCompactSupport {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    HasCompactSupport (cutoffEdgeWeight a f) := (axisBump_hasCompactSupport ha).mul_right

theorem iteratedDeriv_tsupport_subset (N : ℕ) (f : ℝ → ℝ) :
    tsupport (iteratedDeriv N f) ⊆ tsupport f := by
  induction N with
  | zero => simp only [iteratedDeriv_zero,subset_refl]
  | succ N ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem cutoffEdgeWeight_iteratedDeriv_zero_off {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ)
    (N : ℕ) {x : ℝ} (hx : x ∉ Icc (-a) a) :
    iteratedDeriv N (cutoffEdgeWeight a f) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hx (axisBump_tsupport_subset ha (tsupport_mul_subset_left
    (iteratedDeriv_tsupport_subset N (cutoffEdgeWeight a f) hmem)))

def cutoffEdgeDerivativeBound (a : ℝ) (ha : 0 < a) (N : ℕ) (B : ℝ) : ℝ :=
  derivativeConvolution (axisBumpDerivativeBound a ha) (fun _ => B) N

theorem cutoffEdgeDerivativeBound_nonneg {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (N : ℕ) :
    0 ≤ cutoffEdgeDerivativeBound a ha N B :=
  derivativeConvolution_nonneg (fun k => (axisBumpDerivativeBound_pos ha k).le) (fun _ => hB) N

theorem cutoffEdgeWeight_iteratedDeriv_bound {a B : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I)
    (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (-a) a) :
    |iteratedDeriv N (cutoffEdgeWeight a f) x| ≤ cutoffEdgeDerivativeBound a ha N B := by
  have hχ : ContDiffAt ℝ N (axisBump a) x := (axisBump_contDiff a).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfx : ContDiffAt ℝ N f x := (hf.contDiffAt (hI.mem_nhds (hsub hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have hprod := iteratedDeriv_mul hχ hfx
  change iteratedDeriv N (cutoffEdgeWeight a f) x = _ at hprod
  rw [←Real.norm_eq_abs,hprod]
  refine (norm_sum_le _ _).trans ?_
  unfold cutoffEdgeDerivativeBound derivativeConvolution
  apply Finset.sum_le_sum
  intro index _
  have hχb : ‖iteratedDeriv index (axisBump a) x‖ ≤ axisBumpDerivativeBound a ha index := by
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact axisBump_derivative_le ha index x
  have hfb : ‖iteratedDeriv (N-index) f x‖ ≤ B := by
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hjet (N-index) (Nat.sub_le _ _) x hx
  simp only [norm_mul,Real.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hfb
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hχb (Nat.cast_nonneg _)) hB)

theorem cutoffEdgeWeight_iteratedDeriv_L1 {a B : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I)
    (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    (∫ x : ℝ, |iteratedDeriv N (cutoffEdgeWeight a f) x|) ≤
      (2*a)*cutoffEdgeDerivativeBound a ha N B := by
  have hglobal := cutoffEdgeWeight_contDiff ha hI hf hsub
  have hcont : Continuous (fun x => |iteratedDeriv N (cutoffEdgeWeight a f) x|) :=
    (hglobal.continuous_iteratedDeriv N (WithTop.coe_le_coe.mpr le_top)).abs
  have hrestrict : (∫ x in Icc (-a) a, |iteratedDeriv N (cutoffEdgeWeight a f) x|) =
      ∫ x : ℝ, |iteratedDeriv N (cutoffEdgeWeight a f) x| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [cutoffEdgeWeight_iteratedDeriv_zero_off ha f N hx,abs_zero]
  rw [←hrestrict]
  have hm := integral_mono_ae (μ := volume.restrict (Icc (-a) a)) hcont.continuousOn.integrableOn_Icc
    ((continuous_const : Continuous (fun _ : ℝ => cutoffEdgeDerivativeBound a ha N B)).continuousOn.integrableOn_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact cutoffEdgeWeight_iteratedDeriv_bound ha hB hI hf hsub N hjet hx)
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -a ≤ a),smul_eq_mul] at hm
  simpa only [sub_neg_eq_add,two_mul] using hm

theorem cutoffEdgeWeight_cos_integral_bound {a B tau : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (htau : 0 < tau)
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    |∫ x : ℝ, axisBump a x*f x*Real.cos (tau*x)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N :=
  finite_oscillatory_weight_bound N (cutoffEdgeWeight_contDiff ha hI hf hsub)
    (cutoffEdgeWeight_hasCompactSupport ha f) htau
    (cutoffEdgeWeight_iteratedDeriv_L1 ha hB hI hf hsub N hjet)

end SmoothLocal.Pulse

end

end OAI
