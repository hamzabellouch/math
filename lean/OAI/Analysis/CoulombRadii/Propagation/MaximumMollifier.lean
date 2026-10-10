import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior
import OAI.Analysis.CoulombRadii.Propagation.SmoothMaximum

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators Topology ContDiff Convolution
namespace NeutralAtom

def maximumBump (n : ℕ) : ContDiffBump (0:Position) :=
  ⟨(1/((n:ℝ)+1))/2, 1/((n:ℝ)+1), by positivity, by
    have H : 0<1/((n:ℝ)+1) := by positivity
    linarith⟩

def maximumMollify (n : ℕ) (f : Position → ℝ) : Position → ℝ :=
  f ⋆[lsmul ℝ ℝ,volume] (maximumBump n).normed volume

lemma maximumBump_rOut_le_one (n : ℕ) : (maximumBump n).rOut≤1 := by
  dsimp [maximumBump]
  exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)

lemma maximumBump_rOut_tendsto : Tendsto (fun n => (maximumBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma maximumMollify_contDiff {f : Position → ℝ} (hf : LocallyIntegrable f volume) (n : ℕ) :
    ContDiff ℝ ∞ (maximumMollify n f) :=
  (maximumBump n).hasCompactSupport_normed.contDiff_convolution_right (lsmul ℝ ℝ) hf
    (maximumBump n).contDiff_normed

lemma maximumMollify_tendsto {f : Position → ℝ} (hf : Continuous f) (x : Position) :
    Tendsto (fun n => maximumMollify n f x) atTop (𝓝 (f x)) := by
  have H := ContDiffBump.convolution_tendsto_right_of_continuous (μ:=volume)
    maximumBump_rOut_tendsto hf x
  simpa only [continuous_convolution_comm,maximumMollify] using H

lemma maximumMollify_ae_tendsto {f : Position → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, Tendsto (fun n => maximumMollify n f x) atTop (𝓝 (f x)) := by
  have H := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ:=volume)
    maximumBump_rOut_tendsto (K:=2) (Eventually.of_forall (fun n => by dsimp [maximumBump]; linarith)) hf
  simpa only [continuous_convolution_comm,maximumMollify] using H

lemma weakLaplacianGE_maximumMollify {f q : Position → ℝ}
    (hf : LocallyIntegrable f volume) (hw : WeakLaplacianGE f univ q) (n : ℕ) (x : Position) :
    maximumMollify n q x≤coordinateLaplacian (maximumMollify n f) x := by
  let φ := maximumBump n
  have ht := normed_bump_reflect_tsupport φ x
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    (isCompact_closedBall x φ.rOut).of_isClosed_subset (isClosed_tsupport _) ht
  have hs : ContDiff ℝ ∞ (fun y => φ.normed volume (x-y)) :=
    φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have H := hw _ hs hc (subset_univ _) (fun y => φ.nonneg_normed _)
  unfold maximumMollify
  rw [coordinateLaplacian_convolution hf (maximumBump n).contDiff_normed (maximumBump n).hasCompactSupport_normed]
  simpa only [coordinateLaplacian_reflect,convolution_def,lsmul_apply,smul_eq_mul] using H

lemma maximumMollify_abs_le {f : Position → ℝ} (hf : LocallyIntegrable f volume)
    {A : ℝ} {U : Set Position} (hA : ∀ y∈U, |f y|≤A) (n : ℕ) {x : Position}
    (hx : Metric.closedBall x (maximumBump n).rOut⊆U) : |maximumMollify n f x|≤A := by
  let φ := maximumBump n
  have hi := (φ.hasCompactSupport_normed (μ:=volume)).convolutionExists_right (lsmul ℝ ℝ) hf φ.continuous_normed x
  change Integrable (fun y => f y*φ.normed volume (x-y)) volume at hi
  change |∫ y, f y*φ.normed volume (x-y)|≤A
  calc
    _ ≤ ∫ y, |f y*φ.normed volume (x-y)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => f y*φ.normed volume (x-y))
    _ ≤ ∫ y, A*φ.normed volume (x-y) := by
      have hin : Integrable (fun y => |f y*φ.normed volume (x-y)|) volume := hi.norm
      apply integral_mono hin ((integrable_normed_bump_reflect φ x).const_mul A)
      intro y
      change |f y*φ.normed volume (x-y)|≤A*φ.normed volume (x-y)
      rw [abs_mul,abs_of_nonneg (φ.nonneg_normed _)]
      by_cases hy : φ.normed volume (x-y)=0
      · simp [hy]
      · apply mul_le_mul_of_nonneg_right _ (φ.nonneg_normed _)
        exact hA y (hx (normed_bump_reflect_tsupport φ x (subset_closure hy)))
    _ = A := by rw [integral_const_mul,integral_sub_left_eq_self,φ.integral_normed,mul_one]

lemma maximumMollify_abs_le_ball {f : Position → ℝ} (hf : LocallyIntegrable f volume)
    {A R : ℝ} (hA : ∀ y∈Metric.closedBall (0:Position) (R+1), |f y|≤A)
    (n : ℕ) {x : Position} (hx : x∈Metric.closedBall 0 R) : |maximumMollify n f x|≤A := by
  apply maximumMollify_abs_le hf hA n
  intro y hy
  simp only [Metric.mem_closedBall] at *
  have h := dist_triangle y x 0
  exact h.trans (add_le_add (hy.trans (maximumBump_rOut_le_one n)) hx |>.trans_eq (add_comm 1 R))

end NeutralAtom

end
open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators Topology ContDiff Convolution
namespace NeutralAtom

lemma continuous_softWeight {e : ℝ} (he : 0 < e) : Continuous (softWeight e) :=
  (continuous_const.add (continuous_id.div (contDiff_softAbs he).continuous
    (fun x => ne_of_gt (softAbs_pos he x)))).div_const 2

lemma convex_pair_abs_le {p u v A B : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hu : |u| ≤ A) (hv : |v| ≤ B) : |p*u+(1-p)*v| ≤ A+B := by
  calc
    _ ≤ |p*u|+|(1-p)*v| := abs_add_le _ _
    _ ≤ |u|+|v| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg (sub_nonneg.mpr hp1)]
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_right hp1 (abs_nonneg u)
      · simpa using mul_le_mul_of_nonneg_right (show 1-p ≤ 1 by linarith) (abs_nonneg v)
    _ ≤ A+B := add_le_add hu hv

lemma tendsto_integral_compact_mul {F : ℕ → Position → ℝ} {f φ : Position → ℝ}
    (hF : ∀ n, Continuous (F n)) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {C : ℝ} (hb : ∀ n x, x ∈ tsupport φ → |F n x| ≤ C)
    (ht : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x*φ x) atTop (𝓝 (∫ x, f x*φ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C*‖φ x‖)
    (fun n => ((hF n).mul hφ).aestronglyMeasurable)
    ((hφ.integrable_of_hasCompactSupport hc).norm.const_mul C)
  · intro n
    filter_upwards [] with x
    change ‖F n x*φ x‖ ≤ C*‖φ x‖
    rw [norm_mul,Real.norm_eq_abs (F n x)]
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hb n x hx) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · filter_upwards [ht] with x hx
    exact hx.mul_const _

lemma weakLaplacianGE_maximumMollify_local {f q : Position → ℝ} {U : Set Position}
    (hf : LocallyIntegrable f volume) (hw : WeakLaplacianGE f U q) (n : ℕ) (x : Position)
    (hx : Metric.closedBall x (maximumBump n).rOut ⊆ U) :
    maximumMollify n q x ≤ coordinateLaplacian (maximumMollify n f) x := by
  let φ := maximumBump n
  have ht := normed_bump_reflect_tsupport φ x
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    (isCompact_closedBall x φ.rOut).of_isClosed_subset (isClosed_tsupport _) ht
  have hs : ContDiff ℝ ∞ (fun y => φ.normed volume (x-y)) :=
    φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have H := hw _ hs hc (ht.trans hx) (fun y => φ.nonneg_normed _)
  unfold maximumMollify
  rw [coordinateLaplacian_convolution hf (maximumBump n).contDiff_normed (maximumBump n).hasCompactSupport_normed]
  simpa only [coordinateLaplacian_reflect,convolution_def,lsmul_apply,smul_eq_mul] using H

theorem WeakLaplacianGE.max_tied {f g q r : Position → ℝ} {U : Set Position}
    (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable q volume) (hr : LocallyIntegrable r volume)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |q x| ≤ C)
    (hbr : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |r x| ≤ C)
    (hwf : WeakLaplacianGE f U q) (hwg : WeakLaplacianGE g U r)
    (htie : ∀ x, f x=g x → q x=r x) :
    WeakLaplacianGE (fun x => max (f x) (g x)) U (fun x => if g x ≤ f x then q x else r x) := by
  intro φ hφ hc ht hp
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:Position)
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:Position) (R+1)).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:Position) (R+1)).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨Q,hQ⟩ := hbq (R+1)
  obtain ⟨S,hS⟩ := hbr (R+1)
  let e : ℕ → ℝ := fun n => (maximumBump n).rOut
  have he : ∀ n, 0 < e n := fun n => (maximumBump n).rOut_pos
  have hF (n : ℕ) := maximumMollify_contDiff hf.locallyIntegrable n
  have hG (n : ℕ) := maximumMollify_contDiff hg.locallyIntegrable n
  have hQn (n : ℕ) := maximumMollify_contDiff hq n
  have hSn (n : ℕ) := maximumMollify_contDiff hr n
  let p : ℕ → Position → ℝ := fun n x => softWeight (e n) (maximumMollify n f x-maximumMollify n g x)
  let v : ℕ → Position → ℝ := fun n x => softMax (e n) (maximumMollify n f x) (maximumMollify n g x)
  let a : ℕ → Position → ℝ := fun n x => p n x*maximumMollify n q x+(1-p n x)*maximumMollify n r x
  have hpc (n : ℕ) : Continuous (p n) := (continuous_softWeight (he n)).comp ((hF n).continuous.sub (hG n).continuous)
  have hvc (n : ℕ) : ContDiff ℝ ∞ (v n) := contDiff_softMax (he n) (hF n) (hG n)
  have hac (n : ℕ) : Continuous (a n) := ((hpc n).mul (hQn n).continuous).add ((continuous_const.sub (hpc n)).mul (hSn n).continuous)
  have hbv (n : ℕ) (x : Position) (hx : x ∈ tsupport φ) : |v n x| ≤ A+B+1 := by
    have H := softMax_abs_le (he n).le
      (maximumMollify_abs_le_ball hf.locallyIntegrable hA n (hR hx))
      (maximumMollify_abs_le_ball hg.locallyIntegrable hB n (hR hx))
    have hle : e n ≤ 1 := maximumBump_rOut_le_one n
    linarith
  have hba (n : ℕ) (x : Position) (hx : x ∈ tsupport φ) : |a n x| ≤ Q+S := by
    exact convex_pair_abs_le (softWeight_bounds (he n) _).1 (softWeight_bounds (he n) _).2
      (maximumMollify_abs_le_ball hq hQ n (hR hx))
      (maximumMollify_abs_le_ball hr hS n (hR hx))
  have hva (x : Position) : Tendsto (fun n => v n x) atTop (𝓝 (max (f x) (g x))) :=
    softMax_tendsto maximumBump_rOut_tendsto (maximumMollify_tendsto hf x) (maximumMollify_tendsto hg x)
  have haa : ∀ᵐ x, Tendsto (fun n => a n x) atTop (𝓝 (if g x ≤ f x then q x else r x)) := by
    filter_upwards [maximumMollify_ae_tendsto hq,maximumMollify_ae_tendsto hr] with x hx hy
    exact softWeight_response_tendsto maximumBump_rOut_tendsto he (maximumMollify_tendsto hf x)
      (maximumMollify_tendsto hg x) hx hy (htie x)
  have hla := tendsto_integral_compact_mul hac hφ.continuous hc hba haa
  have hlv := tendsto_integral_compact_mul (fun n => (hvc n).continuous)
    (contDiff_coordinateLaplacian hφ).continuous (hasCompactSupport_coordinateLaplacian hc)
    (fun n x hx => hbv n x (tsupport_coordinateLaplacian_subset φ hx)) (Eventually.of_forall hva)
  apply le_of_tendsto_of_tendsto hla hlv
  obtain ⟨δ,hδ,hδU⟩ := hc.exists_cthickening_subset_open hU ht
  have hn : ∀ᶠ n in atTop, e n < δ := maximumBump_rOut_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with n hn
  have hlocal (x : Position) (hx : x ∈ tsupport φ) : Metric.closedBall x (maximumBump n).rOut ⊆ U :=
    (Metric.closedBall_subset_closedBall hn.le).trans ((Metric.closedBall_subset_cthickening hx δ).trans hδU)
  have hpoint (x : Position) (hx : x ∈ tsupport φ) : a n x ≤ coordinateLaplacian (v n) x := by
    apply le_trans _ (coordinateLaplacian_softMax_lower (he n) (hF n) (hG n) x)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (weakLaplacianGE_maximumMollify_local hf.locallyIntegrable hwf n x (hlocal x hx))
        (softWeight_bounds (he n) _).1
    · exact mul_le_mul_of_nonneg_left (weakLaplacianGE_maximumMollify_local hg.locallyIntegrable hwg n x (hlocal x hx))
        (sub_nonneg.mpr (softWeight_bounds (he n) _).2)
  rw [integral_mul_coordinateLaplacian_eq (fun x _ => (hvc n).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hφ hc]
  apply integral_mono
    (integrable_mul_compact_of_continuousAt (fun x _ => (hac n).continuousAt) hφ.continuous hc)
    (integrable_mul_compact_of_continuousAt (fun x _ => (contDiff_coordinateLaplacian (hvc n)).continuous.continuousAt) hφ.continuous hc)
  intro x
  change a n x*φ x ≤ coordinateLaplacian (v n) x*φ x
  by_cases hx : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hpoint x hx) (hp x)
  · simp [image_eq_zero_of_notMem_tsupport hx]

end NeutralAtom

end

end OAI
