import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombTestCharge
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierSmoothMaxBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

def WeakLaplacianLowerOn (U : Set TFSpace) (u h : TFSpace → ℝ) : Prop :=
  ∀ φ : TFSpace → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
    tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) →
    (∫ x, h x*φ x) ≤ ∫ x, u x*Δ φ x

lemma newtonMul_flip_eq : newtonMul.flip = newtonMul := by
  exact ContinuousLinearMap.flip_mul

lemma laplacian_sub_left {k : TFSpace → ℝ} (hk : ContDiff ℝ 2 k)
    (x y : TFSpace) : Δ (fun z => k (x-z)) y = Δ k (x-y) := by
  have hd : ContDiff ℝ 2 (fun z : TFSpace => k (x+z)) :=
    hk.comp (contDiff_const.add contDiff_id)
  have hh := laplacian_comp_isometry (LinearIsometryEquiv.neg ℝ) y hd.contDiffAt
  simpa only [LinearIsometryEquiv.coe_neg,sub_eq_add_neg,tfLaplacian_translate] using hh

lemma tsupport_sub_left {k : TFSpace → ℝ} {r : ℝ}
    (hk : ∀ z, k z ≠ 0 → ‖z‖ ≤ r) (x : TFSpace) :
    tsupport (fun y => k (x-y)) ⊆ closedBall x r := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  rw [mem_closedBall,dist_eq_norm_sub']
  exact hk (x-y) hy

lemma weak_lower_convolution {U : Set TFSpace} {u h k : TFSpace → ℝ}
    (hu : Continuous u) (hw : WeakLaplacianLowerOn U u h)
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hk0 : ∀ y, 0 ≤ k y)
    {x : TFSpace} (hs : tsupport (fun y => k (x-y)) ⊆ U) :
    (k ⋆[newtonMul] h) x ≤ Δ (k ⋆[newtonMul] u) x := by
  have hd : ContDiff ℝ 2 (fun y => k (x-y)) := hk.comp (contDiff_const.sub contDiff_id)
  have hc : HasCompactSupport (fun y => k (x-y)) := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hi := hw _ hd hc hs (fun y => hk0 (x-y))
  have he : k ⋆[newtonMul] u = u ⋆[newtonMul] k := by
    simpa only [newtonMul_flip_eq] using (convolution_flip newtonMul (f := u) (g := k))
  rw [he,laplacian_convolution hu.locallyIntegrable hkc hk]
  simp_rw [laplacian_sub_left hk] at hi
  rw [convolution_eq_swap]
  simpa only [newtonMul,ContinuousLinearMap.mul_apply',mul_comm] using hi

def maxKernel (n : ℕ) : TFSpace → ℝ := (shrinkingBump n).normed volume

def maxMollify (n : ℕ) (u : TFSpace → ℝ) : TFSpace → ℝ :=
  maxKernel n ⋆[newtonMul] u

lemma maxKernel_radius (n : ℕ) : (shrinkingBump (E := TFSpace) n).rOut ≤ 2 := by
  dsimp [shrinkingBump]
  have hn : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have ht := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn
  norm_num only [one_div_one] at ht
  linarith

lemma maxKernel_support (n : ℕ) {z : TFSpace} (hz : maxKernel n z ≠ 0) :
    ‖z‖ ≤ (shrinkingBump (E := TFSpace) n).rOut := by
  have ht : z ∈ Function.support ((shrinkingBump (E := TFSpace) n).normed volume) := hz
  rw [ContDiffBump.support_normed_eq] at ht
  exact (by simpa only [mem_ball,dist_zero_right] using ht : ‖z‖ < _).le

lemma maxMollify_contDiff {u : TFSpace → ℝ} (hu : LocallyIntegrable u) (n : ℕ) :
    ContDiff ℝ 2 (maxMollify n u) :=
  (shrinkingBump n).hasCompactSupport_normed.contDiff_convolution_left newtonMul
    (shrinkingBump n).contDiff_normed hu

lemma maxMollify_tendsto {u : TFSpace → ℝ} (hu : Continuous u) (x : TFSpace) :
    Tendsto (fun n => maxMollify n u x) atTop (𝓝 (u x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto hu x

lemma maxMollify_ae_tendsto {u : TFSpace → ℝ} (hu : LocallyIntegrable u) :
    ∀ᵐ x, Tendsto (fun n => maxMollify n u x) atTop (𝓝 (u x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    shrinkingBump_tendsto (K := 2) _ hu
  exact Eventually.of_forall fun n => le_rfl

lemma maxMollify_bound {u : TFSpace → ℝ} {R C : ℝ}
    (hC : ∀ y, ‖y‖ ≤ R+2 → ‖u y‖ ≤ C) (n : ℕ) {x : TFSpace} (hx : ‖x‖ ≤ R) :
    ‖maxMollify n u x‖ ≤ C := by
  have hi : Integrable (maxKernel n) :=
    (shrinkingBump n).continuous_normed.integrable_of_hasCompactSupport
      (shrinkingBump n).hasCompactSupport_normed
  change ‖∫ z, maxKernel n z*u (x-z)‖ ≤ C
  calc
    _ ≤ ∫ z, C*maxKernel n z := norm_integral_le_of_norm_le (hi.const_mul C)
      (Eventually.of_forall fun z => by
        by_cases hz : maxKernel n z = 0
        · simp only [hz,zero_mul,mul_zero,norm_zero,le_refl]
        · rw [norm_mul,Real.norm_of_nonneg (show 0 ≤ maxKernel n z from (shrinkingBump n).nonneg_normed z)]
          have hb : ‖u (x-z)‖ ≤ C := hC (x-z)
            ((norm_sub_le x z).trans (add_le_add hx ((maxKernel_support n hz).trans (maxKernel_radius n))))
          nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ maxKernel n z from (shrinkingBump n).nonneg_normed z)])
    _ = C := by rw [integral_const_mul]; change C*(∫ z, (shrinkingBump n).normed volume z) = C; rw [ContDiffBump.integral_normed,mul_one]

lemma continuous_ball_bound {u : TFSpace → ℝ} (hu : Continuous u) (R : ℝ) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ R → ‖u x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := ((isCompact_closedBall (0 : TFSpace) R).image hu).isBounded.exists_pos_norm_lt
  exact ⟨C,hC,fun x hx => (hb _ ⟨x,by simpa using hx,rfl⟩).le⟩

theorem weak_maximum_common_source {U : Set TFSpace} (hU : IsOpen U)
    {u v h : TFSpace → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hh : LocallyIntegrable h) {C : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C)
    (hwu : WeakLaplacianLowerOn U u h) (hwv : WeakLaplacianLowerOn U v h) :
    WeakLaplacianLowerOn U (fun x => max (u x) (v x)) h := by
  intro φ hφ hcφ hsφ hnφ
  obtain ⟨δ,hδ,hsδ⟩ := hcφ.isCompact.exists_cthickening_subset_open hU hsφ
  obtain ⟨R,hR,hbR⟩ := hcφ.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨Cu,hCu,hbu⟩ := continuous_ball_bound hu (R+2)
  obtain ⟨Cv,hCv,hbv⟩ := continuous_ball_bound hv (R+2)
  let D := max Cu Cv
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → TFSpace → ℝ := fun n => smoothMaximum (ε n) (maxMollify n u) (maxMollify n v)
  have hwd (n : ℕ) : ContDiff ℝ 2 (w n) := smoothMaximum_contDiff (hε n)
    (maxMollify_contDiff hu.locallyIntegrable n) (maxMollify_contDiff hv.locallyIntegrable n)
  have hwb (n : ℕ) {x : TFSpace} (hx : x ∈ tsupport φ) : ‖w n x‖ ≤ D+1 := by
    have hux : ‖maxMollify n u x‖ ≤ D :=
      (maxMollify_bound hbu n (hbR x hx).le).trans (le_max_left _ _)
    have hvx : ‖maxMollify n v x‖ ≤ D :=
      (maxMollify_bound hbv n (hbR x hx).le).trans (le_max_right _ _)
    have hw := smoothMaximum_norm_bound (hε n).le x hux hvx
    change ‖w n x‖ ≤ D+ε n/2 at hw
    linarith [hεle n]
  have hwlim (x : TFSpace) : Tendsto (fun n => w n x) atTop (𝓝 (max (u x) (v x))) :=
    smoothMaximum_tendsto x (Eventually.of_forall fun n => (hε n).le) hε0
      (maxMollify_tendsto hu x) (maxMollify_tendsto hv x)
  have hΔφ := tfLaplacian_continuous hφ
  have hcΔφ := tfLaplacian_compact hφ hcφ
  have htR : Tendsto (fun n => ∫ x, w n x*Δ φ x) atTop
      (𝓝 (∫ x, max (u x) (v x)*Δ φ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (D+1)*‖Δ φ x‖)
    · intro n
      exact ((hwd n).continuous.mul hΔφ).aestronglyMeasurable
    · exact (hΔφ.norm.integrable_of_hasCompactSupport hcΔφ.norm).const_mul _
    · intro n
      exact Eventually.of_forall fun x => by
        by_cases hx : Δ φ x = 0
        · simp only [hx,mul_zero,norm_zero,le_refl]
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hwb n (tfLaplacian_support hφ hx)) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (hwlim x).mul_const (Δ φ x)
  have htL : Tendsto (fun n => ∫ x, maxMollify n h x*φ x) atTop (𝓝 (∫ x, h x*φ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => C*‖φ x‖)
    · intro n
      exact ((maxMollify_contDiff hh n).continuous.mul hφ.continuous).aestronglyMeasurable
    · exact (hφ.continuous.norm.integrable_of_hasCompactSupport hcφ.norm).const_mul C
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact maxMollify_bound (fun y _ => hhC y) n (le_refl ‖x‖)
    · filter_upwards [maxMollify_ae_tendsto hh] with x hx
      exact hx.mul_const (φ x)
  apply le_of_tendsto_of_tendsto htL htR
  filter_upwards [(shrinkingBump_tendsto (E := TFSpace)).eventually (gt_mem_nhds hδ)] with n hn
  have hks (x : TFSpace) (hx : x ∈ tsupport φ) :
      tsupport (fun y => maxKernel n (x-y)) ⊆ U := by
    intro y hy
    have hxy := tsupport_sub_left (fun z hz => maxKernel_support n hz) x hy
    apply hsδ
    exact mem_cthickening_of_dist_le y x δ (tsupport φ) hx ((mem_closedBall.mp hxy).trans hn.le)
  have hlow (x : TFSpace) (hx : x ∈ tsupport φ) : maxMollify n h x ≤ Δ (w n) x := by
    apply smoothMaximum_laplacian_lower (hε n) (maxMollify_contDiff hu.locallyIntegrable n)
      (maxMollify_contDiff hv.locallyIntegrable n)
    · exact weak_lower_convolution hu hwu (shrinkingBump n).contDiff_normed
        (shrinkingBump n).hasCompactSupport_normed (shrinkingBump n).nonneg_normed (hks x hx)
    · exact weak_lower_convolution hv hwv (shrinkingBump n).contDiff_normed
        (shrinkingBump n).hasCompactSupport_normed (shrinkingBump n).nonneg_normed (hks x hx)
  rw [compact_laplacian_green (hwd n) hφ hcφ]
  apply integral_mono
    (((maxMollify_contDiff hh n).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left)
    (((tfLaplacian_continuous (hwd n)).mul hφ.continuous).integrable_of_hasCompactSupport hcφ.mul_left)
  intro x
  change maxMollify n h x * φ x ≤ Δ (w n) x * φ x
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hlow x (subset_tsupport φ hx)) (hnφ x)

end CoulombBarrier

end

end OAI
