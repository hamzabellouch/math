import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierWeakMaxBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierWeakMaxGeneral_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

open CoulombAnalysis CoulombPDE CoulombAtom

lemma maxMollify_test_pairing {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (n : ℕ) :
    (∫ x, maxMollify n h x * φ x) =
      maxMollify n (h ⋆[newtonMul] (fun x => φ (-x))) 0 := by
  let φ' : TFSpace → ℝ := fun x => φ (-x)
  have hd : Continuous φ' := hφ.comp continuous_neg
  have hc : HasCompactSupport φ' := hcφ.comp_homeomorph (Homeomorph.neg TFSpace)
  have hk : Continuous (maxKernel n) := (shrinkingBump n).continuous_normed
  have hkc : HasCompactSupport (maxKernel n) := (shrinkingBump n).hasCompactSupport_normed
  have hhn : LocallyIntegrable (fun x => ‖h x‖) := fun x => (hh x).norm
  have hfg := hkc.convolutionExists_left newtonMul hk hh
  have hgk := hc.norm.convolutionExists_right newtonMul hhn hd.norm
  have hgkc := hc.norm.continuous_convolution_right newtonMul hhn hd.norm
  have hfgk := hkc.norm.convolutionExists_left_of_continuous_right (μ := volume) newtonMul
    hk.norm.locallyIntegrable hgkc 0
  have ha := convolution_assoc newtonMul newtonMul newtonMul newtonMul
    (fun x y z : ℝ => mul_assoc x y z) hk.aestronglyMeasurable
    hh.aestronglyMeasurable hd.aestronglyMeasurable
    (Eventually.of_forall hfg) (Eventually.of_forall hgk) hfgk
  simpa only [maxMollify,convolution_def, newtonMul, ContinuousLinearMap.mul_apply',zero_sub,φ',neg_neg] using ha

lemma maxMollify_test_tendsto {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, maxMollify n h x * φ x) atTop (𝓝 (∫ x, h x*φ x)) := by
  let φ' : TFSpace → ℝ := fun x => φ (-x)
  have hd : Continuous φ' := hφ.comp continuous_neg
  have hc : HasCompactSupport φ' := hcφ.comp_homeomorph (Homeomorph.neg TFSpace)
  have ht := maxMollify_tendsto (hc.continuous_convolution_right newtonMul hh hd) 0
  simp_rw [maxMollify_test_pairing hh hφ hcφ]
  convert ht using 1
  simp only [convolution_def,newtonMul,ContinuousLinearMap.mul_apply',zero_sub,φ',neg_neg]

theorem weak_maximum_common_locallyIntegrable_source {U : Set TFSpace} (hU : IsOpen U)
    {u v h : TFSpace → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hh : LocallyIntegrable h)
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
  have htL := maxMollify_test_tendsto hh hφ.continuous hcφ
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

end Work_BarrierWeakMaxGeneral_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology Convolution BigOperators Manifold

open CoulombAnalysis CoulombPDE CoulombAtom

lemma locallyIntegrable_mul_test {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => h x*φ x) :=
  hh.integrable_smul_right_of_hasCompactSupport hφ hcφ

lemma laplacian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → TFSpace → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : TFSpace) :
    Δ (∑ i ∈ s, f i) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Pi.zero_def,laplacian_const]
  | @insert i s hi ih =>
    have hi' := hf i (Finset.mem_insert_self _ _)
    have hs' : ∀ j ∈ s, ContDiff ℝ 2 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsD : ContDiff ℝ 2 (∑ j ∈ s, f j) := by
      simpa only [←Finset.sum_apply] using ContDiff.sum hs'
    rw [Finset.sum_insert hi,hi'.contDiffAt.laplacian_add hsD.contDiffAt,
      ih hs',Finset.sum_insert hi]

theorem weak_lower_open_cover {ι : Type*} {V : ι → Set TFSpace}
    (hV : ∀ i, IsOpen (V i)) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : ∀ i, WeakLaplacianLowerOn (V i) u h) :
    WeakLaplacianLowerOn (⋃ i, V i) u h := by
  classical
  intro φ hφ hcφ hsφ hnφ
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ,TFSpace))
    (isClosed_tsupport φ) V hV hsφ
  let s := (ρ.locallyFinite.finite_nonempty_inter_compact hcφ.isCompact).toFinset
  let ψ : ι → TFSpace → ℝ := fun i x => ρ i x*φ x
  have hψd (i : ι) : ContDiff ℝ 2 (ψ i) :=
    ((ρ i).contMDiff.contDiff.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).mul hφ
  have hψc (i : ι) : HasCompactSupport (ψ i) := hcφ.mul_left
  have hψs (i : ι) : tsupport (ψ i) ⊆ V i := tsupport_mul_subset_left.trans (hρ i)
  have hψn (i : ι) (x : TFSpace) : 0 ≤ ψ i x := mul_nonneg (ρ.nonneg i x) (hnφ x)
  have hψzero {i : ι} (hi : i ∉ s) (x : TFSpace) : ψ i x = 0 := by
    dsimp [ψ]
    by_cases h1 : ρ i x = 0
    · rw [h1,zero_mul]
    · have h2 : φ x = 0 := by
        by_contra h2
        apply hi
        exact (Set.Finite.mem_toFinset _).mpr ⟨x,h1,subset_tsupport φ h2⟩
      rw [h2,mul_zero]
  have hsum : ∑ i ∈ s, ψ i = φ := by
    funext x
    rw [Finset.sum_apply]
    calc
      ∑ i ∈ s, ψ i x = ∑ᶠ i, ψ i x :=
        (finsum_eq_sum_of_support_subset (fun i => ψ i x) (s := s) fun i hi => by
          by_contra hn
          exact hi (hψzero hn x)).symm
      _ = φ x := by
        dsimp only [ψ]
        rw [←finsum_mul]
        by_cases hx : φ x = 0
        · rw [hx,mul_zero]
        · rw [ρ.sum_eq_one (subset_tsupport φ hx),one_mul]
  have hLp : (∫ x, h x*φ x) = ∑ i ∈ s, ∫ x, h x*ψ i x := by
    conv_lhs => rw [←hsum]
    simp only [Finset.sum_apply,Finset.mul_sum]
    exact integral_finsetSum s (fun i _ => locallyIntegrable_mul_test hh (hψd i).continuous (hψc i))
  have hRp : (∫ x, u x*Δ φ x) = ∑ i ∈ s, ∫ x, u x*Δ (ψ i) x := by
    conv_lhs => rw [←hsum]
    simp_rw [laplacian_finset_sum s ψ (fun i _ => hψd i),Finset.mul_sum]
    exact integral_finsetSum s (fun i _ => locallyIntegrable_mul_test hu
      (tfLaplacian_continuous (hψd i)) (tfLaplacian_compact (hψd i) (hψc i)))
  rw [hLp,hRp]
  exact Finset.sum_le_sum fun i _ => hw i _ (hψd i) (hψc i) (hψs i) (hψn i)

end CoulombBarrier

end

end OAI
