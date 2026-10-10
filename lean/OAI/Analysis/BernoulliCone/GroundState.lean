import OAI.Analysis.BernoulliCone.ConePicone

namespace OAI

universe uF

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Laplacian
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}
namespace GroundState

lemma compact_extension_near_test (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hφ : Test D φ) :
    ∃ F : Space d → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀x∈tsupport φ, F =ᶠ[𝓝 x] Y := by
  obtain ⟨χ,hχ,hχc,hχD,hχ1,_⟩ := exists_cutoff hφ.2.1 hD hφ.2.2
  refine ⟨fun x=>χ x*Y x,?_,hχc.mul_right,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x∈tsupport χ
    · exact hχ.contDiffAt.mul (hY.contDiffAt (hD.mem_nhds (hχD hx)))
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
  · intro x hx
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp [hy]

lemma compact_green {F φ : Space d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hφ : Test univ φ) :
    (∫x, inner ℝ (gradient F x) (gradient φ x)) = -(∫x, Δ F x*φ x) := by
  have hi := (show Test univ F from ⟨hF,hc,subset_univ _⟩).h1.laplacian_ibp hφ
  simp only [Measure.restrict_univ] at hi
  have hs := SchwartzMap.integral_mul_laplacian_right_eq_left
    (hc.toSchwartzMap hF) (hφ.2.1.toSchwartzMap hφ.1) (μ:=volume)
  simp only [SchwartzMap.laplacian_apply] at hs
  change (∫x, F x*Δ φ x)=(∫x, Δ F x*φ x) at hs
  linarith

lemma local_green (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hφ : Test D φ) :
    (∫x, inner ℝ (gradient Y x) (gradient φ x)) = -(∫x, Δ Y x*φ x) := by
  obtain ⟨F,hF,hFc,hFY⟩ := compact_extension_near_test hD hY hφ
  have hi := compact_green hF hFc (show Test univ φ from ⟨hφ.1,hφ.2.1,subset_univ _⟩)
  convert! hi using 1
  · apply integral_congr_ae
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        simp only [gradient,(hFY x hx).fderiv_eq]
      · have hz : gradient φ x=0 := by rw [gradient,fderiv_of_notMem_tsupport ℝ hx,map_zero]
        simp [hz]
  · congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        rw [(InnerProductSpace.laplacian_congr_nhds (hFY x hx)).eq_of_nhds]
      · simp [image_eq_zero_of_notMem_tsupport hx]

lemma local_green_integrable (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hφ : Test D φ) :
    Integrable (fun x=>inner ℝ (gradient Y x) (gradient φ x)) ∧
    Integrable (fun x=>Δ Y x*φ x) := by
  obtain ⟨F,hF,hFc,hFY⟩ := compact_extension_near_test hD hY hφ
  have hFtest : Test univ F := ⟨hF,hFc,subset_univ _⟩
  have hφtest : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hgrad := integrable_inner_of_memLp hFtest.memLp_gradient hφtest.memLp_gradient
  simp only [Measure.restrict_univ] at hgrad
  have hLap : Continuous (Δ F) := by
    let S := hFc.toSchwartzMap hF
    have he : (Laplacian.laplacian S : Space d → ℝ)=Δ F := funext fun x=>SchwartzMap.laplacian_apply S x
    exact he ▸ (Laplacian.laplacian S).continuous
  have hi : Integrable (fun x=>Δ F x*φ x) volume :=
    (hLap.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_left
  constructor
  · apply hgrad.congr
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        simp only [gradient,(hFY x hx).fderiv_eq]
      · have hz : gradient φ x=0 := by rw [gradient,fderiv_of_notMem_tsupport ℝ hx,map_zero]
        simp [hz]
  · apply hi.congr
    exact ae_of_all _ fun x=>by
      by_cases hx : x∈tsupport φ
      · dsimp only
        rw [(InnerProductSpace.laplacian_congr_nhds (hFY x hx)).eq_of_nhds]
      · simp [image_eq_zero_of_notMem_tsupport hx]

open Halfspace

lemma square_ratio_test (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x) (hφ : Test D φ) :
    Test D (positiveSquareRatio φ Y) := by
  have hs : tsupport (positiveSquareRatio φ Y)⊆tsupport φ := by
    apply closure_mono
    intro x hx
    by_contra hn
    have hz : φ x=0 := Function.notMem_support.mp hn
    change positiveSquareRatio φ Y x ≠ 0 at hx
    exact hx (by simp [positiveSquareRatio,hz])
  refine ⟨?_,hφ.2.1.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hφ.2.2⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈tsupport φ
  · have hy := hY.contDiffAt (hD.mem_nhds (hφ.2.2 hx))
    have hp := hYp x (hφ.2.2 hx)
    have he : positiveSquareRatio φ Y =ᶠ[𝓝 x] (fun y=>φ y^2/Y y) := by
      filter_upwards [hy.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp)] with y hh
      change 0 < Y y at hh
      simp only [positiveSquareRatio,ite_eq_left hh]
    exact ((hφ.1.contDiffAt.pow 2).div hy hp.ne').congr_of_eventuallyEq he
  · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change φ y = 0 at hy
    simp [positiveSquareRatio,hy]

lemma picone_identity (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x) (hφ : Test D φ) (x : Space d) :
    ‖gradient φ x-(φ x/Y x) • gradient Y x‖^2 = ‖gradient φ x‖^2-
      inner ℝ (gradient Y x) (gradient (positiveSquareRatio φ Y) x) := by
  by_cases hx : x∈D
  · rw [positiveSquareRatio_gradient
      ((hY.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp))
      (hφ.1.differentiable (by simp) x) (hYp x hx)]
    rw [norm_sub_sq_real]
    simp only [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_comm (gradient φ x) (gradient Y x)]
    ring
  · rw [hφ.eq_zero_outside hx,hφ.gradient_eq_zero_outside hx,
      (square_ratio_test hD hY hYp hφ).gradient_eq_zero_outside hx]
    simp

/-- Ground-state square completion for arbitrary compact smooth tests in a
positive superharmonic domain. It is proved by the weak integration-by-parts
identity, not inserted as an assumption about the explicit barrier. -/
theorem picone_test (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hφ : Test D φ) :
    (∫x, ‖gradient φ x-(φ x/Y x) • gradient Y x‖^2) ≤
      (∫x, ‖gradient φ x‖^2) := by
  have hq := square_ratio_test hD hY hYp hφ
  have hqi := local_green_integrable hD hY hq
  have hgr := local_green hD hY hq
  have hn : (∫x, Δ Y x*positiveSquareRatio φ Y x)≤0 := by
    apply integral_nonpos
    intro x
    by_cases hx : x∈D
    · exact mul_nonpos_of_nonpos_of_nonneg (hLap x hx) (positiveSquareRatio_nonneg x)
    · simp [hq.eq_zero_outside hx]
  have hφtest : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hi := hφtest.memLp_gradient.integrable_norm_pow (show (2:ℕ)≠0 by simp)
  simp only [Measure.restrict_univ] at hi
  simp_rw [picone_identity hD hY hYp hφ]
  rw [integral_sub hi hqi.1]
  linarith

lemma drift_test_memLp (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x) (hφ : Test D φ) :
    MemLp (fun x=>gradient φ x-(φ x/Y x) • gradient Y x) 2 volume := by
  have hc : Continuous (fun x=>(φ x/Y x) • gradient Y x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x∈tsupport φ
    · have hy := hY.contDiffAt (hD.mem_nhds (hφ.2.2 hx))
      exact (hφ.1.continuous.continuousAt.div hy.continuousAt (hYp x (hφ.2.2 hx)).ne').smul
        ((InnerProductSpace.toDual ℝ (Space d)).symm.continuous.continuousAt.comp
          (hy.continuousAt_fderiv (by simp)))
    · apply (continuousAt_const (y:=(0:Space d))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change φ y=0 at hy
      simp [hy]
  have hs : HasCompactSupport (fun x=>(φ x/Y x) • gradient Y x) := by
    apply hφ.2.1.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    change (φ x/Y x) • gradient Y x ≠ 0 at hx
    change φ x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hφt : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hg := hφt.memLp_gradient
  simp only [Measure.restrict_univ] at hg
  exact hg.sub (hc.memLp_of_hasCompactSupport hs)

lemma integral_norm_sq_eq {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure (Space d)} {f : Space d → F} (hf : MemLp f 2 μ) :
    (∫x, ‖f x‖^2 ∂μ)=‖hf.toLp f‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq]

lemma picone_test_eLpNorm (hD : IsOpen D) {Y φ : Space d → ℝ}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hφ : Test D φ) :
    eLpNorm (fun x=>gradient φ x-(φ x/Y x) • gradient Y x) 2 (volume.restrict D) ≤
      eLpNorm (gradient φ) 2 (volume.restrict D) := by
  have hφt : Test univ φ := ⟨hφ.1,hφ.2.1,subset_univ _⟩
  have hg := hφt.memLp_gradient
  simp only [Measure.restrict_univ] at hg
  have hl := drift_test_memLp hD hY hYp hφ
  have hi := picone_test hD hY hYp hLap hφ
  rw [integral_norm_sq_eq hl,integral_norm_sq_eq hg] at hi
  have hn : ‖hl.toLp _‖ ≤ ‖hg.toLp _‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hi
  have hh : eLpNorm (fun x=>gradient φ x-(φ x/Y x) • gradient Y x) 2 volume ≤
      eLpNorm (gradient φ) 2 volume := by
    rw [← Lp.enorm_toLp hl,← Lp.enorm_toLp hg,← ofReal_norm,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hn
  have he : eLpNorm (gradient φ) 2 (volume.restrict D)=eLpNorm (gradient φ) 2 volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hD.measurableSet]
    congr 1
    ext x
    by_cases hx : x∈D
    · simp [hx]
    · simp [hx,hφ.gradient_eq_zero_outside hx]
  rw [he]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hh

/-- The full H¹₀ ground-state inequality. Fatou's lemma handles the singular
coefficient at the boundary or cone vertex; no bounded-drift or Hardy hypothesis
is imposed. -/
theorem picone_h10_eLpNorm (hD : IsOpen D) {Y w : Space d → ℝ} {G : Space d → Space d}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hw : H10 D w G) :
    MemLp (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict D) ∧
    eLpNorm (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict D) ≤
      eLpNorm G 2 (volume.restrict D) := by
  obtain ⟨φ,hφ,hφw,hφG⟩ := SobolevCalculus.H10_sequence hw
  have htψ := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2:ENNReal)≠0)
    hφw
  have htG := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2:ENNReal)≠0)
    hφG
  obtain ⟨a,ha,haw⟩ := htψ.exists_seq_tendsto_ae
  obtain ⟨b,hb,hbG⟩ := (htG.comp ha.tendsto_atTop).exists_seq_tendsto_ae
  let ψ := fun n=>φ (a (b n))
  have hψ : ∀n, Test D (ψ n) := fun n=>hφ (a (b n))
  let T := fun n x=>gradient (ψ n) x-(ψ n x/Y x) • gradient Y x
  let L := fun x=>G x-(w x/Y x) • gradient Y x
  have hT : ∀n, MemLp (T n) 2 (volume.restrict D) := fun n=>
    (drift_test_memLp hD hY hYp (hψ n)).mono_measure Measure.restrict_le_self
  have hTL : ∀ᵐ x ∂volume.restrict D, Tendsto (fun n=>T n x) atTop (𝓝 (L x)) := by
    filter_upwards [haw,hbG] with x hx hy
    exact hy.sub (((hx.comp hb.tendsto_atTop).div_const (Y x)).smul tendsto_const_nhds)
  have hLm := aestronglyMeasurable_of_tendsto_ae _
    (fun n=>(hT n).aestronglyMeasurable) hTL
  have hl := Lp.eLpNorm_lim_le_liminf_eLpNorm (p:=2)
    (fun n=>(hT n).aestronglyMeasurable) L hLm hTL
  have hGnorm : Tendsto (fun n=>eLpNorm (gradient (ψ n)) 2 (volume.restrict D)) atTop
      (𝓝 (eLpNorm G 2 (volume.restrict D))) := by
    have hLp : Tendsto (fun n=>(hφ n).memLp_gradient.toLp (gradient (φ n))) atTop
        (𝓝 (hw.1.2.1.toLp G)) := by
      apply tendsto_iff_enorm_sub_tendsto_zero.mpr
      simpa only [← MemLp.toLp_sub,Lp.enorm_toLp] using hφG
    have hh := hLp.enorm.comp (ha.tendsto_atTop.comp hb.tendsto_atTop)
    simpa only [Lp.enorm_toLp,Function.comp_def,ψ] using hh
  have hbound : eLpNorm L 2 (volume.restrict D) ≤ eLpNorm G 2 (volume.restrict D) := by
    refine hl.trans ?_
    rw [← hGnorm.liminf_eq]
    apply Filter.liminf_le_liminf
    · exact Eventually.of_forall fun n=>picone_test_eLpNorm hD hY hYp hLap (hψ n)
    all_goals isBoundedDefault
  exact ⟨hbound.trans_lt hw.1.2.1,hbound⟩

theorem picone_h10 (hD : IsOpen D) {Y w : Space d → ℝ} {G : Space d → Space d}
    (hY : ContDiffOn ℝ ∞ Y D) (hYp : ∀x∈D, 0<Y x)
    (hLap : ∀x∈D, Δ Y x≤0) (hw : H10 D w G) :
    (∫x in D, ‖G x-(w x/Y x) • gradient Y x‖^2) ≤
      (∫x in D, ‖G x‖^2) := by
  obtain ⟨hl,hb⟩ := picone_h10_eLpNorm hD hY hYp hLap hw
  have ht := ENNReal.toReal_mono hw.1.2.1.ne hb
  rw [integral_norm_sq_eq hl,integral_norm_sq_eq hw.1.2.1,Lp.norm_toLp,Lp.norm_toLp]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg ht 2

lemma orthogonal_h10_of_tests {G : Space d → Space d}
    (hG : MemLp G 2 (volume.restrict D))
    (ht : ∀φ, Test D φ → (∫x in D, inner ℝ (G x) (gradient φ x))=0) :
    ∀v V, H10 D v V → (∫x in D, inner ℝ (G x) (V x))=0 := by
  intro v V hv
  obtain ⟨f,hf,_,hfG⟩ := SobolevCalculus.H10_sequence hv
  have hl : Tendsto (fun n => (hf n).memLp_gradient.toLp (gradient (f n)))
      atTop (𝓝 (hv.1.2.1.toLp V)) := by
    apply tendsto_iff_enorm_sub_tendsto_zero.mpr
    simpa only [← MemLp.toLp_sub,Lp.enorm_toLp] using hfG
  have hi : Tendsto (fun n => inner ℝ (hG.toLp G)
      ((hf n).memLp_gradient.toLp (gradient (f n)))) atTop
      (𝓝 (inner ℝ (hG.toLp G) (hv.1.2.1.toLp V))) := tendsto_const_nhds.inner hl
  have he n : inner ℝ (hG.toLp G) ((hf n).memLp_gradient.toLp (gradient (f n)))=0 := by
    rw [L2.inner_def]
    convert! ht (f n) (hf n) using 1
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp,(hf n).memLp_gradient.coeFn_toLp] with x hx hy
    rw [hx,hy]
  simp only [he] at hi
  have hz := tendsto_nhds_unique hi tendsto_const_nhds
  rw [L2.inner_def] at hz
  convert! hz using 1
  apply integral_congr_ae
  filter_upwards [hG.coeFn_toLp,hv.1.2.1.coeFn_toLp] with x hx hy
  rw [hx,hy]

theorem harmonic_h10 (hD : IsOpen D) {u w : Space d → ℝ} {G : Space d → Space d}
    (hu : ContDiffOn ℝ ∞ u D) (hLap : ∀x∈D, Δ u x=0)
    (hG : MemLp (gradient u) 2 (volume.restrict D)) (hw : H10 D w G) :
    (∫x in D, inner ℝ (gradient u x) (G x))=0 := by
  apply orthogonal_h10_of_tests hG _ w G hw
  intro φ hφ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx=>by rw [hφ.gradient_eq_zero_outside hx,inner_zero_right])]
  rw [local_green hD hu hφ]
  suffices hh : (fun x=>Δ u x*φ x)=(fun _=>0) by rw [hh,integral_zero,neg_zero]
  ext x
  by_cases hx:x∈D
  · simp [hLap x hx]
  · simp [hφ.eq_zero_outside hx]

end GroundState
end Bernoulli

end
end

end OAI
