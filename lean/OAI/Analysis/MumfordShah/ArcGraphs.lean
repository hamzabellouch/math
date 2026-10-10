import Mathlib
import OAI.Analysis.MumfordShah.GraphCalculus

namespace OAI

/-! MumfordShah arc graphs. -/

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
open Filter
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Laplacian ContinuousLinearMap
open scoped ENNReal NNReal ContDiff
open Set Metric Topology InnerProductSpace Complex MeasureTheory
open scoped ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

lemma real_compact_smooth_cutoff {A O : Set ℝ} (hA : IsCompact A)
    (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ O ∧ (∀ x ∈ A, χ =ᶠ[𝓝 x] 1) ∧ ∀ x, χ x ∈ Icc (0:ℝ) 1 := by
  obtain ⟨R, hAR⟩ := hA.isBounded.subset_ball (0 : ℝ)
  obtain ⟨V, hV, hAV, hVO⟩ := hA.exists_isOpen_closure_subset
    ((hO.inter isOpen_ball).mem_nhdsSet.mpr (subset_inter hAO hAR))
  have hVc : IsCompact (closure V) := (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset
    isClosed_closure (hVO.trans (inter_subset_right.trans ball_subset_closedBall))
  obtain ⟨W, hW, hAW, hWV⟩ := hA.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hAV)
  obtain ⟨χ, hχ, hχrange, hχsupp, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (modelWithCornersSelf ℝ ℝ) (n := (⊤ : ℕ∞))
      hV isClosed_closure hWV
  have hts : tsupport χ = closure V := by rw [tsupport, hχsupp]
  refine ⟨χ, contMDiff_iff_contDiff.mp hχ, ?_, ?_, ?_, ?_⟩
  · simpa [HasCompactSupport, hts] using hVc
  · rw [hts]
    exact hVO.trans inter_subset_left
  · intro x hx
    filter_upwards [hW.mem_nhds (hAW hx)] with y hy
    exact (hχone y).mp (subset_closure hy)
  · intro x
    exact hχrange (mem_range_self x)

lemma contDiffAt_real_extension {κ : ℝ → ℝ} {s : ℝ} (hκ : ContDiffAt ℝ 1 κ s) :
    ∃ k : ℝ → ℝ, ContDiff ℝ 1 k ∧ k =ᶠ[𝓝 s] κ := by
  obtain ⟨U,hκU,hU,hsU⟩ := _root_.eventually_nhds_iff.mp (hκ.eventually (by norm_num))
  have hkU : ContDiffOn ℝ 1 κ U := fun x hx => (hκU x hx).contDiffWithinAt
  obtain ⟨χ,hχ,hc,ht,hχ1,hrange⟩ := real_compact_smooth_cutoff (isCompact_singleton (x := s)) hU
    (singleton_subset_iff.mpr hsU)
  refine ⟨fun x => χ x * κ x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by norm_num)).contDiffAt.mul (hκU x hx)
    · have hn : x ∉ tsupport χ := fun hh => hx (ht hh)
      apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hn] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  · filter_upwards [hχ1 s (mem_singleton s)] with x hx
    simp only [Pi.one_apply] at hx
    simp only [hx,one_mul]

lemma local_graph_of_re_deriv_ne_zero {γ : ℝ → ℂ} {A : Set ℂ}
    (hγ : ContDiffAt ℝ 1 γ 0) (hd : (deriv γ 0).re ≠ 0)
    (hγA : ∀ᶠ s in 𝓝 (0:ℝ), γ s ∈ A) :
    ∃ κ : ℝ → ℝ, ContDiff ℝ 1 κ ∧
      ∃ I : Set ℝ, IsOpen I ∧ (γ 0).re ∈ I ∧
        ∀ s ∈ I, graphChart κ s 0 ∈ A := by
  let q : ℝ → ℝ := fun s => (γ s).re
  have hq : ContDiffAt ℝ 1 q 0 := Complex.reCLM.contDiff.contDiffAt.comp 0 hγ
  have hqd : HasDerivAt q (deriv γ 0).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hγ.differentiableAt (by norm_num)).hasDerivAt
  have hqe := hqd.hasFDerivAt_equiv hd
  let ψ : ℝ → ℝ := hq.localInverse hqe (by norm_num)
  have hψ : ContDiffAt ℝ 1 ψ (q 0) := hq.to_localInverse hqe (by norm_num)
  have hψ0 : ψ (q 0) = 0 := hq.localInverse_apply_image hqe (by norm_num)
  have hright : ∀ᶠ s in 𝓝 (q 0), q (ψ s) = s :=
    (hq.hasStrictFDerivAt' hqe (by norm_num)).eventually_right_inverse
  have hcomp : ContDiffAt ℝ 1 (fun s => (γ (ψ s)).im) (q 0) := by
    apply Complex.imCLM.contDiff.contDiffAt.comp
    exact (hψ0.symm ▸ hγ).comp _ hψ
  obtain ⟨κ,hκ,heκ⟩ := contDiffAt_real_extension hcomp
  have hA : ∀ᶠ s in 𝓝 (q 0), γ (ψ s) ∈ A :=
    (show Tendsto ψ (𝓝 (q 0)) (𝓝 0) by
      have ht : Tendsto ψ (𝓝 (q 0)) (𝓝 (ψ (q 0))) := hψ.continuousAt
      simpa only [hψ0] using ht).eventually hγA
  have hh : ∀ᶠ s in 𝓝 (q 0), graphChart κ s 0 ∈ A := by
    filter_upwards [hright,heκ,hA] with s hs hk ha
    have he : graphChart κ s 0 = γ (ψ s) := by
      apply Complex.ext
      · simpa only [graphChart,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
          Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] using hs.symm
      · simp [graphChart,hk]
    rwa [he]
  obtain ⟨I,hIA,hI,h0⟩ := _root_.eventually_nhds_iff.mp hh
  exact ⟨κ,hκ,I,hI,h0,hIA⟩

lemma containsOpenC1Arc_rotated_graph {A H : Set ℂ} (hArc : ContainsOpenC1Arc A H) :
    ∃ a : Circle, ∃ κ : ℝ → ℝ, ContDiff ℝ 1 κ ∧
      ∃ I : Set ℝ, IsOpen I ∧ ∃ s₀ ∈ I,
        ∀ s ∈ I, graphChart κ s 0 ∈ (_root_.rotation a) ⁻¹' A := by
  obtain ⟨U,hU,γ,hγ,hd,hemb,hH,hA⟩ := hArc
  have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) 1 := by norm_num
  have hc : ContDiffAt ℝ 1 γ 0 := hγ.contDiffAt (isOpen_Ioo.mem_nhds h0)
  have ha : ∀ᶠ s in 𝓝 (0:ℝ), γ s ∈ A := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
    apply hA
    rw [hH]
    exact mem_image_of_mem γ hs
  by_cases hv : (deriv γ 0).re ≠ 0
  · obtain ⟨κ,hκ,I,hI,hs,hIA⟩ := local_graph_of_re_deriv_ne_zero hc hv ha
    refine ⟨1,κ,hκ,I,hI,(γ 0).re,hs,?_⟩
    simpa only [map_one,LinearIsometryEquiv.coe_one,preimage_id] using hIA
  · have hdre : (deriv γ 0).re = 0 := not_ne_iff.mp hv
    have hdim : (deriv γ 0).im ≠ 0 := by
      intro he
      apply hd 0 h0
      exact Complex.ext hdre he
    let i : Circle := ⟨Complex.I,by change Complex.I ∈ sphere (0:ℂ) 1; simp⟩
    let R := _root_.rotation i
    let Γ : ℝ → ℂ := fun s => R (γ s)
    have hΓ : ContDiffAt ℝ 1 Γ 0 := R.toContinuousLinearEquiv.contDiff.contDiffAt.comp 0 hc
    have hΓd : deriv Γ 0 = R (deriv γ 0) :=
      (R.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt 0
        (hc.differentiableAt (by norm_num)).hasDerivAt).deriv
    have hΓre : (deriv Γ 0).re ≠ 0 := by
      rw [hΓd]
      change (Complex.I * deriv γ 0).re ≠ 0
      simpa only [Complex.mul_re,Complex.I_re,Complex.I_im,
        zero_mul,one_mul,zero_sub,neg_ne_zero] using hdim
    have hΓA : ∀ᶠ s in 𝓝 (0:ℝ), Γ s ∈ R.symm ⁻¹' A := by
      filter_upwards [ha] with s hs
      simpa only [mem_preimage,Γ,R.symm_apply_apply] using hs
    obtain ⟨κ,hκ,I,hI,hs,hIA⟩ := local_graph_of_re_deriv_ne_zero hΓ hΓre hΓA
    refine ⟨i⁻¹,κ,hκ,I,hI,(Γ 0).re,hs,?_⟩
    simpa only [R,_root_.rotation_symm] using hIA

lemma graphChart_add_height (κ : ℝ → ℝ) (s r : ℝ) :
    graphChart κ s r = graphChart κ s 0 + Complex.ofReal r * Complex.I := by
  simp only [graphChart,add_zero,Complex.ofReal_add]
  ring

lemma graph_strip_inside_open {A O : Set ℂ} (hO : IsOpen O) (hAO : A ⊆ O)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ 1 κ) {I : Set ℝ} (hI : IsOpen I)
    {s₀ : ℝ} (hs₀ : s₀ ∈ I) (hgraph : ∀ s ∈ I, graphChart κ s 0 ∈ A)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ J : Set ℝ, IsOpen J ∧ s₀ ∈ J ∧ J ⊆ I ∧
      ∃ η : ℝ → ℝ, ContDiff ℝ 1 η ∧ HasCompactSupport η ∧ η 0 = 1 ∧
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧
          ∀ s ∈ J, ∀ r ∈ tsupport η, ∀ t ∈ ball (0:ℂ) δ,
            graphChart κ s r+t ∈ O := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds (hAO (hgraph s₀ hs₀)))
  have hε3 : 0 < ε/3 := by positivity
  have hc : Continuous (fun s => graphChart κ s 0) := by
    have hk := hκ.continuous
    unfold graphChart
    fun_prop
  let J := I ∩ (fun s => graphChart κ s 0) ⁻¹' ball (graphChart κ s₀ 0) (ε/3)
  have hJ : IsOpen J := hI.inter (isOpen_ball.preimage hc)
  have hsJ : s₀ ∈ J := ⟨hs₀,mem_ball_self hε3⟩
  obtain ⟨η,hη,hcη,htη,hη1,_⟩ := real_compact_smooth_cutoff (isCompact_singleton (x := (0:ℝ)))
    isOpen_ball (singleton_subset_iff.mpr (mem_ball_self hε3))
  refine ⟨J,hJ,hsJ,inter_subset_left,η,hη.of_le (by norm_num),hcη,
    (hη1 0 (mem_singleton 0)).eq_of_nhds,min δ₀ (ε/3),lt_min hδ₀ hε3,min_le_left _ _,?_⟩
  intro s hs r hr t ht
  apply hball
  have hs' : dist (graphChart κ s 0) (graphChart κ s₀ 0) < ε/3 := hs.2
  have hr' : ‖(r:ℂ)*Complex.I‖ < ε/3 := by
    simpa only [mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Complex.norm_I,mul_one] using htη hr
  have ht' : ‖t‖ < ε/3 := (show ‖t‖ < min δ₀ (ε/3) by simpa only [mem_ball,dist_zero_right] using ht).trans_le (min_le_right _ _)
  rw [mem_ball,graphChart_add_height]
  have hdist := dist_triangle ((graphChart κ s 0+(r:ℂ)*Complex.I)+t) (graphChart κ s 0) (graphChart κ s₀ 0)
  have he : dist ((graphChart κ s 0+(r:ℂ)*Complex.I)+t) (graphChart κ s 0) = ‖(r:ℂ)*Complex.I+t‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  rw [he] at hdist
  have hn := norm_add_le ((r:ℂ)*Complex.I) t
  linarith

end MumfordShah
end

end OAI
