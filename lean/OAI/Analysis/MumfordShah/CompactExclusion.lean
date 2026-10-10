import Mathlib
import OAI.Analysis.MumfordShah.RotationRigidity

namespace OAI

/-! MumfordShah compact exclusion. -/

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
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Laplacian ContinuousLinearMap
open scoped ENNReal NNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

instance compactExclusionGradientCompleteSpace : CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

lemma connected_complement_of_null_subset {H B : Set ℂ} (hH : volume H = 0)
    (hD : IsConnected Hᶜ) (hB : B ⊆ H) : IsConnected Bᶜ := by
  have hd : Dense Hᶜ := Measure.dense_of_ae (μ := volume) (by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hH)
  apply hD.subset_closure (compl_subset_compl.mpr hB)
  rw [hd.closure_eq]
  exact subset_univ _

lemma affine_gradient_ae {O : Set ℂ} (hO : IsOpen O) (hO0 : volume Oᶜ = 0)
    {f : ℂ → ℝ} {G : ℂ → ℂ} (hG : ∀ᵐ x ∂volume, x ∈ O → G x = gradient f x)
    {L : ℂ →L[ℝ] ℝ} {b : ℝ} (hf : ∀ x ∈ O, f x = L x+b) :
    G =ᵐ[volume] fun _ => (toDual ℝ ℂ).symm L := by
  filter_upwards [hG,show ∀ᵐ x ∂volume, x ∈ O from ae_iff.mpr hO0] with x hx hxo
  rw [hx hxo]
  have he : f =ᶠ[𝓝 x] fun y => L y+b := by
    filter_upwards [hO.mem_nhds hxo] with y hy using hf y hy
  rw [Filter.EventuallyEq.gradient_eq he]
  unfold gradient
  rw [(L.hasFDerivAt.add_const b).fderiv]

lemma gradient_zero_of_affine_decomposition {v : Pair} {O : Set ℂ}
    (hO : IsOpen O) (hO0 : volume Oᶜ = 0) {f : ℂ → ℝ} {G e : ℂ → ℂ}
    (he : MemLp e 2 volume) (hGeq : ∀ᵐ x ∂volume, x ∈ O → G x = gradient f x)
    (hgm : v.grad =ᵐ[volume] fun x => G x+(e x-compactGradientProjection (he.toLp e) x))
    {C : ℝ} (hgrowth : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G x‖^2) ≤ C*(1+R))
    (haff : ∃ L : ℂ →L[ℝ] ℝ, ∃ b : ℝ, ∀ x ∈ O, f x = L x+b)
    (hint : (∫ x : ℂ, inner ℝ (G x) (e x)) =
      -(∫ x : ℂ, inner ℝ (e x-compactGradientProjection (he.toLp e) x)
        (e x-compactGradientProjection (he.toLp e) x))) :
    G =ᵐ[volume] 0 ∧ v.grad =ᵐ[volume] 0 := by
  obtain ⟨L,b,hf⟩ := haff
  have hGa := affine_gradient_ae hO hO0 hGeq hf
  have hc := constant_field_eq_zero_of_linear_energy_growth hGa hgrowth
  have hG0 : G =ᵐ[volume] 0 := by
    change G =ᵐ[volume] fun _ => 0
    simpa only [hc] using hGa
  have hleft : (∫ x : ℂ, inner ℝ (G x) (e x)) = 0 := by
    trans ∫ x : ℂ, (0:ℝ)
    · apply integral_congr_ae
      filter_upwards [hG0] with x hx
      simp [hx]
    · simp
  let p := fun x => e x-compactGradientProjection (he.toLp e) x
  have hp : MemLp p 2 volume := he.sub (Lp.memLp _)
  have hsq : (∫ x : ℂ, ‖p x‖^2) = 0 := by
    simpa only [hleft,real_inner_self_eq_norm_sq,neg_eq_zero] using hint.symm
  have hae : ∀ᵐ x ∂volume, ‖p x‖^2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖p x‖)
      (hp.integrable_norm_pow (by norm_num))).mp hsq
  refine ⟨hG0,?_⟩
  filter_upwards [hgm,hG0,hae] with x hx hy hz
  have hp0 : p x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  simpa only [Pi.zero_apply,hy,show e x-compactGradientProjection (he.toLp e) x = 0 from hp0,add_zero] using hx

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Laplacian ContinuousLinearMap
open scoped ENNReal NNReal ContDiff

theorem minimizer_gradient_zero_of_compact_piece {v : Pair}
    (hv : GlobalAbsoluteMinimizer v) (hD : IsConnected v.Kᶜ)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hH : v.K = A ∪ B) (hArc : ContainsOpenC1Arc A v.K)
    {C : ℝ} (hm : ∀ R : ℝ, 1 ≤ R →
      (∫ x in ball (0:ℂ) R, ‖v.grad x‖^2) ≤ C*(1+R)) :
    v.grad =ᵐ[volume] 0 := by
  have hH0 := volume_eq_zero_of_locally_finite_length hv.1.2.2.1
  have hBs : B ⊆ v.K := by rw [hH]; exact subset_union_right
  have hB0 : volume B = 0 := measure_mono_null hBs hH0
  have hOc : IsConnected Bᶜ := connected_complement_of_null_subset hH0 hD hBs
  have hAO : A ⊆ Bᶜ := disjoint_left.mp hAB
  obtain ⟨h,e,he,φ,f,G,C',r,hh,hhc,hht,hpot,hf,hGeq,hueq,hgm,hGL,hC',hg,hr,htests⟩ :=
    minimizer_decomposition_with_jump_interactions hv hA hB hAB hH hm
  have hints : ∀ k : ℂ → ℝ, ∀ d : ℂ → ℂ, SobolevOn k d Aᶜ →
      IsCompact (essentialSupport k) → ∀ t ∈ ball (0:ℂ) r,
      (∫ z : ℂ, inner ℝ (G z) (d (z-t))) = ∫ z : ℂ, inner ℝ (G z) (d z) := by
    intro k d hkd hkc t ht
    obtain ⟨hd,ψ,hψ,hint⟩ := htests k d hkd hkc
    have h0 := hint 0 (mem_ball_self hr)
    simpa only [sub_zero] using (hint t ht).trans h0.symm
  have haff := harmonic_affine_of_arc_jump_interactions hA.isClosed hB.isOpen_compl hOc hAO hArc
    hf hGeq hr hints
  obtain ⟨hd,ψ,hψ,hint⟩ := htests h e hh hhc
  have hself := hint 0 (mem_ball_self hr)
  simp only [sub_zero] at hself
  exact (gradient_zero_of_affine_decomposition hB.isOpen_compl (by simpa) he hGeq hgm hg haff hself).2

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

instance compactExclusionConstantCompleteSpace : CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

lemma global_admissible_constant_of_gradient_zero {v : Pair} (hv : GlobalAdmissible v)
    (hD : IsConnected v.Kᶜ) (hzero : v.grad =ᵐ[volume] 0) :
    ∃ c : ℝ, v.u =ᵐ[volume] fun _ => c := by
  have hH0 := volume_eq_zero_of_locally_finite_length hv.2.2.1
  have hO : IsOpen v.Kᶜ := hv.1.isOpen_compl
  have hu : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → SobolevOn v.u v.grad (S ∩ v.Kᶜ) := by
    intro S hS hb
    exact hv.2.2.2 S hS hb
  have hw : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S → MemLp v.grad 2 (volume.restrict S) := by
    intro S hS hb
    have hh := (hv.2.2.2 S hS hb).2.1
    rwa [restrict_diff_null_set hH0] at hh
  have huli : LocallyIntegrable v.u volume := by
    intro x
    refine ⟨ball x 1,ball_mem_nhds x zero_lt_one,?_⟩
    let : IsFiniteMeasure (volume.restrict (ball x 1)) :=
      isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
    have hh := (hv.2.2.2 (ball x 1) isOpen_ball isBounded_ball).1
    rw [restrict_diff_null_set hH0] at hh
    exact hh.integrable (by norm_num)
  have hdiv : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ v.Kᶜ →
      (∫ x : ℂ, inner ℝ (v.grad x) (gradient ψ x)) = 0 := by
    intro ψ hψ hc ht
    trans ∫ x : ℂ, (0:ℝ)
    · apply integral_congr_ae
      filter_upwards [hzero] with x hx
      simp only [hx,Pi.zero_apply,inner_zero_left]
    · simp
  obtain ⟨f,hfeq,hfs,hfh,hfw,hgf⟩ := local_sobolev_divergence_free_regular hO hu hw huli hdiv
  have hgradC : ContinuousOn (gradient f) v.Kᶜ := fun x hx =>
    (gradient_contDiffAt_of_two (hfh x hx).1).continuousAt.continuousWithinAt
  have hgae : gradient f =ᵐ[volume.restrict v.Kᶜ] 0 := by
    filter_upwards [ae_restrict_of_ae hgf,ae_restrict_of_ae hzero,ae_restrict_mem hO.measurableSet] with x hx hz hxo
    exact (hx hxo).trans hz
  have hgrad := Measure.eqOn_open_of_ae_eq hgae hO hgradC continuousOn_const
  have hfd : v.Kᶜ.EqOn (fderiv ℝ f) 0 := by
    intro x hx
    rw [← toDual_gradient,hgrad hx]
    simp
  obtain ⟨c,hc⟩ := hO.exists_is_const_of_fderiv_eq_zero hD.isPreconnected
    (hfs.differentiableOn (by norm_num)) hfd
  refine ⟨c,?_⟩
  filter_upwards [hfeq,show ∀ᵐ x ∂volume, x ∈ v.Kᶜ from by simpa [ae_iff] using hH0] with x hx hxo
  exact hx.symm.trans (hc x hxo)

lemma sobolevOn_constant {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U) (c : ℝ) :
    SobolevOn (fun _ : ℂ => c) (fun _ => (0:ℂ)) U := by
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hh := sobolevOn_of_contDiffOn hU ((contDiff_const (c := c)).contDiffOn)
    (memLp_const c) (show MemLp (gradient (fun _ : ℂ => c)) 2 (volume.restrict U) by simp)
  simpa only [gradient_fun_const'] using hh

theorem no_compact_piece_of_gradient_zero {v : Pair} (hv : GlobalAbsoluteMinimizer v)
    (hD : IsConnected v.Kᶜ) (hzero : v.grad =ᵐ[volume] 0)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hH : v.K = A ∪ B) (hAl : 0 < lengthMeasure A) : False := by
  obtain ⟨c,hc⟩ := global_admissible_constant_of_gradient_zero hv.1 hD hzero
  let q : Pair := ⟨v.u,B,fun _ => 0⟩
  have hBs : B ⊆ v.K := by rw [hH]; exact subset_union_right
  have hq : GlobalAdmissible q := by
    refine ⟨hB,hv.1.2.1.mono hBs,?_,?_⟩
    · intro R hR
      exact (measure_mono (inter_subset_inter_left _ hBs)).trans_lt (hv.1.2.2.1 R hR)
    · intro U hU hb
      exact (sobolevOn_constant (hU.sdiff hB) (hb.subset sdiff_subset) c).congr_ae hc
  obtain ⟨R,hR,hAR⟩ := hA.isBounded.exists_pos_norm_lt
  have haV : A ⊆ ball (0:ℂ) R := fun x hx => by simpa only [mem_ball,dist_zero_right] using hAR x hx
  have hchange : (q.K ∆ v.K) ∪ essentialSupport (fun x => q.u x-v.u x) = A := by
    have he0 : essentialSupport (fun x => q.u x-v.u x) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hx 1 zero_lt_one
      filter_upwards [] with y
      simp only [q,sub_self]
    rw [he0,union_empty]
    ext x
    simp only [q,hH,mem_symmDiff,mem_union]
    have hd : x ∈ A → x ∈ B → False := fun ha hb => disjoint_left.mp hAB ha hb
    tauto
  have hcomp : IsCompactComparison v q (ball (0:ℂ) R) := by
    unfold IsCompactComparison CompactlyContained
    rw [hchange,hA.isClosed.closure_eq]
    exact ⟨hA,haV⟩
  have hineq := hv.2 (ball 0 R) isOpen_ball isBounded_ball q hq hcomp
  have hdir : (∫⁻ x in ball (0:ℂ) R \ v.K, ENNReal.ofReal (‖v.grad x‖^2)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_of_ae hzero] with x hx
    simp [hx]
  have hset : v.K ∩ ball (0:ℂ) R = A ∪ (B ∩ ball 0 R) := by
    ext x
    simp only [hH,mem_inter_iff,mem_union]
    have hx := @haV x
    tauto
  have hd : Disjoint A (B ∩ ball (0:ℂ) R) := hAB.mono_right inter_subset_left
  have hBl : lengthMeasure (B ∩ ball (0:ℂ) R) ≠ ⊤ :=
    ((measure_mono (inter_subset_inter_left _ hBs)).trans_lt (hv.1.2.2.1 R hR)).ne
  have hless : lengthMeasure A + lengthMeasure (B ∩ ball (0:ℂ) R) ≤
      0 + lengthMeasure (B ∩ ball (0:ℂ) R) := by
    simpa only [homogeneousEnergy,q,hdir,hset,measure_union hd (hB.measurableSet.inter measurableSet_ball),
      norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero,lintegral_zero,zero_add] using hineq
  have hAz : lengthMeasure A ≤ 0 := (ENNReal.add_le_add_iff_right hBl).mp hless
  exact (not_lt_of_ge hAz) hAl

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open Laplacian ContinuousLinearMap
open scoped ENNReal NNReal ContDiff symmDiff

theorem compactPieceExclusion : CompactPieceExclusion := by
  intro v hv hD hgrowth hpiece
  obtain ⟨C,hC⟩ := hgrowth
  obtain ⟨A,hA,hAH,hAl,hB,hsep,hArc⟩ := hpiece
  have hAB : Disjoint A (v.K \ A) := disjoint_sdiff_self_right
  have hH : v.K = A ∪ (v.K \ A) := by
    ext x
    change (x ∈ v.K) ↔ (x ∈ A ∨ (x ∈ v.K ∧ x ∉ A))
    have hx := @hAH x
    tauto
  have hzero := minimizer_gradient_zero_of_compact_piece hv hD hA hB hAB hH hArc hC
  exact no_compact_piece_of_gradient_zero hv hD hzero hA hB hAB hH hAl

end MumfordShah

end

end OAI
