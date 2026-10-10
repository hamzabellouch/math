import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Holonomy.CompactHolonomy

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {T : X → X}

lemma observation_integral_rate {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∫ x, (observationCocycle g hT.measurable hg h0 h1).lowerRate x ∂μ = ∫ x,g x ∂μ := by
  let f := observationCocycle g hT.measurable hg h0 h1
  have hi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (h0 x)]; exact h1 x)
  have him (i : ℕ) : Integrable (fun x => g (T^[i] x)) μ := (hT.iterate i).integrable_comp_of_integrable hi
  have he (n : ℕ) (hn : n≠0) : (∫ x,f.average n x ∂μ)=∫ x,g x ∂μ := by
    change (∫ x,birkhoffSum T g n x/(n : ℝ) ∂μ)=_
    rw [integral_div]
    have hs : (∫ x,birkhoffSum T g n x ∂μ)=(n : ℝ)*(∫ x,g x ∂μ) := by
      unfold birkhoffSum
      rw [integral_finsetSum _ (fun i _ => him i)]
      simp only [BoundedSubadditive.integral_comp (hT.iterate _) hi.aestronglyMeasurable,
        Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [hs,mul_div_cancel_left₀ _ (by exact_mod_cast hn)]
  have ht := f.tendsto_integral_average hT
  have hc : Tendsto (fun n => ∫ x,f.average n x ∂μ) atTop (𝓝 (∫ x,g x ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (he n hn).symm
  exact tendsto_nhds_unique ht hc

theorem exists_bounded_birkhoff_limit {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x,0≤G x ∧ G x≤1) ∧ (∀ x,G (T x)=G x) ∧
      (∀ᵐ x ∂μ,Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 (G x))) ∧
      ∀ A : Set X, MeasurableSet A → T ⁻¹' A=A → ∫ x in A,G x ∂μ=∫ x in A,g x ∂μ := by
  let f := observationCocycle g hT.measurable hg h0 h1
  refine ⟨f.lowerRate,f.measurable_lowerRate,f.lowerRate_bounds,f.lowerRate_shift,f.ae_tendsto_average hT,?_⟩
  intro A hA hTA
  have hm : MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
    simpa only [hTA] using hT.restrict_preimage hA
  exact observation_integral_rate hm hg h0 h1

theorem forward_backward_birkhoff {μ : Measure X} [IsFiniteMeasure μ]
    {S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hST : ∀ x,S (T x)=x) (hTS : ∀ x,T (S x)=x)
    {g : X → ℝ} (hg : Measurable g) (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x,0≤G x ∧ G x≤1) ∧ (∀ x,G (T x)=G x) ∧
      ∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 (G x)) ∧
        Tendsto (fun n : ℕ => birkhoffSum S g n x/(n : ℝ)) atTop (𝓝 (G x)) := by
  obtain ⟨F,hFm,hFb,hFT,hFconv,hFint⟩ := exists_bounded_birkhoff_limit hT hg h0 h1
  obtain ⟨B,hBm,hBb,hBS,hBconv,hBint⟩ := exists_bounded_birkhoff_limit hS hg h0 h1
  have hFS (x : X) : F (S x)=F x := by simpa only [hTS] using (hFT (S x)).symm
  have hBT (x : X) : B (T x)=B x := by simpa only [hST] using (hBS (T x)).symm
  have hFi : Integrable F μ := (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hFb x).1]; exact (hFb x).2)
  have hBi : Integrable B μ := (integrable_const (1 : ℝ)).mono' hBm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hBb x).1]; exact (hBb x).2)
  have hle : F≤ᵐ[μ] B := by
    let A := {x | B x<F x}
    have hA : MeasurableSet A := measurableSet_lt hBm hFm
    have hAT : T ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBT,hFT]
    have hAS : S ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBS,hFS]
    have he : (∫ x in A,F x-B x ∂μ)=0 := by
      rw [integral_sub hFi.integrableOn hBi.integrableOn,hFint A hA hAT,hBint A hA hAS,sub_self]
    have hn : 0≤ᵐ[μ.restrict A] (fun x => F x-B x) :=
      (ae_restrict_mem hA).mono fun x hx => sub_nonneg.mpr (le_of_lt hx)
    have hz := (integral_eq_zero_iff_of_nonneg_ae hn (hFi.sub hBi).integrableOn).mp he
    filter_upwards [(ae_restrict_iff' hA).mp hz] with x hx
    by_contra he'
    have hh := hx (not_le.mp he')
    change F x-B x=0 at hh
    linarith
  have hge : B≤ᵐ[μ] F := by
    let A := {x | F x<B x}
    have hA : MeasurableSet A := measurableSet_lt hFm hBm
    have hAT : T ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBT,hFT]
    have hAS : S ⁻¹' A=A := by ext x; simp only [A,mem_preimage,mem_ofPred_eq,hBS,hFS]
    have he : (∫ x in A,B x-F x ∂μ)=0 := by
      rw [integral_sub hBi.integrableOn hFi.integrableOn,hFint A hA hAT,hBint A hA hAS,sub_self]
    have hn : 0≤ᵐ[μ.restrict A] (fun x => B x-F x) :=
      (ae_restrict_mem hA).mono fun x hx => sub_nonneg.mpr (le_of_lt hx)
    have hz := (integral_eq_zero_iff_of_nonneg_ae hn (hBi.sub hFi).integrableOn).mp he
    filter_upwards [(ae_restrict_iff' hA).mp hz] with x hx
    by_contra he'
    have hh := hx (not_le.mp he')
    change B x-F x=0 at hh
    linarith
  refine ⟨F,hFm,hFb,hFT,?_⟩
  filter_upwards [hFconv,hBconv,hle,hge] with x hx hy hxy hyx
  exact ⟨hx,by simpa only [le_antisymm hyx hxy] using hy⟩

end BoundedSubadditive

end
section
open MeasureTheory Filter Set Topology
open scoped Topology ENNReal BigOperators

lemma birkhoff_difference_tendsto_zero {X : Type*} [PseudoMetricSpace X]
    {T : X → X} {g : X → ℝ} (hg : UniformContinuous g) {x y : X}
    (hxy : Tendsto (fun n : ℕ => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)-birkhoffSum T g n y/(n : ℝ)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n : ℕ => g (T^[n] x)-g (T^[n] y)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hδg⟩ := Metric.uniformContinuous_iff.mp hg ε hε
    filter_upwards [hxy.eventually (eventually_lt_nhds hδ)] with n hn
    simpa only [Real.dist_eq,sub_zero] using hδg hn
  have hc := hdiff.cesaro
  convert hc using 1
  funext n
  simp only [birkhoffSum,Finset.sum_sub_distrib,div_eq_mul_inv]
  ring

lemma birkhoff_limit_eq_of_asymptotic {X : Type*} [PseudoMetricSpace X]
    {T : X → X} {g : X → ℝ} (hg : UniformContinuous g) {x y : X}
    (hxy : Tendsto (fun n : ℕ => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0))
    {a b : ℝ} (hx : Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 a))
    (hy : Tendsto (fun n : ℕ => birkhoffSum T g n y/(n : ℝ)) atTop (𝓝 b)) : a=b :=
  sub_eq_zero.mp (tendsto_nhds_unique (hx.sub hy) (birkhoff_difference_tendsto_zero hg hxy))

namespace StandardMapEntropy

lemma complexProjection_dist_le (z w : ℂ) : dist (complexProjection z) (complexProjection w)≤‖z-w‖ := by
  change max (dist (z.re : Circle) (w.re : Circle)) (dist (z.im : Circle) (w.im : Circle))≤‖z-w‖
  apply max_le
  · calc
      dist (z.re : Circle) (w.re : Circle)=‖((z.re-w.re : ℝ) : Circle)‖ := by
        rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      _ ≤ |z.re-w.re| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ ‖z-w‖ := Complex.abs_re_le_norm (z-w)
  · calc
      dist (z.im : Circle) (w.im : Circle)=‖((z.im-w.im : ℝ) : Circle)‖ := by
        rw [dist_eq_norm,←QuotientAddGroup.mk_sub]
      _ ≤ |z.im-w.im| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ ‖z-w‖ := Complex.abs_im_le_norm (z-w)

lemma fineStableCurve_asymptotic (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    Tendsto (fun n : ℕ => dist ((standardMap k)^[n] (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s)))
      ((standardMap k)^[n] (complexProjection (fineStableCurve k χ ε δ hδ hq w hw t)))) atTop (𝓝 0) := by
  have hq0 : 0≤Real.exp (-χ+ε)+δ := by positivity
  have hc := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (2*fineScale k ε δ)).mul_const |s-t|
  simp only [mul_zero,zero_mul] at hc
  simpa only [complexProjection_iterate] using squeeze_zero (fun _ => dist_nonneg)
    (fun n => (complexProjection_dist_le _ _).trans (fineStableCurve_contraction k χ ε δ hδ hq w hw hs ht n)) hc

theorem fineStableCurve_birkhoff_eq (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (g : C(Torus,ℝ)) {a b : ℝ}
    (ha : Tendsto (fun n : ℕ => birkhoffSum (standardMap k) g n
      (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s))/(n : ℝ)) atTop (𝓝 a))
    (hb : Tendsto (fun n : ℕ => birkhoffSum (standardMap k) g n
      (complexProjection (fineStableCurve k χ ε δ hδ hq w hw t))/(n : ℝ)) atTop (𝓝 b)) : a=b :=
  birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous g.continuous)
    (fineStableCurve_asymptotic k χ ε δ hδ hq w hw hs ht) ha hb

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineUnstableCurve (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w)))) : ℝ → ℂ :=
  fun s => tangentReversal (fineStableCurve k χ ε δ hδ hq (tangentReversal w) hw s)
@[simp] lemma fineUnstableCurve_zero (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w)))) :
    fineUnstableCurve k χ ε δ hδ hq w hw 0=w := by
  simp only [fineUnstableCurve,fineStableCurve_zero,tangentReversal_involutive]
lemma fineUnstableCurve_contraction (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardInverseLift k)^[n] (fineUnstableCurve k χ ε δ hδ hq w hw s)-
      (standardInverseLift k)^[n] (fineUnstableCurve k χ ε δ hδ hq w hw t)‖≤
      (6*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n*|s-t| := by
  simp only [fineUnstableCurve,inverse_lift_iterate_reversed,←map_sub]
  exact ((tangentReversal_norm_le _).trans (mul_le_mul_of_nonneg_left
    (fineStableCurve_contraction k χ ε δ hδ hq (tangentReversal w) hw hs ht n) (by norm_num))).trans_eq (by ring)
lemma fineUnstableCurve_contDiffOn (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w)))) :
    ContDiffOn ℝ 1 (fineUnstableCurve k χ ε δ hδ hq w hw) (Ioo (-1 : ℝ) 1) :=
  tangentReversal.contDiff.comp_contDiffOn (fineStableCurve_contDiffOn k χ ε δ hδ hq (tangentReversal w) hw)
lemma fineUnstableCurve_asymptotic (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    Tendsto (fun n : ℕ => dist ((inverseMap k)^[n] (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw s)))
      ((inverseMap k)^[n] (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw t)))) atTop (𝓝 0) := by
  have hq0 : 0≤Real.exp (-χ+ε)+δ := by positivity
  have hc := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (6*fineScale k ε δ)).mul_const |s-t|
  simp only [mul_zero,zero_mul] at hc
  simpa only [complexProjection_inverse_iterate] using squeeze_zero (fun _ => dist_nonneg)
    (fun n => (complexProjection_dist_le _ _).trans (fineUnstableCurve_contraction k χ ε δ hδ hq w hw hs ht n)) hc

lemma fineUnstableCurve_birkhoff_eq (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (g : C(Torus,ℝ)) {a b : ℝ}
    (ha : Tendsto (fun n : ℕ => birkhoffSum (inverseMap k) g n
      (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw s))/(n : ℝ)) atTop (𝓝 a))
    (hb : Tendsto (fun n : ℕ => birkhoffSum (inverseMap k) g n
      (complexProjection (fineUnstableCurve k χ ε δ hδ hq w hw t))/(n : ℝ)) atTop (𝓝 b)) : a=b :=
  birkhoff_limit_eq_of_asymptotic (CompactSpace.uniformContinuous_of_continuous g.continuous)
    (fineUnstableCurve_asymptotic k χ ε δ hδ hq w hw hs ht) ha hb

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology

lemma ae_unstableVector_reversal_stable (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area,0<standardLyapunov k hk z →
      wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0 := by
  filter_upwards [measurePreserving_standardReversal.quasiMeasurePreserving.ae
    (ae_stableVector_reversal_unstable k hk),standardLyapunov_reversal_ae k hk] with z hz he hp
  simpa only [standardReversal_involutive] using hz (by rwa [he])

lemma fineSize_eq_delta_mul (k χ ε δ : ℝ) (z : Torus) :
    fineSize k χ ε δ z=δ*fineSize k χ ε 1 z := by
  unfold fineSize fineScale
  ring

lemma fineFrame_eq_delta_smul (k χ ε δ : ℝ) (z : Torus) (p : RealPlane) :
    fineFrame k χ ε δ z p=δ•fineFrame k χ ε 1 z p := by
  simp only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,
    fineSize_eq_delta_mul k χ ε δ z,smul_smul]

lemma fineInverse_eq_inv_delta_smul (k χ ε δ : ℝ) (z : Torus) (p : ℂ) :
    fineInverse k χ ε δ z p=δ⁻¹•fineInverse k χ ε 1 z p := by
  simp only [fineInverse,flatInverse,ContinuousLinearMap.comp_apply,smul_apply,
    fineSize_eq_delta_mul k χ ε δ z,mul_inv_rev,map_smul,smul_smul]
  congr 1
  ring

lemma fine_relative_frame_independent_delta (k χ ε : ℝ) {δ : ℝ} (hδ : δ≠0)
    (z z' : Torus) (T : ℂ →L[ℝ] ℂ) (p : RealPlane) :
    fineInverse k χ ε δ z (T (fineFrame k χ ε δ z' p))=
      fineInverse k χ ε 1 z (T (fineFrame k χ ε 1 z' p)) := by
  rw [fineFrame_eq_delta_smul,map_smul,map_smul,fineInverse_eq_inv_delta_smul,smul_smul,mul_inv_cancel₀ hδ,one_smul]

lemma tangentReversal_wedge (s u : ℂ) : wedge (tangentReversal s) (tangentReversal u)=-wedge s u := by
  simp only [wedge,tangentReversal_re,tangentReversal_im]
  ring

lemma fineFrame_first (k χ ε δ : ℝ) (z : Torus) :
    fineFrame k χ ε δ z (1,0)=(fineSize k χ ε δ z/(2*stableScale k χ z))•stableVector k z := by
  simp only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,
    lyapunovFrame,planeFrame_apply,pairToComplex_apply,
    zero_div,zero_smul,add_zero,smul_smul]
  congr 1
  ring

lemma fineFrame_second (k χ ε δ : ℝ) (z : Torus) :
    fineFrame k χ ε δ z (0,1)=(fineSize k χ ε δ z/(2*unstableScale k χ z))•unstableVector k z := by
  simp only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,
    lyapunovFrame,planeFrame_apply,pairToComplex_apply,
    zero_div,zero_smul,zero_add,smul_smul]
  congr 1
  ring

lemma fineInverse_first_zero (k χ ε δ : ℝ) (z : Torus) {p : ℂ}
    (hp : wedge p (unstableVector k z)=0) : (fineInverse k χ ε δ z p).1=0 := by
  simp [fineInverse,flatInverse,lyapunovCoframe,planeCoframe_apply,hp]

lemma fineInverse_second_zero (k χ ε δ : ℝ) (z : Torus) {p : ℂ}
    (hp : wedge (stableVector k z) p=0) : (fineInverse k χ ε δ z p).2=0 := by
  simp [fineInverse,flatInverse,lyapunovCoframe,planeCoframe_apply,hp]

theorem fine_reversal_frame_swap (k χ ε : ℝ) (z : Torus)
    (hr : wedge (stableVector k z) (unstableVector k z)≠0)
    (hr' : wedge (stableVector k (standardReversal z)) (unstableVector k (standardReversal z))≠0)
    (hline : wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0)
    (hline' : wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0) :
    ∃ α β : ℝ,α≠0 ∧ β≠0 ∧ ∀ δ : ℝ,δ≠0 → ∀ p : RealPlane,
      fineInverse k χ ε δ z (tangentReversal (fineFrame k χ ε δ (standardReversal z) p))=(β*p.2,α*p.1) := by
  let M := (fineInverse k χ ε 1 z).comp (tangentReversal.comp (fineFrame k χ ε 1 (standardReversal z)))
  have hfirst : (M (1,0)).1=0 := by
    apply fineInverse_first_zero
    change wedge (tangentReversal (fineFrame k χ ε 1 (standardReversal z) (1,0))) (unstableVector k z)=0
    rw [fineFrame_first,map_smul,wedge_smul_left]
    have h : wedge (tangentReversal (stableVector k (standardReversal z))) (unstableVector k z)=0 := by
      rw [wedge_swap,hline,neg_zero]
    rw [h,mul_zero]
  have hsecond : (M (0,1)).2=0 := by
    apply fineInverse_second_zero
    change wedge (stableVector k z) (tangentReversal (fineFrame k χ ε 1 (standardReversal z) (0,1)))=0
    rw [fineFrame_second,map_smul,wedge_smul_right]
    have h := tangentReversal_wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))
    rw [tangentReversal_involutive,hline',neg_zero] at h
    rw [wedge_swap,h,neg_zero,mul_zero]
  have hi : Function.Injective M := by
    intro p q hpq
    have h := congrArg (fun v => fineInverse k χ ε 1 (standardReversal z)
      (tangentReversal (fineFrame k χ ε 1 z v))) hpq
    simpa only [M,ContinuousLinearMap.comp_apply,
      fineFrame_inverse k χ ε (by norm_num : (0 : ℝ)<1) z hr,tangentReversal_involutive,
      fineInverse_frame k χ ε (by norm_num : (0 : ℝ)<1) (standardReversal z) hr'] using h
  let α := (M (1,0)).2
  let β := (M (0,1)).1
  have hα : α≠0 := by
    intro he
    have hz : M (1,0)=M 0 := by rw [map_zero]; exact Prod.ext hfirst he
    have h := hi hz
    norm_num at h
  have hβ : β≠0 := by
    intro he
    have hz : M (0,1)=M 0 := by rw [map_zero]; exact Prod.ext he hsecond
    have h := hi hz
    norm_num at h
  refine ⟨α,β,hα,hβ,?_⟩
  intro δ hδ p
  rw [fine_relative_frame_independent_delta k χ ε hδ]
  change M p=(_,_)
  have hp : p=p.1•((1,0) : RealPlane)+p.2•((0,1) : RealPlane) := by ext <;> simp
  rw [hp,map_add,map_smul,map_smul]
  apply Prod.ext <;> simp [hfirst,hsecond,α,β,mul_comm]

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

theorem compact_reversible_fineRegular_block (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε)
    {r : ℝ≥0∞} (hr : r<area (spectralGapRegion k hk χ)) :
    ∃ K : Set Torus, K⊆spectralGapRegion k hk χ ∧ IsCompact K ∧ r<area K ∧
      ContinuousOn (fun z => (orbitChartData k χ ε z,orbitChartData k χ ε (standardReversal z))) K ∧
      ∀ z∈K,
        (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] z) ∧
          FineRegular k χ ε ((inverseMap k)^[n] z)) ∧
        (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] (standardReversal z)) ∧
          FineRegular k χ ε ((inverseMap k)^[n] (standardReversal z))) ∧
        wedge (stableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 ∧
        wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0 ∧
        wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0 := by
  let μ := area.restrict (spectralGapRegion k hk χ)
  have hrev := (measurePreserving_reversal_spectralGapRegion k hk χ).quasiMeasurePreserving.ae
    (ae_fineRegular_all_iterates k hk hχ hε)
  have htrans := ae_restrict_of_ae (μ := area) (s := spectralGapRegion k hk χ) (ae_reversal_tangent_transverse k hk)
  have hline := ae_restrict_of_ae (μ := area) (s := spectralGapRegion k hk χ) (ae_stableVector_reversal_unstable k hk)
  have hlineR := ae_restrict_of_ae (μ := area) (s := spectralGapRegion k hk χ) (ae_unstableVector_reversal_stable k hk)
  have hg := measurableSet_spectralGapRegion k hk χ
  have hall : ∀ᵐ z ∂μ,
      (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] z) ∧ FineRegular k χ ε ((inverseMap k)^[n] z)) ∧
      (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] (standardReversal z)) ∧
        FineRegular k χ ε ((inverseMap k)^[n] (standardReversal z))) ∧
      wedge (stableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 ∧
      wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0 ∧
        wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0 := by
    filter_upwards [ae_fineRegular_all_iterates k hk hχ hε,hrev,htrans,hline,hlineR,ae_restrict_mem hg] with z hz hr ht hl hlR hzg
    have hp : 0<standardLyapunov k hk z := hχ.trans hzg
    exact ⟨hz,hr,ht hp,hl hp,hlR hp⟩
  obtain ⟨B,hBae,hB,hBG⟩ := IsMeasurablyGenerated.exists_measurable_subset hall
  have hfull : (B∩spectralGapRegion k hk χ : Set Torus) =ᵐ[area] spectralGapRegion k hk χ := by
    filter_upwards [(ae_restrict_iff' hg).mp hBae] with z hz
    apply propext
    exact ⟨And.right,fun h => ⟨hz h,h⟩⟩
  have hm : area (B∩spectralGapRegion k hk χ)=area (spectralGapRegion k hk χ) := measure_congr hfull
  let : PolishSpace LyapunovChartData := inferInstance
  let : PolishSpace (LyapunovChartData × LyapunovChartData) := by constructor
  let : TopologicalSpace.IsCompletelyMetrizableSpace (ℕ → LyapunovChartData × LyapunovChartData) :=
    @TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable ℕ _
      (fun _ => LyapunovChartData × LyapunovChartData) _ (fun _ => inferInstance)
  let : PolishSpace (ℕ → LyapunovChartData × LyapunovChartData) := { toSecondCountableTopology := inferInstance, toIsCompletelyMetrizableSpace := inferInstance }
  let : SecondCountableTopology (ℕ → LyapunovChartData × LyapunovChartData) := inferInstance
  let : PolishSpace ((ℕ → LyapunovChartData × LyapunovChartData) × (ℕ → LyapunovChartData × LyapunovChartData)) :=
    { toSecondCountableTopology := inferInstance, toIsCompletelyMetrizableSpace := inferInstance }
  let : BorelSpace LyapunovChartData := inferInstance
  let : BorelSpace (LyapunovChartData × LyapunovChartData) := inferInstance
  let : BorelSpace (ℕ → LyapunovChartData × LyapunovChartData) := inferInstance
  let : BorelSpace ((ℕ → LyapunovChartData × LyapunovChartData) × (ℕ → LyapunovChartData × LyapunovChartData)) := inferInstance
  have hdata : Measurable (fun z => (orbitChartData k χ ε z,orbitChartData k χ ε (standardReversal z))) :=
    (measurable_orbitChartData k χ ε).prodMk ((measurable_orbitChartData k χ ε).comp measurePreserving_standardReversal.measurable)
  obtain ⟨K,hKA,hK,hcont,hKr⟩ := measurable_compact_continuity_block area hdata (hB.inter hg)
    (r := r) (by rwa [hm])
  exact ⟨K,fun z hz => (hKA hz).2,hK,hKr,hcont,fun z hz => hBG (hKA hz).1⟩

theorem compact_lift_reversible_block (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ C : Set ℂ, IsCompact C ∧ 0<volume C ∧
      (∀ v∈C,complexProjection v∈spectralGapRegion k hk χ) ∧
      ContinuousOn (fun v => (orbitChartData k χ ε (complexProjection v),
        orbitChartData k χ ε (complexProjection (tangentReversal v)))) C ∧
      ∀ v∈C,
        (∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)) ∧
          FineRegular k χ ε (complexProjection ((standardInverseLift k)^[n] v))) ∧
        (∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal v))) ∧
          FineRegular k χ ε (complexProjection ((standardInverseLift k)^[n] (tangentReversal v)))) ∧
        wedge (stableVector k (complexProjection v))
          (tangentReversal (stableVector k (complexProjection (tangentReversal v))))≠0 ∧
        wedge (unstableVector k (complexProjection v))
          (tangentReversal (stableVector k (complexProjection (tangentReversal v))))=0 ∧
        wedge (unstableVector k (complexProjection (tangentReversal v)))
          (tangentReversal (stableVector k (complexProjection v)))=0 := by
  obtain ⟨K,hKG,hK,hKpos,hdata,hreg⟩ := compact_reversible_fineRegular_block k hk hχ hε hgap
  let C : Set ℂ := complexProjection ⁻¹' K ∩ Metric.closedBall 0 2
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) 2).inter_left
    (hK.isClosed.preimage continuous_complexProjection)
  have hKC : area K≤volume C := area_le_volume_of_complexRep_subset hK.measurableSet (by
    intro z hz
    exact ⟨by simpa only [mem_preimage,complexProjection_complexRep] using hz,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using complexRep_norm_le_two z⟩)
  refine ⟨C,hC,hKpos.trans_le hKC,fun v hv => hKG hv.1,?_,?_⟩
  · simpa only [complexProjection_tangentReversal,Function.comp_def] using
      hdata.comp continuous_complexProjection.continuousOn (fun _ hv => hv.1)
  · intro v hv
    have h := hreg (complexProjection v) hv.1
    simpa only [complexProjection_iterate,complexProjection_inverse_iterate,complexProjection_tangentReversal] using h

end StandardMapEntropy

end
end

end OAI
