import OAI.Analysis.DiskMaximal.Localization

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SobolevBand
open WeakSobolev DiskMaximalTools DiskMoments

lemma high_dyadic (n : ℕ) : high n=2*((2:ℝ)^(2*n)*low n) := by
  have he : 2*n=n+n := by omega
  rw [high,low,he,pow_add]
  field_simp

lemma small_dyadic {L n : ℕ} (hn : L≤n) : 2*low L=2*((2:ℝ)^(n-L)*low n) := by
  have hp : (2:ℝ)^n=2^(n-L)*2^L := by rw [← pow_add,Nat.sub_add_cancel hn]
  rw [low,low,hp]
  field_simp

lemma small_le_high (L n : ℕ) : 2*low L≤high n := by
  have hl : low L≤1 := (inv_le_one₀ (by positivity : (0:ℝ)<2^L)).mpr (one_le_pow₀ (by norm_num))
  have hh : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  unfold high
  nlinarith

lemma gradient_error_restrict {u : ℕ → ℂ → ℝ} {g : ℂ → ℂ}
    (hu : ∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) (hg : Integrable g)
    (ht : Tendsto (fun n => ∫ x, ‖gradient (u n) x-g x‖) atTop (𝓝 0)) (S : Set ℂ) :
    Tendsto (fun n => ∫ x in S, ‖gradient (u n) x‖) atTop (𝓝 (∫ x in S, ‖g x‖)) := by
  have hi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  apply integral_norm_converges hg.integrableOn (fun n => (hi n).integrableOn)
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ ht
  intro n
  exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun x => norm_nonneg _)) ((hi n).sub hg).norm

lemma exists_diagonal_smooth {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hw : HasGradient (μ := volume) f g) :
    ∃ u : ℕ → ℂ → ℝ, (∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) ∧
      (∀ n, (∫ x,‖gradient (u n) x‖) ≤ (∫ x,‖g x‖)+1) ∧
      Tendsto (fun n => ∫ x,‖gradient (u n) x-g x‖) atTop (𝓝 0) ∧
      (∀ n x, ‖band (u n) (low n) (high n) x-band f (low n) (high n) x‖ ≤ 1/((n:ℝ)+1)) := by
  have he (n : ℕ) : 0 < min (1/((n:ℝ)+1)) (Real.pi*(low n)^2/((n:ℝ)+1)) := by
    have := low_pos n
    apply lt_min <;> positivity
  choose u hu hc he1 he2 using fun n => exists_smooth_compact_approx hf hg hw (he n)
  have hi (n) : Integrable (u n) := (hu n).continuous.integrable_of_hasCompactSupport (hc n)
  have h1 n : ContDiff ℝ 1 (u n) := (hu n).of_le (by simp)
  refine ⟨u,fun n => ⟨h1 n,hc n⟩,?_,?_,?_⟩
  · intro n
    apply (gradient_integral_le (h1 n) (hc n) hg).trans
    gcongr
    have hn : 1/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ((he2 n).le.trans (min_le_left _ _)).trans hn
  · apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => (he2 n).le.trans (min_le_left _ _))
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n x
    rw [Real.norm_eq_abs]
    apply (band_sub_le (hi n) hf (low_pos n) (low_le_high n) x).trans
    have := low_pos n
    apply (div_le_iff₀ (by positivity : 0<Real.pi*(low n)^2)).mpr
    have h := (he1 n).le.trans (min_le_right _ _)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using h

lemma smooth_diagonal_local_L1 {f : ℂ → ℝ} {g : ℂ → ℂ} {u : ℕ → ℂ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hw : HasGradient (μ := volume) f g)
    (hu : ∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n))
    (he : ∀ n x, ‖band (u n) (low n) (high n) x-band (fun y => |f y|) (low n) (high n) x‖ ≤ 1/((n:ℝ)+1))
    {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => ∫ x in K, ‖band (u n) (low n) (high n) x-maximalComplexReal f x‖) atTop (𝓝 0) := by
  let H := fun n => band (u n) (low n) (high n)
  let A := fun n => band (fun y => |f y|) (low n) (high n)
  have hUi n : Integrable (u n) := (hu n).1.continuous.integrable_of_hasCompactSupport (hu n).2
  have hGi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hH n : Continuous (H n) := (band_lipschitz (hUi n) (hGi n) (contDiff_hasGradient (hu n).1) (low_pos n) (low_le_high n)).continuous
  have hA n : Continuous (A n) := (band_lipschitz hf.abs (abs_gradient_bound hf hg).1 (hw.abs hf hg) (low_pos n) (low_le_high n)).continuous
  have hM := (locallyIntegrable_maximal hf hg hw).integrableOn_isCompact hK
  have hHi n : IntegrableOn (H n) K := (hH n).continuousOn.integrableOn_compact hK
  have hAi n : IntegrableOn (A n) K := (hA n).continuousOn.integrableOn_compact hK
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hb (n : ℕ) : (∫ x in K, ‖H n x-maximalComplexReal f x‖) ≤
      (1/((n:ℝ)+1))*volume.real K+(∫ x in K,‖A n x-maximalComplexReal f x‖) := by
    have hcst : (∫ _ : ℂ in K,(1/((n:ℝ)+1)))=(1/((n:ℝ)+1))*volume.real K := by simp only [setIntegral_const,smul_eq_mul,mul_comm]
    have hdiff : IntegrableOn (fun x => ‖A n x-maximalComplexReal f x‖) K := ((hAi n).sub hM).norm
    have hconst : IntegrableOn (fun _ : ℂ => (1/((n:ℝ)+1))) K := integrable_const _
    rw [← hcst,← integral_add hconst hdiff]
    apply integral_mono ((hHi n).sub hM).norm ((integrable_const _).add ((hAi n).sub hM).norm)
    intro x
    change ‖H n x-maximalComplexReal f x‖ ≤ 1/((n:ℝ)+1)+‖A n x-maximalComplexReal f x‖
    exact (norm_sub_le_norm_sub_add_norm_sub (H n x) (A n x) (maximalComplexReal f x)).trans (add_le_add (he n x) le_rfl)
  have hlim : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))*volume.real K+(∫ x in K,‖A n x-maximalComplexReal f x‖)) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_add] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (volume.real K)).add (diagonal_local_L1 hf hg hw hK)
  exact squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hb hlim
end SobolevBand

namespace WeakCompact
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {μ : Measure X}
lemma densityLimit_compact_bound_limit (w : ℕ → X → ℝ) (hw : ∀ n, Integrable (w n) μ)
    (h0 : ∀ n, ∀ᵐ x ∂μ,0≤w n x) {B : ℝ} (hb : ∀ n,(∫ x,w n x ∂μ)≤B)
    {D : ℝ} {a : ℕ → ℝ} {K O : Set X} (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (ha : ∀ᶠ n in atTop,(∫ x in O,w n x ∂μ)≤a n) (ht : Tendsto a atTop (𝓝 D)) :
    densityLimit w hw h0 hb K ≤ ENNReal.ofReal D := by
  have he (ε : ℝ) (hε : 0<ε) : densityLimit w hw h0 hb K ≤ ENNReal.ofReal (D+ε) := by
    apply densityLimit_compact_bound w hw h0 hb hK hO hKO
    filter_upwards [ha,ht.eventually (gt_mem_nhds (by linarith : D<D+ε))] with n hn hn'
    exact hn.trans hn'.le
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x := densityLimit w hw h0 hb K))
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (show Tendsto (fun n : ℕ => D+1/((n:ℝ)+1)) atTop (𝓝 D) by
        simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  exact Eventually.of_forall (fun n => he _ (by positivity))
end WeakCompact

namespace NullLocalization
open SobolevBand DiskMoments PhysicalCells

lemma thickening_null_integral {K : Set ℂ} (hK : IsCompact K) (hK0 : volume K=0)
    {G : ℂ → ℝ} (hG : Integrable G) :
    Tendsto (fun L => ∫ x in Metric.thickening (12*(2*low L)) K,G x) atTop (𝓝 0) := by
  let s := fun L => Metric.thickening (12*(2*low L)) K
  have hm : Antitone s := fun i j hij => Metric.thickening_mono (by gcongr; exact low_antitone hij) K
  have he : (⋂ L,s L)=K := by
    apply subset_antisymm
    · intro x hx
      apply hK.isClosed.closure_eq ▸ (show x∈closure K from ?_)
      rw [Metric.mem_closure_iff]
      intro ε hε
      have ht : Tendsto (fun L => 12*(2*low L)) atTop (𝓝 0) := by
        simpa only [mul_zero] using (low_tendsto.const_mul 2).const_mul 12
      obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds hε)).exists
      obtain ⟨y,hy,hxy⟩ := Metric.mem_thickening_iff.mp (mem_iInter.mp hx L)
      exact ⟨y,hy,hxy.trans hL⟩
    · exact subset_iInter (fun L => Metric.self_subset_thickening (by have := low_pos L; positivity) K)
  have ht := tendsto_setIntegral_of_antitone (fun L => Metric.isOpen_thickening.measurableSet) hm ⟨0,hG.integrableOn⟩
  rw [he,setIntegral_measure_zero _ hK0] at ht
  exact ht

lemma local_split_bound : ∃ C : ℝ, 0<C ∧ ∀ {u : ℕ → ℂ → ℝ},
    (∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) → ∀ (L : ℕ) {O K : Set ℂ},
    MeasurableSet O → volume O<⊤ → O⊆Metric.thickening (2*low L) K →
    ∀ᶠ n in atTop,
      (∫ x in O,‖gradient (band (u n) (low n) (high n)) x‖) ≤
      C*(∫ x in Metric.thickening (12*(2*low L)) K,‖gradient (u n) x‖)+
        ((∫ x,‖gradient (u n) x‖)/(Real.pi*(2*low L)^2))*volume.real O := by
  obtain ⟨C,hC,hlocal⟩ := smooth_small_local_budget
  refine ⟨C,hC,?_⟩
  intro u hu L O K hO hOf hOK
  have : IsFiniteMeasure (volume.restrict O) := ⟨by simpa using hOf⟩
  filter_upwards [eventually_ge_atTop L] with n hn
  have hat : low n≤2*low L := (low_antitone hn).trans (by have := low_pos L; linarith)
  have hfi := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)
  have hsi := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) hat
  have hcon : IntegrableOn (fun _ : ℂ => (∫ y,‖gradient (u n) y‖)/(Real.pi*(2*low L)^2)) O := integrable_const _
  have hb := integral_mono_ae (hfi.norm.integrableOn (s := O)) (hsi.norm.integrableOn.add hcon)
    (ae_restrict_of_ae (split_gradient (hu n).1 (hu n).2 (low_pos n) hat (small_le_high L n)))
  simp only [Pi.add_apply] at hb
  rw [integral_add hsi.norm.integrableOn hcon,setIntegral_const] at hb
  simp only [smul_eq_mul,mul_comm (volume.real O)] at hb
  apply hb.trans
  gcongr
  have hh := hlocal (hu n).1 (hu n).2 (low_pos n) (n-L) (K := K) hO
  rw [← small_dyadic hn] at hh
  exact hh hOK

lemma diagonal_density_limit_ac {u : ℕ → ℂ → ℝ} {g : ℂ → ℂ}
    (hu : ∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) (hg : Integrable g)
    (ht : Tendsto (fun n => ∫ x,‖gradient (u n) x-g x‖) atTop (𝓝 0))
    (w : ℕ → ℂ → ℝ) (hw : ∀ n, Integrable (w n)) (h0 : ∀ n,∀ᵐ x,0≤w n x)
    {B A : ℝ} (hb : ∀ n,(∫ x,w n x)≤B) (hA : 0≤A)
    (hdom : ∀ n,∀ᵐ x,w n x≤A*‖gradient (band (u n) (low n) (high n)) x‖) :
    WeakCompact.densityLimit w hw h0 hb ≪ volume := by
  have := WeakCompact.densityLimit_regular w hw h0 hb
  apply WeakCompact.absolutelyContinuous_of_compact_null
  intro K hK hK0
  obtain ⟨C,hC,hlocal⟩ := local_split_bound
  let ν := WeakCompact.densityLimit w hw h0 hb
  let V := ∫ x,‖g x‖
  have hi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hv := WeakSobolev.integral_norm_converges hg hi ht
  have hL (L : ℕ) : ν K≤ENNReal.ofReal (A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)) := by
    have he (ε : ℝ) (hε : 0<ε) : ν K≤ENNReal.ofReal
        (A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)+A*(V/(Real.pi*(2*low L)^2))*ε) := by
      obtain ⟨U,hKU,hU,hUf⟩ := K.exists_isOpen_lt_of_lt (μ := (volume : Measure ℂ)) (ENNReal.ofReal ε) (by simpa only [hK0] using ENNReal.ofReal_pos.mpr hε)
      let O := U∩Metric.thickening (2*low L) K
      have hO : IsOpen O := hU.inter Metric.isOpen_thickening
      have hKO : K⊆O := subset_inter hKU (Metric.self_subset_thickening (by have := low_pos L; positivity) K)
      have hOM : volume O≤ENNReal.ofReal ε := (measure_mono inter_subset_left).trans hUf.le
      have hOf : volume O<⊤ := hOM.trans_lt ENNReal.ofReal_lt_top
      have hOB : volume.real O≤ε := by
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hOM).trans_eq (ENNReal.toReal_ofReal hε.le)
      have hgi n : Integrable (fun x => ‖gradient (band (u n) (low n) (high n)) x‖) :=
        (smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)).norm
      have hd n : (∫ x in O,w n x)≤A*(∫ x in O,‖gradient (band (u n) (low n) (high n)) x‖) := by
        rw [← integral_const_mul]
        exact integral_mono_ae (hw n).integrableOn ((hgi n).integrableOn.const_mul A) (ae_restrict_of_ae (hdom n))
      have hh : ν K≤ENNReal.ofReal (A*(C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)+(V/(Real.pi*(2*low L)^2))*volume.real O)) := by
        apply WeakCompact.densityLimit_compact_bound_limit w hw h0 hb hK hO hKO
          (a := fun n => A*(C*(∫ x in Metric.thickening (12*(2*low L)) K,‖gradient (u n) x‖)+((∫ x,‖gradient (u n) x‖)/(Real.pi*(2*low L)^2))*volume.real O))
        · filter_upwards [hlocal hu L hO.measurableSet hOf inter_subset_right] with n hn
          exact (hd n).trans (mul_le_mul_of_nonneg_left hn hA)
        · exact ((gradient_error_restrict hu hg ht _).const_mul C |>.add ((hv.div_const _).mul_const _)).const_mul A
      apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
      have hv0 : 0≤V := integral_nonneg (fun x => norm_nonneg (g x))
      have hcoef : 0≤A*(V/(Real.pi*(2*low L)^2)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hOB hcoef]
    apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x := ν K))
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (show Tendsto (fun n : ℕ => A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)+A*(V/(Real.pi*(2*low L)^2))*(1/((n:ℝ)+1))) atTop
          (𝓝 (A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖))) by
          simpa only [mul_zero,add_zero] using tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _)))
    exact Eventually.of_forall (fun n => he _ (by positivity))
  apply le_antisymm _ bot_le
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((thickening_null_integral hK hK0 hg.norm).const_mul (A*C))
  have hb' := le_of_tendsto_of_tendsto (tendsto_const_nhds (x := ν K)) ht' (Eventually.of_forall hL)
  change ν K ≤ 0
  simpa only [mul_zero,ENNReal.ofReal_zero] using hb'
end NullLocalization

namespace WeakCompact
open CompactlySupported CompactlySupportedContinuousMap

lemma densityLimit_rn (w : ℕ → ℂ → ℝ) (hw : ∀ n,Integrable (w n))
    (h0 : ∀ n,∀ᵐ x,0≤w n x) {B D : ℝ} (hb : ∀ n,(∫ x,w n x)≤B) (hB : 0≤B)
    (hac : densityLimit w hw h0 hb ≪ volume)
    (hm : densityLimit w hw h0 hb univ≤ENNReal.ofReal D) (hD : 0≤D) :
    ∃ d : ℂ → ℝ, Integrable d ∧ (∀ x,0≤d x) ∧ (∫ x,d x)≤D ∧
      ∀ φ : C_c(ℂ,ℝ), Tendsto (fun n => ∫ x,w n x*φ x) (hyperfilter ℕ) (𝓝 (∫ x,d x*φ x)) := by
  let ν := densityLimit w hw h0 hb
  have : IsFiniteMeasure ν := densityLimit_finite w hw h0 hb hB
  let d := fun x => (ν.rnDeriv volume x).toReal
  have hi : Integrable d := by
    have h := Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := volume) (s := univ) (measure_ne_top ν univ)
    simpa only [integrableOn_univ] using h
  refine ⟨d,hi,fun x => ENNReal.toReal_nonneg,?_,?_⟩
  · rw [show (∫ x,d x)=ν.real univ from Measure.integral_toReal_rnDeriv hac]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hm).trans_eq (ENNReal.toReal_ofReal hD)
  · intro φ
    rw [show (∫ x,d x*φ x)=(∫ x,φ x ∂ν) from integral_toReal_rnDeriv_mul hac]
    exact densityLimit_integral w hw h0 hb φ
end WeakCompact

namespace WeakSobolev
lemma local_L1_test_converges {F : ℂ → ℝ} {u : ℕ → ℂ → ℝ}
    (hF : LocallyIntegrable F) (hu : ∀ n,LocallyIntegrable (u n))
    (ht : ∀ K : Set ℂ, IsCompact K → Tendsto (fun n => ∫ x in K,‖u n x-F x‖) atTop (𝓝 0))
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x,u n x*φ x) atTop (𝓝 (∫ x,F x*φ x)) := by
  let K := tsupport φ
  have hK : IsCompact K := hc
  have hFm : IntegrableOn F K := hF.integrableOn_isCompact hK
  have hum n : IntegrableOn (u n) K := (hu n).integrableOn_isCompact hK
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hφ
  have hlim := bounded_smul_converges hFm hum (ht K hK) hφ.aestronglyMeasurable.restrict (ae_of_all _ hB)
  have hi n : IntegrableOn (fun x => φ x*u n x) K := (hum n).bdd_smul B hφ.aestronglyMeasurable.restrict (ae_of_all _ hB)
  have hf : IntegrableOn (fun x => φ x*F x) K := hFm.bdd_smul B hφ.aestronglyMeasurable.restrict (ae_of_all _ hB)
  have hh := integral_converges_norm hf hi hlim
  have he (v : ℂ → ℝ) : (∫ x in K,φ x*v x)=(∫ x,v x*φ x) := by
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      by_cases hx : x∈K
      · rw [indicator_of_mem hx,mul_comm]
      · rw [indicator_of_notMem hx]
        simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero])
  simpa only [he,smul_eq_mul] using hh
end WeakSobolev

namespace SobolevBand
open WeakSobolev WeakCompact CompactlySupported CompactlySupportedContinuousMap DiskMoments

/-- Positive directional densities share a single ultrafilter, so their differences
retain the distributional identities. Absolute continuity is proved by local
small-radius cutoff estimates, rather than assumed as a BV compactness upgrade. -/
lemma positive_direction_limit : ∃ C : ℝ, 0<C ∧
    ∀ {u : ℕ → ℂ → ℝ} {g : ℂ → ℂ},
    (∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) → Integrable g →
    (∀ n, (∫ x,‖gradient (u n) x‖)≤(∫ x,‖g x‖)+1) →
    Tendsto (fun n => ∫ x,‖gradient (u n) x-g x‖) atTop (𝓝 0) →
    ∀ v : ℂ, ‖v‖≤1 → ∃ d : ℂ → ℝ, Integrable d ∧ (∀ x,0≤d x) ∧
      (∫ x,d x)≤2*C*(∫ x,‖g x‖) ∧
      ∀ φ : C_c(ℂ,ℝ), Tendsto
        (fun n => ∫ x,(‖gradient (band (u n) (low n) (high n)) x‖+
          ⟪gradient (band (u n) (low n) (high n)) x,v⟫)*φ x)
        (hyperfilter ℕ) (𝓝 (∫ x,d x*φ x)) := by
  obtain ⟨C,hC,hbound⟩ := smooth_dyadic_bound
  refine ⟨C,hC,?_⟩
  intro u g hu hg hV ht v hv
  let q := fun n => gradient (band (u n) (low n) (high n))
  let w := fun n x => ‖q n x‖+⟪q n x,v⟫
  let V := ∫ x,‖g x‖
  have hV0 : 0≤V := integral_nonneg (fun x => norm_nonneg _)
  have hqi n : Integrable (q n) := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)
  have hwi n : Integrable (w n) := (hqi n).norm.add ((hqi n).inner_const (𝕜 := ℝ) v)
  have hinner n x : |⟪q n x,v⟫|≤‖q n x‖ :=
    (abs_real_inner_le_norm (q n x) v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)
  have hw0 n : ∀ᵐ x,0≤w n x := ae_of_all _ (fun x => by
    dsimp only [w]
    have := (abs_le.mp (hinner n x)).1
    linarith)
  have hdom n : ∀ᵐ x,w n x≤2*‖q n x‖ := ae_of_all _ (fun x => by
    dsimp only [w]
    have := (abs_le.mp (hinner n x)).2
    linarith)
  have hmass n : (∫ x,w n x)≤2*C*(∫ x,‖gradient (u n) x‖) := by
    have h := hbound (hu n).1 (hu n).2 (low_pos n) (2*n)
    rw [← high_dyadic n] at h
    calc
      (∫ x,w n x) ≤ ∫ x,2*‖q n x‖ := integral_mono_ae (hwi n) ((hqi n).norm.const_mul 2) (hdom n)
      _ = 2*(∫ x,‖q n x‖) := integral_const_mul _ _
      _ ≤ 2*(C*(∫ x,‖gradient (u n) x‖)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hb n : (∫ x,w n x)≤2*C*(V+1) :=
    (hmass n).trans (mul_le_mul_of_nonneg_left (hV n) (by positivity))
  have hac := NullLocalization.diagonal_density_limit_ac hu hg ht w hwi hw0 hb (by norm_num : (0:ℝ)≤2) hdom
  have hi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hsharp := densityLimit_sharp_mass w hwi hw0 hb hmass
    ((integral_norm_converges hg hi ht).const_mul (2*C))
  exact densityLimit_rn w hwi hw0 hb (by positivity) hac hsharp (by positivity)
end SobolevBand

namespace WeakSobolev
open CompactlySupported CompactlySupportedContinuousMap

lemma direction_identity_limit {F : ℂ → ℝ} {H : ℕ → ℂ → ℝ} {q : ℕ → ℂ → ℂ}
    (hF : LocallyIntegrable F) (hH : ∀ n, LocallyIntegrable (H n))
    (hqi : ∀ n, Integrable (q n)) (hw : ∀ n, HasGradient (μ := volume) (H n) (q n))
    (ht : ∀ K : Set ℂ, IsCompact K → Tendsto (fun n => ∫ x in K,‖H n x-F x‖) atTop (𝓝 0))
    {d e : ℂ → ℝ} (hd : Integrable d) (he : Integrable e) (v : ℂ)
    (hv : ∀ φ : C_c(ℂ,ℝ), Tendsto (fun n => ∫ x,(‖q n x‖+⟪q n x,v⟫)*φ x)
      (hyperfilter ℕ) (𝓝 (∫ x,d x*φ x)))
    (h0 : ∀ φ : C_c(ℂ,ℝ), Tendsto (fun n => ∫ x,(‖q n x‖+⟪q n x,(0:ℂ)⟫)*φ x)
      (hyperfilter ℕ) (𝓝 (∫ x,e x*φ x))) :
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,F x*fderiv ℝ φ x v) = -∫ x,(d x-e x)*φ x := by
  intro φ hφ hc
  let φ' : C_c(ℂ,ℝ) := ⟨⟨φ,hφ.continuous⟩,hc⟩
  have hn n : Integrable (fun x => ‖q n x‖*φ x) :=
    (hqi n).norm.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hp n : Integrable (fun x => (‖q n x‖+⟪q n x,v⟫)*φ x) :=
    ((hqi n).norm.add ((hqi n).inner_const (𝕜 := ℝ) v)).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hd' : Integrable (fun x => d x*φ x) := hd.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have he' : Integrable (fun x => e x*φ x) := he.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hvn n : (∫ x,(‖q n x‖+⟪q n x,v⟫)*φ x)-(∫ x,(‖q n x‖+⟪q n x,(0:ℂ)⟫)*φ x) =
      ∫ x,⟪q n x,v⟫*φ x := by
    simp only [inner_zero_right,add_zero]
    rw [← integral_sub (hp n) (hn n)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have hde : (∫ x,d x*φ x)-(∫ x,e x*φ x) = ∫ x,(d x-e x)*φ x := by
    rw [← integral_sub hd' he']
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have hlim : Tendsto (fun n => ∫ x,H n x*fderiv ℝ φ x v) (hyperfilter ℕ)
      (𝓝 (-∫ x,(d x-e x)*φ x)) := by
    have h := ((hv φ').sub (h0 φ')).neg
    change Tendsto (fun n => -((∫ x,(‖q n x‖+⟪q n x,v⟫)*φ x)-(∫ x,(‖q n x‖+⟪q n x,(0:ℂ)⟫)*φ x)))
      (hyperfilter ℕ) (𝓝 (-((∫ x,d x*φ x)-(∫ x,e x*φ x)))) at h
    simp only [hvn,hde,← hw _ φ hφ hc v] at h
    exact h
  exact tendsto_nhds_unique
    ((local_L1_test_converges hF hH ht ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ v)).mono_left Nat.hyperfilter_le_atTop) hlim

lemma complex_inner_one (z : ℂ) : ⟪z,(1:ℂ)⟫=(z.re:ℝ) := by
  simp [real_inner_eq_re_inner, RCLike.inner_apply]
lemma complex_inner_I (z : ℂ) : ⟪z,Complex.I⟫=(z.im:ℝ) := by
  simp [real_inner_eq_re_inner, RCLike.inner_apply]

lemma complex_hasGradient_of_coordinates {F : ℂ → ℝ} {G : ℂ → ℂ}
    (hF : LocallyIntegrable F) (hG : Integrable G)
    (h1 : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,F x*fderiv ℝ φ x 1) = -∫ x,(G x).re*φ x)
    (hI : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,F x*fderiv ℝ φ x Complex.I) = -∫ x,(G x).im*φ x) :
    HasGradient (μ := volume) F G := by
  intro φ hφ hc v
  have hv : v=v.re • (1:ℂ)+v.im • Complex.I := by simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  have hh w : Integrable (fun x => F x*fderiv ℝ φ x w) :=
    hF.integrable_smul_right_of_hasCompactSupport ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ w)
  have hg1 : Integrable (fun x => (G x).re*φ x) :=
    (hG.inner_const (𝕜 := ℝ) (1:ℂ)).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc |>.congr (ae_of_all _ (fun x => by simp only [complex_inner_one,smul_eq_mul]))
  have hgI : Integrable (fun x => (G x).im*φ x) :=
    (hG.inner_const (𝕜 := ℝ) Complex.I).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc |>.congr (ae_of_all _ (fun x => by simp only [complex_inner_I,smul_eq_mul]))
  have hfder x : F x*fderiv ℝ φ x v=v.re*(F x*fderiv ℝ φ x 1)+v.im*(F x*fderiv ℝ φ x Complex.I) := by
    conv_lhs => rw [hv]
    simp only [map_add,map_smul,smul_eq_mul]
    ring
  have hinner x : ⟪G x,v⟫*φ x=v.re*((G x).re*φ x)+v.im*((G x).im*φ x) := by
    conv_lhs => rw [hv]
    rw [inner_add_right,real_inner_smul_right,real_inner_smul_right,complex_inner_one,complex_inner_I]
    ring
  simp_rw [hfder,hinner]
  rw [integral_add ((hh 1).const_mul _) ((hh Complex.I).const_mul _),
    integral_add (hg1.const_mul _) (hgI.const_mul _)]
  simp only [integral_const_mul,h1 φ hφ hc,hI φ hφ hc]
  ring
end WeakSobolev

namespace SobolevBand
open WeakSobolev DiskMaximalTools DiskMoments

/-- The all-radius absolute endpoint on the isometric complex model of the plane.
No smoothness, sign, compact support, or boundedness remains on the input. -/
lemma complex_endpoint : ∃ C : ℝ, 0<C ∧ ∀ (f : ℂ → ℝ) (g : ℂ → ℂ),
    Integrable f → Integrable g → HasGradient (μ := volume) f g →
    LocallyIntegrable (maximalComplexReal f) ∧ ∃ G : ℂ → ℂ,
      Integrable G ∧ HasGradient (μ := volume) (maximalComplexReal f) G ∧
        (∫ x,‖G x‖)≤C*(∫ x,‖g x‖) := by
  obtain ⟨C,hC,hlim⟩ := positive_direction_limit
  refine ⟨8*C,by positivity,?_⟩
  intro f g hf hg hw
  let a := fun x => absCoefficient (f x) • g x
  have ha : Integrable a := (abs_gradient_bound hf hg).1
  obtain ⟨u,hu,hV,ht,he⟩ := exists_diagonal_smooth hf.abs ha (hw.abs hf hg)
  let H := fun n => band (u n) (low n) (high n)
  let q := fun n => gradient (H n)
  have hqi n : Integrable (q n) := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)
  have hH n : LocallyIntegrable (H n) := (smooth_band_lipschitz (hu n).1 (hu n).2 (low_pos n) (low_le_high n)).continuous.locallyIntegrable
  have hwH n : HasGradient (μ := volume) (H n) (q n) :=
    lipschitz_hasGradient (smooth_band_lipschitz (hu n).1 (hu n).2 (low_pos n) (low_le_high n))
  have hF := locallyIntegrable_maximal hf hg hw
  have htH (K : Set ℂ) (hK : IsCompact K) :
      Tendsto (fun n => ∫ x in K,‖H n x-maximalComplexReal f x‖) atTop (𝓝 0) :=
    smooth_diagonal_local_L1 hf hg hw hu he hK
  obtain ⟨d0,hd0,h0pos,h0mass,h0lim⟩ := hlim hu ha hV ht 0 (by simp)
  obtain ⟨d1,hd1,h1pos,h1mass,h1lim⟩ := hlim hu ha hV ht 1 (by simp)
  obtain ⟨dI,hdI,hIpos,hImass,hIlim⟩ := hlim hu ha hV ht Complex.I (by simp)
  let G := fun x => ((d1 x-d0 x : ℝ):ℂ)+((dI x-d0 x : ℝ):ℂ)*Complex.I
  have hG : Integrable G := ((hd1.sub hd0).ofReal).add (((hdI.sub hd0).ofReal).mul_const Complex.I)
  have hGre x : (G x).re=d1 x-d0 x := by simp [G]
  have hGim x : (G x).im=dI x-d0 x := by simp [G]
  refine ⟨hF,G,hG,?_,?_⟩
  · apply complex_hasGradient_of_coordinates hF hG
    · simpa only [hGre] using direction_identity_limit hF hH hqi hwH htH hd1 hd0 1 h1lim h0lim
    · simpa only [hGim] using direction_identity_limit hF hH hqi hwH htH hdI hd0 Complex.I hIlim h0lim
  · have hb x : ‖G x‖≤d1 x+dI x+2*d0 x := by
      have h := Complex.norm_le_abs_re_add_abs_im (G x)
      rw [hGre,hGim] at h
      have h1 : |d1 x-d0 x| ≤ d1 x+d0 x := by
        exact abs_le.mpr ⟨by linarith [h1pos x,h0pos x],by linarith [h1pos x,h0pos x]⟩
      have hI : |dI x-d0 x| ≤ dI x+d0 x := by
        exact abs_le.mpr ⟨by linarith [hIpos x,h0pos x],by linarith [hIpos x,h0pos x]⟩
      linarith
    have hi := integral_mono hG.norm ((hd1.add hdI).add (hd0.const_mul 2)) hb
    simp only [Pi.add_apply] at hi
    rw [integral_add (f := fun x => d1 x+dI x) (hd1.add hdI) (hd0.const_mul 2),integral_add hd1 hdI,integral_const_mul] at hi
    have hba : (∫ x,‖a x‖)≤∫ x,‖g x‖ := (abs_gradient_bound hf hg).2
    have hh : (∫ x,‖G x‖)≤8*C*(∫ x,‖a x‖) := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_left hba (by positivity))
end SobolevBand

namespace WeakSobolev
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

lemma HasGradient.comp_isometry {f : F → ℝ} {g : F → F}
    (hw : HasGradient (μ := volume) f g) (e : E ≃ₗᵢ[ℝ] F) :
    HasGradient (μ := volume) (fun x => f (e x)) (fun x => e.symm (g (e x))) := by
  intro φ hφ hc v
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
  have hd x : fderiv ℝ ψ (e x) (e v)=fderiv ℝ φ x v := by
    rw [fderiv_comp (e x) (hφ.differentiable (by simp) _) (e.symm.differentiableAt),e.symm.fderiv]
    change fderiv ℝ φ (e.symm (e x)) (e.symm (e v))=fderiv ℝ φ x v
    simp only [e.symm_apply_apply]
  have hi x : ⟪e.symm (g (e x)),v⟫=⟪g (e x),e v⟫ := by
    simpa only [e.apply_symm_apply] using (e.inner_map_map (e.symm (g (e x))) v).symm
  have h := hw ψ hψ hψc (e v)
  rw [← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => f y*fderiv ℝ ψ y (e v)),
    ← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => ⟪g y,e v⟫*ψ y)] at h
  simpa only [hd,← hi,ψ,Function.comp_apply,e.symm_apply_apply] using h
end WeakSobolev

end

end OAI
