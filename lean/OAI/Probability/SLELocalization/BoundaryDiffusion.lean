import Mathlib
import OAI.Probability.SLELocalization.SwallowingLaws
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Boundary Green estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing GreenPhysical

lemma deterministic_budget {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (κ β a : ℝ) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    (U : C(I, ℝ)) (x L : ℝ) (b : ℝ → ℝ) (hb : Continuous b)
    (hb0 : b 0=0) (hU : EqOn (extendDriver T U) (fun t => Real.sqrt κ*b t) (Icc 0 T)) :
    let τ := stop hε hT.le U x β a L
    let F := field hε hT.le β a (Real.sqrt κ) U x
    let V := drift hε hT.le β a (Real.sqrt κ) U x
    F τ (b τ) ≤
        (F τ (b τ)-F 0 (b 0)-(∫ t in (0:ℝ)..τ,V t (b t))-
          (1/2:ℝ)*∫ t in (0:ℝ)..τ,iteratedDeriv 2 (F t) (b t))+radial (-β) x ε := by
  dsimp only
  let τ := stop hε hT.le U x β a L
  let F := field hε hT.le β a (Real.sqrt κ) U x
  let V := drift hε hT.le β a (Real.sqrt κ) U x
  have htau := stop_bounds hε hT.le U x β a L
  have hmap : Continuous (fun t => ((U,t),b t)) := (continuous_const.prodMk continuous_id).prodMk hb
  have hV : Continuous (fun t => V t (b t)) := by
    have hh := (continuous_drift hε hT.le β a (Real.sqrt κ) x).comp hmap
    dsimp only [Function.comp_def] at hh
    exact hh
  have hQ : Continuous (fun t => iteratedDeriv 2 (F t) (b t)) := by
    have hh := (continuous_coeff hε hT.le β a (Real.sqrt κ) x 2 (Or.inr rfl)).comp hmap
    dsimp only [Function.comp_def] at hh
    exact hh
  have hneg : (∫ t in (0:ℝ)..τ, V t (b t)+(1/2:ℝ)*iteratedDeriv 2 (F t) (b t)) ≤ 0 := by
    have hh : (∫ t in (0:ℝ)..τ, V t (b t)+(1/2:ℝ)*iteratedDeriv 2 (F t) (b t)) ≤
        ∫ _t in (0:ℝ)..τ, (0:ℝ) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo htau.1
        ((hV.add (continuous_const.mul hQ)).intervalIntegrable _ _)
        (intervalIntegrable_const)
      intro t ht
      have hh := (deficit_pos_iff hε hT.le U x β a L t).1
        (positive_before hε hT.le hT U x β a L ht.1.le ht.2)
      change V t (b t)+(1/2:ℝ)*iteratedDeriv 2 (F t) (b t) ≤ 0
      have he := generator_field hε hT.le κ β a hκ U x t (b t) hh.1.le
        (hU ⟨ht.1.le,ht.2.le.trans htau.2⟩)
      change V t (b t)+(1/2:ℝ)*iteratedDeriv 2 (F t) (b t) = _ at he
      rw [he]
      exact mul_nonpos_of_nonneg_of_nonpos (factor_pos hε hT.le β a U x t).le
        (generator_nonpos hκ hβ ha hba (hε.trans hh.1) hε)
    simpa using hh
  have hhalf : IntervalIntegrable (fun t => (1/2:ℝ)*iteratedDeriv 2 (F t) (b t)) volume 0 τ :=
    (hQ.intervalIntegrable _ _).const_mul _
  rw [intervalIntegral.integral_add (hV.intervalIntegrable _ _) hhalf,
    intervalIntegral.integral_const_mul] at hneg
  have hini : F 0 (b 0) = radial (-β) x ε := by rw [hb0]; exact field_initial hε hT.le β a _ U x
  change F τ (b τ) ≤ (F τ (b τ)-F 0 (b 0)-(∫ t in (0:ℝ)..τ,V t (b t))-
    (1/2:ℝ)*∫ t in (0:ℝ)..τ,iteratedDeriv 2 (F t) (b t))+radial (-β) x ε
  rw [hini]
  linarith

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.Swallowing
open LoewnerCutoff LoewnerExit BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
variable {ε : ℝ} (hε : 0 < ε)

def coeffAt (k : ℕ) (s : ℝ≥0) (β C sdev : ℝ) (z : ℂ) (ρ δ : ℝ)
    (q : C(I, ℝ) × ℝ) : ℝ := by
  classical
  exact if ∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg q.1 z ρ δ t then
    iteratedDeriv k (field hε s.coe_nonneg β C sdev q.1 z s) q.2 else 0

lemma coeffAt_measurable (k : ℕ) (hk : k = 1 ∨ k = 2) (s : ℝ≥0)
    (β C sdev : ℝ) (z : ℂ) (ρ δ : ℝ) :
    @Measurable (C(I, ℝ) × ℝ) ℝ (@Prod.instMeasurableSpace _ _ (borel _) inferInstance) _ (coeffAt hε k s β C sdev z ρ δ) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  have hc : Continuous (fun q : C(I, ℝ) × ℝ =>
      iteratedDeriv k (field hε s.coe_nonneg β C sdev q.1 z s) q.2) := by
    have hp : Continuous (fun q : C(I, ℝ) × ℝ => ((q.1,(s:ℝ)),q.2)) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    have hh := (continuous_coeff hε s.coe_nonneg β C sdev z k hk).comp hp
    dsimp only [Function.comp_def] at hh
    exact hh
  apply hc.measurable.ite _ measurable_const
  exact ((isOpen_positive_on hε s.coe_nonneg z ρ δ s).preimage continuous_fst).measurableSet

def rawCoeff {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (β C sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (sample : Ω) : ℝ :=
  if s < T then coeffAt hε k s β C sdev z ρ δ (BrownianDriver.path B sdev s sample, B s sample) else 0

lemma rawCoeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (hk : k = 1 ∨ k = 2) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (β C sdev : ℝ) (z : ℂ) (ρ δ : ℝ) :
    Measurable[pastSigma B s] (rawCoeff hε k B T s β C sdev z ρ δ) := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  let : MeasurableSpace Ω := pastSigma B s
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s β C sdev z ρ δ).comp
      ((BrownianDriver.path_measurable_past B sdev s).prodMk (past_measurable_eval B (s := s) le_rfl))
  · exact measurable_const

lemma rawCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (T s : ℝ≥0)
    (β C sdev : ℝ) (z : ℂ) (ρ δ : ℝ) :
    AEMeasurable (rawCoeff hε k B T s β C sdev z ρ δ) P := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s β C sdev z ρ δ).comp_aemeasurable
      ((BrownianDriver.path_aemeasurable hB sdev s).prodMk (hB.toIsPreBrownianReal.hasLaw_eval s).aemeasurable)
  · exact aemeasurable_const

lemma rawCoeff_eq {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (hT : 0 < (T:ℝ)) (β C sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) :
    rawCoeff hε k B T s β C sdev z ρ δ sample =
      if (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ then
        iteratedDeriv k (field hε T.coe_nonneg β C sdev (BrownianDriver.path B sdev T sample) z s) (B s sample) else 0 := by
  classical
  by_cases hsT : s < T
  · have he := BrownianDriver.prefix_eq B sdev s T sample hc hsT.le
    have hf := field_prefix_eq hε T.coe_nonneg s.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z β C sdev he
      ⟨s.coe_nonneg, le_rfl⟩
    have hd := deficit_prefix_eq hε s.coe_nonneg T.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z ρ δ he
    have hi : (∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg (BrownianDriver.path B sdev s sample) z ρ δ t) ↔
        (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ := by
      rw [lt_stop_iff hε T.coe_nonneg hT _ z ρ δ ⟨s.coe_nonneg,hsT⟩]
      exact forall₂_congr (fun t ht => by rw [hd ht])
    simp only [rawCoeff, ite_eq_left hsT, coeffAt, hi, hf]
  · have hstop : ¬ (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ :=
      not_lt_of_ge ((stop_bounds hε T.coe_nonneg _ z ρ δ).2.trans (not_lt.1 hsT))
    simp only [rawCoeff, ite_eq_right hsT, ite_eq_right hstop]

lemma rawCoeff_stoppedCoeff_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (T : ℝ≥0)
    (hT : 0 < (T:ℝ)) (β C sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (n i : ℕ) :
    rawCoeff hε k B T (dyadicTime T n i) β C sdev z ρ δ =ᵐ[P]
      stoppedCoeff k B T
        (fun sample => stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ)
        (fun sample => field hε T.coe_nonneg β C sdev (BrownianDriver.path B sdev T sample) z) n i := by
  filter_upwards [hB.cont] with sample hc
  rw [rawCoeff_eq hε k B T _ hT β C sdev z ρ δ sample hc]
  simp only [stoppedCoeff, coe_dyadicTime]

theorem localized_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (β C sdev : ℝ) (hβ : β ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ) (ρ δ : ℝ) :
    let U := BrownianDriver.path B sdev T
    let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
    let F := fun sample => field hε T.coe_nonneg β C sdev (U sample) z
    let V := fun sample => drift hε T.coe_nonneg β C sdev (U sample) z
    let Y := fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
      (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
      (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)
    Integrable Y P ∧ (∫ sample, Y sample ∂P) = 0 := by
  dsimp only
  let U := BrownianDriver.path B sdev T
  let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
  let F := fun sample => field hε T.coe_nonneg β C sdev (U sample) z
  let V := fun sample => drift hε T.coe_nonneg β C sdev (U sample) z
  have hreg : ∀ᵐ sample ∂P, BrownianField.FieldRegular (F sample) (V sample)
      (fun t => B t.toNNReal sample) (τ sample) := by
    filter_upwards [hB.cont] with sample hc
    exact regular hε T.coe_nonneg hT β C sdev hβ (U sample) z ρ δ _
      (hc.comp continuous_real_toNNReal)
  have htau : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T :=
    Filter.Eventually.of_forall (fun sample => stop_bounds hε T.coe_nonneg (U sample) z ρ δ)
  obtain ⟨K₁,hK₁,hb₁⟩ := coeff_uniform_bound hε T.coe_nonneg β C sdev hβ z 1 (Or.inl rfl)
  obtain ⟨K₂,hK₂,hb₂⟩ := coeff_uniform_bound hε T.coe_nonneg β C sdev hβ z 2 (Or.inr (Or.inl rfl))
  have hsbound (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ (W : C(I, ℝ)) (t b : ℝ),
        |iteratedDeriv k (field hε T.coe_nonneg β C sdev W z t) b| ≤ K)
      (n i : ℕ) : ∀ᵐ sample ∂P, |stoppedCoeff k B T τ F n i sample| ≤ K := by
    apply Filter.Eventually.of_forall
    intro sample
    unfold stoppedCoeff
    split_ifs
    · exact hb _ _ _
    · simpa only [abs_zero] using hK
  let A := fun n i => rawCoeff hε 1 B T (dyadicTime T n i) β C sdev z ρ δ
  let Q := fun n i => rawCoeff hε 2 B T (dyadicTime T n i) β C sdev z ρ δ
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 1 T hT β C sdev z ρ δ n i
  have hCe (n i : ℕ) : Q n i =ᵐ[P] stoppedCoeff 2 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 2 T hT β C sdev z ρ δ n i
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (A n i) :=
    rawCoeff_measurable_past hε 1 (Or.inl rfl) B T _ _ _ _ z ρ δ
  have hCm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (Q n i) :=
    rawCoeff_measurable_past hε 2 (Or.inr rfl) B T _ _ _ _ z ρ δ
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 1 (Or.inl rfl) T _ _ _ _ z ρ δ).aestronglyMeasurable K₁
    filter_upwards [hAe n i, hsbound 1 K₁ hK₁ hb₁ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |A n i sample| ≤ K₁
    rw [he]
    exact hb
  have hC2 (n i : ℕ) : MemLp (Q n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 2 (Or.inr rfl) T _ _ _ _ z ρ δ).aestronglyMeasurable K₂
    filter_upwards [hCe n i, hsbound 2 K₂ hK₂ hb₂ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |Q n i sample| ≤ K₂
    rw [he]
    exact hb
  have hi := stopped_field_ito_centered_ae hB T τ F V htau hreg A Q hAe hCe hCm hC2
    K₂ hK₂ (hsbound 2 K₂ hK₂ hb₂) hAm hA2 K₁ hK₁ (hsbound 1 K₁ hK₁ hb₁)
  exact hi

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.Swallowing
open GreenPhysical LoewnerCutoff LoewnerExit

abbrev correction {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β C : ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  let U := BrownianDriver.path B (Real.sqrt κ) T ω
  let τ := stop hε T.coe_nonneg U z 0 0
  let F := field hε T.coe_nonneg β C (Real.sqrt κ) U z
  let V := drift hε T.coe_nonneg β C (Real.sqrt κ) U z
  F τ (B τ.toNNReal ω)-F 0 (B 0 ω)-
    (∫ t in (0:ℝ)..τ, V t (B t.toNNReal ω))-
      (1/2:ℝ)*∫ t in (0:ℝ)..τ, iteratedDeriv 2 (F t) (B t.toNNReal ω)

def budget {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β C : ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  if T=0 then lyapunov β C z.re z.im else
    max (correction B κ β C hε T z ω+lyapunov β C z.re z.im) 0

lemma field_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) (hy : ε ≤ z.im) :
    field hε hT β C s U z 0 0 = lyapunov β C z.re z.im := by
  simp only [field,LoewnerField.height,position_initial,mul_zero,sub_zero,max_eq_right hy]

lemma generator_field {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (κ β C : ℝ) (hκ : 0 ≤ κ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ)
    (hy : ε ≤ (position hε hT U z t).im)
    (hU : extendDriver T U t = Real.sqrt κ*b) :
    drift hε hT β C (Real.sqrt κ) U z t b+
      (1/2:ℝ)*iteratedDeriv 2 (field hε hT β C (Real.sqrt κ) U z t) b =
    generator κ β C ((position hε hT U z t).re-Real.sqrt κ*b) (LoewnerField.height hε hT U z t) := by
  have hh : LoewnerField.height hε hT U z t = (position hε hT U z t).im := max_eq_right hy
  rw [second_eq,Real.sq_sqrt hκ]
  dsimp only [drift]
  rw [velocity_eq hy,hh,hU]
  simp only [generator,Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,
    Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero,zero_mul,
    Complex.normSq_apply]
  ring

lemma deterministic_budget {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (κ β : ℝ) (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    (U : C(I, ℝ)) (z : ℂ) (hz : ε ≤ z.im) (b : ℝ → ℝ) (hb : Continuous b)
    (hb0 : b 0=0) (hU : EqOn (extendDriver T U) (fun t => Real.sqrt κ*b t) (Icc 0 T)) :
    let C := (2*κ-8-κ*β)/4
    let d := β*(κ-4-κ*β)/2
    let τ := stop hε hT.le U z 0 0
    let F := field hε hT.le β C (Real.sqrt κ) U z
    let V := drift hε hT.le β C (Real.sqrt κ) U z
    let E := ∫ t in (0:ℝ)..τ,
      (((position hε hT.le U z t).re-Real.sqrt κ*b t)^2+(LoewnerField.height hε hT.le U z t)^2)^(β/2-1)
    0 ≤ E ∧
      F τ (b τ)+d*E ≤
        (F τ (b τ)-F 0 (b 0)- (∫ t in (0:ℝ)..τ,V t (b t))-
          (1/2:ℝ)*∫ t in (0:ℝ)..τ, iteratedDeriv 2 (F t) (b t))+lyapunov β C z.re z.im := by
  dsimp only
  let C := (2*κ-8-κ*β)/4
  let d := β*(κ-4-κ*β)/2
  let τ := stop hε hT.le U z 0 0
  let F := field hε hT.le β C (Real.sqrt κ) U z
  let V := drift hε hT.le β C (Real.sqrt κ) U z
  let H := fun t => (((position hε hT.le U z t).re-Real.sqrt κ*b t)^2+
    (LoewnerField.height hε hT.le U z t)^2)^(β/2-1)
  have htau := stop_bounds hε hT.le U z 0 0
  have hmap : Continuous (fun t => ((U,t),b t)) := (continuous_const.prodMk continuous_id).prodMk hb
  have hV : Continuous (fun t => V t (b t)) := by
    have hh := (continuous_drift hε hT.le β C (Real.sqrt κ) z).comp hmap
    dsimp only [Function.comp_def] at hh
    exact hh
  have hQ : Continuous (fun t => iteratedDeriv 2 (F t) (b t)) := by
    have hh := (continuous_coeff hε hT.le β C (Real.sqrt κ) z 2 (Or.inr rfl)).comp hmap
    dsimp only [Function.comp_def] at hh
    exact hh
  have hHc : Continuous H := by
    have hP := (continuous_position hε hT.le z).comp (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ => (U,t)))
    have hx := (Complex.continuous_re.comp hP).sub (continuous_const.mul hb : Continuous (fun t => Real.sqrt κ*b t))
    have hy : Continuous (LoewnerField.height hε hT.le U z) := continuous_const.max (Complex.continuous_im.comp hP)
    exact ((hx.pow 2).add (hy.pow 2)).rpow_const (fun t => Or.inl (q_pos _ (LoewnerField.height_pos hε hT.le U z t)).ne')
  have hH0 : 0 ≤ ∫ t in (0:ℝ)..τ,H t := by
    apply intervalIntegral.integral_nonneg htau.1
    intro t ht
    exact Real.rpow_nonneg (by positivity) _
  refine ⟨hH0,?_⟩
  have hpoint : ∀ t ∈ Ioo 0 τ, V t (b t)+(1/2:ℝ)*iteratedDeriv 2 (F t) (b t) ≤ -d*H t := by
    intro t ht
    have hh := (deficit_pos_iff hε hT.le U z 0 0 t).1
      (positive_before hε hT.le hT U z 0 0 ht.1.le ht.2)
    have he := generator_field hε hT.le κ β C (by linarith) U z t (b t) hh.2.1.le
      (hU ⟨ht.1.le,ht.2.le.trans htau.2⟩)
    change V t (b t)+(1/2:ℝ)*iteratedDeriv 2 (F t) (b t) = _ at he
    rw [he]
    exact (generator_negative hκ hβ hβκ _ (LoewnerField.height_pos hε hT.le U z t)).2.2
  have hm : (∫ t in (0:ℝ)..τ, V t (b t)+(1/2:ℝ)*iteratedDeriv 2 (F t) (b t)) ≤
      ∫ t in (0:ℝ)..τ, -d*H t := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo htau.1
      ((hV.add (continuous_const.mul hQ)).intervalIntegrable _ _)
      ((continuous_const.mul hHc).intervalIntegrable _ _) hpoint
  have hhalf : IntervalIntegrable (fun t => (1/2:ℝ)*iteratedDeriv 2 (F t) (b t)) volume 0 τ :=
    (hQ.intervalIntegrable _ _).const_mul _
  rw [intervalIntegral.integral_add (hV.intervalIntegrable _ _) hhalf,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hm
  have hinit : F 0 (b 0) = lyapunov β C z.re z.im := by rw [hb0]; exact field_initial hε hT.le β C _ U z hz
  change F τ (b τ)+d*(∫ t in (0:ℝ)..τ,H t) ≤
    (F τ (b τ)-F 0 (b 0)-(∫ t in (0:ℝ)..τ,V t (b t))-
      (1/2:ℝ)*∫ t in (0:ℝ)..τ,iteratedDeriv 2 (F t) (b t))+lyapunov β C z.re z.im
  rw [hinit]
  linarith

lemma budget_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ β : ℝ) (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (z : ℂ) (hz : ε ≤ z.im) :
    let C := (2*κ-8-κ*β)/4
    Integrable (budget B κ β C hε T z) P ∧
      (∫ ω,budget B κ β C hε T z ω ∂P) = lyapunov β C z.re z.im ∧
      ∀ ω, 0 ≤ budget B κ β C hε T z ω := by
  dsimp only
  let C := (2*κ-8-κ*β)/4
  have hgen := generator_negative hκ hβ hβκ z.re (hε.trans_le hz)
  have hC : 0 ≤ C := hgen.1.le
  have hφ : 0 ≤ lyapunov β C z.re z.im := lyapunov_nonneg hC _ (hε.trans_le hz)
  by_cases hT0 : T=0
  · subst T
    have he0 : budget B κ β ((2*κ-8-κ*β)/4) hε 0 z =
        fun _ : Ω => lyapunov β C z.re z.im := by
      funext ω
      exact ite_eq_left rfl
    rw [he0]
    exact ⟨integrable_const _,by simp [C],fun _ => hφ⟩
  have hT : 0 < (T:ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hT0)
  have hb1 : β ≤ 1 := by have hh := div_pos (by norm_num : (0:ℝ)<4) (by linarith : 0<κ); linarith
  have hcenter := localized_centered hB β C (Real.sqrt κ) hb1 hε T hT z 0 0
  change Integrable (correction B κ β C hε T z) P ∧ (∫ ω,correction B κ β C hε T z ω ∂P)=0 at hcenter
  have he : budget B κ β C hε T z =ᵐ[P]
      (fun ω => correction B κ β C hε T z ω+lyapunov β C z.re z.im) := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hc hb0
    have hh := deterministic_budget hε hT κ β hκ hβ hβκ (BrownianDriver.path B (Real.sqrt κ) T ω) z hz
      (fun t => B t.toNNReal ω) (hc.comp continuous_real_toNNReal) (by simpa using hb0)
      (fun t ht => BrownianDriver.extend_eq B _ T ω hc ht)
    dsimp only at hh
    have hn := lyapunov_nonneg (β := β) hC
      ((position hε T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T ω) z
        (stop hε T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T ω) z 0 0)).re-
        Real.sqrt κ*B (stop hε T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T ω) z 0 0).toNNReal ω)
      (LoewnerField.height_pos hε T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T ω) z
        (stop hε T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T ω) z 0 0))
    have hh2 := hh.2
    simp only [Real.toNNReal_zero] at hh2
    have hpos : 0 ≤ correction B κ β C hε T z ω+lyapunov β C z.re z.im :=
      (add_nonneg hn (mul_nonneg hgen.2.1.le hh.1)).trans hh2
    simp only [budget,ite_eq_right hT0,max_eq_left hpos]
  have hi := hcenter.1.add (integrable_const (lyapunov β C z.re z.im))
  refine ⟨hi.congr he.symm,?_,fun ω => ?_⟩
  · rw [integral_congr_ae he,integral_add hcenter.1 (integrable_const _),hcenter.2,zero_add]
    simp [C]
  · simp only [budget,ite_eq_right hT0]
    exact le_max_right _ _

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Swallowing

lemma measure_eventually_budget {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (W : ℕ → Ω → ℝ) (M a : ℝ) (ha : 0 < a)
    (hi : ∀ n, Integrable (W n) P) (hn : ∀ n ω, 0 ≤ W n ω)
    (hmean : ∀ n, (∫ ω,W n ω ∂P)=M) (E : Set Ω)
    (hE : ∀ᵐ ω ∂P, ω∈E → ∀ᶠ n in atTop, a ≤ W n ω) :
    P E ≤ ENNReal.ofReal (M/a) := by
  let L := fun ω => liminf (fun n => ENNReal.ofReal (W n ω)) atTop
  have hm (n : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal (W n ω)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hi n).aemeasurable
  have hLm : AEMeasurable L P := by
    simp only [L,liminf_eq_iSup_iInf_of_nat]
    exact AEMeasurable.iSup (fun n => AEMeasurable.iInf (fun i => AEMeasurable.iInf (fun _ => hm i)))
  have hLi : (∫⁻ ω,L ω ∂P) ≤ ENNReal.ofReal M := by
    have hf := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hm
    have he (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (W n ω) ∂P)=ENNReal.ofReal M := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall (hn n)),hmean n]
    simpa only [he,liminf_const] using hf
  have hsub : E ≤ᵐ[P] {ω | ENNReal.ofReal a ≤ L ω} := by
    filter_upwards [hE] with ω hω
    intro hωE
    apply le_liminf_of_le (by isBoundedDefault)
    exact (hω hωE).mono (fun n hh => ENNReal.ofReal_le_ofReal hh)
  calc
    P E ≤ P {ω | ENNReal.ofReal a ≤ L ω} := measure_mono_ae hsub
    _ ≤ (∫⁻ ω,L ω ∂P)/ENNReal.ofReal a :=
      meas_ge_le_lintegral_div hLm (ENNReal.ofReal_ne_zero_iff.2 ha) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M/ENNReal.ofReal a := by gcongr
    _ = ENNReal.ofReal (M/a) := (ENNReal.ofReal_div_of_pos ha).symm

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing

abbrev correction {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β a : ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (x L : ℝ) (ω : Ω) : ℝ :=
  let U := BrownianDriver.path B (Real.sqrt κ) T ω
  let τ := stop hε T.coe_nonneg U x β a L
  let F := field hε T.coe_nonneg β a (Real.sqrt κ) U x
  let V := drift hε T.coe_nonneg β a (Real.sqrt κ) U x
  F τ (B τ.toNNReal ω)-F 0 (B 0 ω)-
    (∫ t in (0:ℝ)..τ,V t (B t.toNNReal ω))-
    (1/2:ℝ)*∫ t in (0:ℝ)..τ,iteratedDeriv 2 (F t) (B t.toNNReal ω)

def budget {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β a : ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (x L : ℝ) (ω : Ω) : ℝ :=
  max (correction B κ β a hε T x L ω+radial (-β) x ε) 0

lemma budget_nonneg {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β a : ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (x L : ℝ) (ω : Ω) :
    0 ≤ budget B κ β a hε T x L ω := le_max_right _ _

lemma budget_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (x L : ℝ) :
    Integrable (budget B κ β a hε T x L) P ∧
      (∫ ω,budget B κ β a hε T x L ω ∂P) = radial (-β) x ε := by
  have hc := localized_centered hB β a (Real.sqrt κ) hβ hε T hT x L
  change Integrable (correction B κ β a hε T x L) P ∧
    (∫ ω,correction B κ β a hε T x L ω ∂P)=0 at hc
  have he : budget B κ β a hε T x L =ᵐ[P] fun ω => correction B κ β a hε T x L ω+radial (-β) x ε := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hcont hb0
    have hh := deterministic_budget hε hT κ β a hκ hβ ha hba
      (BrownianDriver.path B (Real.sqrt κ) T ω) x L (fun t => B t.toNNReal ω)
      (hcont.comp continuous_real_toNNReal) (by simpa using hb0)
      (fun t ht => BrownianDriver.extend_eq B _ T ω hcont ht)
    dsimp only at hh
    simp only [Real.toNNReal_zero] at hh
    have hn := (field_pos hε T.coe_nonneg β a (Real.sqrt κ)
      (BrownianDriver.path B (Real.sqrt κ) T ω) x
      (stop hε T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T ω) x β a L)
      (B (stop hε T.coe_nonneg (BrownianDriver.path B (Real.sqrt κ) T ω) x β a L).toNNReal ω)).le
    exact max_eq_left (hn.trans hh)
  have hi := hc.1.add (integrable_const (radial (-β) x ε))
  refine ⟨hi.congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_add hc.1 (integrable_const _),hc.2,zero_add]
  simp

def reach (U : C(I, ℝ)) {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (x β a L : ℝ) : Prop :=
  ∃ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, ε < gap hε hT U x s) ∧ L ≤ weight hε hT U x β a t

lemma reached_terminal {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (U : C(I, ℝ))
    (x β a L : ℝ) (hreach : reach U hε hT.le x β a L) :
    L ≤ weight hε hT.le U x β a (stop hε hT.le U x β a L) := by
  obtain ⟨t,ht,hgap,hweight⟩ := hreach
  have hst : stop hε hT.le U x β a L ≤ t := by
    by_contra hn
    have hp := (deficit_pos_iff hε hT.le U x β a L t).1
      (positive_before hε hT.le hT U x β a L ht.1 (lt_of_not_ge hn))
    exact (not_lt_of_ge hweight) hp.2
  have hb := stop_bounds hε hT.le U x β a L
  by_cases hend : stop hε hT.le U x β a L < T
  · have hh := nonpos_at_of_lt hε hT.le hT U x β a L hend
    have hg := hgap _ ⟨hb.1,hst⟩
    simp only [deficit,min_le_iff,sub_nonpos] at hh
    rcases hh with hh | hh
    · exact (not_le_of_gt hg hh).elim
    · exact hh
  · have he : stop hε hT.le U x β a L=t := le_antisymm hst (ht.2.trans (not_lt.1 hend))
    rw [he]
    exact hweight

lemma budget_dominates_reach {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β a : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (x L : ℝ) (ω : Ω)
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω=0)
    (hr : reach (BrownianDriver.path B (Real.sqrt κ) T ω) hε T.coe_nonneg x β a L) :
    L ≤ budget B κ β a hε T x L ω := by
  let U := BrownianDriver.path B (Real.sqrt κ) T ω
  let τ := stop hε T.coe_nonneg U x β a L
  have htau := stop_bounds hε T.coe_nonneg U x β a L
  have hh := deterministic_budget hε hT κ β a hκ hβ ha hba U x L
    (fun t => B t.toNNReal ω) (hc.comp continuous_real_toNNReal) (by simpa using hb0)
    (fun t ht => BrownianDriver.extend_eq B _ T ω hc ht)
  have hw := reached_terminal hε hT U x β a L hr
  have he : field hε T.coe_nonneg β a (Real.sqrt κ) U x τ (B τ.toNNReal ω) =
      weight hε T.coe_nonneg U x β a τ := by
    have hU : extendDriver T U τ = Real.sqrt κ*B τ.toNNReal ω :=
      BrownianDriver.extend_eq B _ T ω hc htau
    simp only [field,weight,gap,hU]
  dsimp only at hh
  simp only [Real.toNNReal_zero] at hh
  change field hε T.coe_nonneg β a (Real.sqrt κ) U x τ (B τ.toNNReal ω) ≤
    correction B κ β a hε T x L ω+radial (-β) x ε at hh
  rw [he] at hh
  exact (hw.trans hh).trans (le_max_left _ _)

theorem maximal_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β a : ℝ)
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hba : κ*(β+1) ≤ 4+2*a)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (x L : ℝ) (hL : 0 < L) :
    P {ω | reach (BrownianDriver.path B (Real.sqrt κ) T ω) hε T.coe_nonneg x β a L} ≤
      ENNReal.ofReal (radial (-β) x ε/L) := by
  have hm := budget_mean hB κ β a hκ hβ ha hba hε T hT x L
  apply measure_eventually_budget (fun _ : ℕ => budget B κ β a hε T x L) _ L hL
    (fun _ => hm.1) (fun _ => budget_nonneg B κ β a hε T x L) (fun _ => hm.2)
  filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hc hb0
  intro hr
  exact Filter.Eventually.of_forall (fun _ => budget_dominates_reach B κ β a hκ hβ ha hba hε T hT x L ω hc hb0 hr)

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryFunctional

lemma continuous_position_time {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) : Continuous (position hε hT U z) := by
  have hp : Continuous (fun t : ℝ => (U, t)) := continuous_const.prodMk continuous_id
  have hh := (continuous_position hε hT z).comp hp
  change Continuous (position hε hT U z) at hh
  exact hh

lemma continuous_logDerivative_time {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) : Continuous (logDerivative hε hT U z) := by
  have hp : Continuous (fun t : ℝ => (U, t)) := continuous_const.prodMk continuous_id
  have hh := (continuous_logDerivative hε hT z).comp hp
  change Continuous (logDerivative hε hT U z) at hh
  exact hh

end SLEExactGauge.BoundaryFunctional

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen

lemma continuous_gap_time {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (x : ℝ) : Continuous (gap hε hT U x) := by
  have hp : Continuous (fun t : ℝ => (U,t)) := continuous_const.prodMk continuous_id
  have hh := (continuous_gap hε hT x).comp hp
  change Continuous (gap hε hT U x) at hh
  exact hh

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing

lemma norm_sum_lower {X δ : ℝ} {D : ℂ} (hX : 0 < X) (hδ : δ ≤ 1/2)
    (hD : ‖D‖ ≤ δ*X) : X/2 ≤ ‖(X:ℂ)+D‖ := by
  have hh := norm_sub_le ((X:ℂ)+D) D
  rw [add_sub_cancel_right,Complex.norm_real,Real.norm_of_nonneg hX.le] at hh
  have hm := mul_le_mul_of_nonneg_right hδ hX.le
  linarith

lemma ratio_real_lower {X δ a : ℝ} {D : ℂ} (hX : 0 < X) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2)
    (hD : ‖D‖ ≤ δ*X) (haδ : a ≤ 2-4*δ) :
    a ≤ 2*((X:ℂ)/((X:ℂ)+D)).re := by
  have hlo := norm_sum_lower hX hδ hD
  have hn : (X:ℂ)+D ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hlo)
  have hquot : ‖D/((X:ℂ)+D)‖ ≤ 2*δ := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hn)).2
    calc
      ‖D‖ ≤ δ*X := hD
      _ ≤ (2*δ)*‖(X:ℂ)+D‖ := by nlinarith
  have he : (X:ℂ)/((X:ℂ)+D) = 1-D/((X:ℂ)+D) := by field_simp; ring
  rw [he,Complex.sub_re,Complex.one_re]
  have hre := (Complex.re_le_norm (D/((X:ℂ)+D))).trans hquot
  linarith

lemma normSq_slope (X : ℝ) (D : ℂ) (hX : X ≠ 0) (hD : (X:ℂ)+D ≠ 0) :
    2*D.re*(2/((X:ℂ)+D)-2/(X:ℂ)).re +
      2*D.im*(2/((X:ℂ)+D)-2/(X:ℂ)).im =
    -4*Complex.normSq D / X^2 * ((X:ℂ)/((X:ℂ)+D)).re := by
  have hQ : (X+D.re)^2+D.im^2 ≠ 0 := by
    have hh := (Complex.normSq_pos.mpr hD).ne'
    simpa only [Complex.normSq_apply,Complex.add_re,Complex.ofReal_re,Complex.add_im,
      Complex.ofReal_im,zero_add,pow_two] using hh
  simp only [Complex.sub_re,Complex.sub_im,Complex.div_re,Complex.div_im,Complex.re_ofNat,
    Complex.im_ofNat,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.normSq_apply,zero_add,zero_mul,mul_zero,add_zero]
  simp only [← pow_two]
  field_simp
  ring

lemma energy_deriv {D : ℝ → ℂ} {l : ℝ → ℝ} {t X a : ℝ}
    (hX : X ≠ 0) (hD : (X:ℂ)+D t ≠ 0)
    (hd : HasDerivAt D (2/((X:ℂ)+D t)-2/(X:ℂ)) t)
    (hl : HasDerivAt l (-2/X^2) t) :
    HasDerivAt (fun s => Complex.normSq (D s)*Real.exp (-a*l s))
      (Real.exp (-a*l t)*(-4*Complex.normSq (D t)/X^2*((X:ℂ)/((X:ℂ)+D t)).re+
        2*a/X^2*Complex.normSq (D t))) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
  dsimp only [Function.comp_def,Complex.reCLM_apply,Complex.imCLM_apply] at hre him
  have hq := (hre.pow 2).add (him.pow 2)
  have hq' : HasDerivAt (fun s => Complex.normSq (D s))
      (2*(D t).re*(2/((X:ℂ)+D t)-2/(X:ℂ)).re+2*(D t).im*(2/((X:ℂ)+D t)-2/(X:ℂ)).im) t := by
    convert hq using 1 <;> (try simp only [Complex.normSq_apply,pow_two]) <;> first | rfl | ring
  rw [normSq_slope _ _ hX hD] at hq'
  apply (hq'.mul ((hl.const_mul (-a)).exp)).congr_deriv
  ring

lemma energy_antitone {S δ a : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) (haδ : a ≤ 2-4*δ)
    (D : ℝ → ℂ) (l X : ℝ → ℝ) (hDc : ContinuousOn D (Icc 0 S)) (hlc : Continuous l)
    (hX : ∀ t ∈ Ioo 0 S, 0 < X t)
    (hDd : ∀ t ∈ Ioo 0 S, HasDerivAt D (2/((X t:ℂ)+D t)-2/(X t:ℂ)) t)
    (hld : ∀ t ∈ Ioo 0 S, HasDerivAt l (-2/(X t)^2) t)
    (hratio : ∀ t ∈ Ioo 0 S, ‖D t‖ ≤ δ*X t) :
    AntitoneOn (fun t => Complex.normSq (D t)*Real.exp (-a*l t)) (Icc 0 S) := by
  have hEc : ContinuousOn (fun t => Complex.normSq (D t)*Real.exp (-a*l t)) (Icc 0 S) :=
    (Complex.continuous_normSq.comp_continuousOn hDc).mul
      ((Real.continuous_exp.comp (continuous_const.mul hlc)).continuousOn)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 S) hEc
    (f' := fun t => Real.exp (-a*l t)*(-4*Complex.normSq (D t)/(X t)^2*
      ((X t:ℂ)/((X t:ℂ)+D t)).re+2*a/(X t)^2*Complex.normSq (D t)))
  · intro t ht
    rw [interior_Icc] at ht
    have hn : (X t:ℂ)+D t ≠ 0 := norm_pos_iff.mp
      (lt_of_lt_of_le (half_pos (hX t ht)) (norm_sum_lower (hX t ht) hδ (hratio t ht)))
    exact (energy_deriv (hX t ht).ne' hn (hDd t ht) (hld t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have hr := ratio_real_lower (hX t ht) hδ0 hδ (hratio t ht) haδ
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hq := Complex.normSq_nonneg (D t)
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Complex.normSq (D t)/(X t)^2 by positivity)
    convert sub_nonpos.mpr hh using 1
    ring

lemma gap_coefficients {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (x t : ℝ) (hx : ε ≤ gap hε hT U x t) :
    velocity ε (extendDriver T U t) (position hε hT U (x:ℂ) t) = 2/(gap hε hT U x t:ℂ) ∧
      variation hε hT U (x:ℂ) t = -2/(gap hε hT U x t)^2 := by
  have hz : position hε hT U (x:ℂ) t = ((position hε hT U (x:ℂ) t).re:ℂ) := by
    apply Complex.ext <;> simp [position_im_zero]
  have hc : clampRe ε (position hε hT U (x:ℂ) t-(extendDriver T U t:ℂ)) =
      (gap hε hT U x t:ℂ) := by
    change BoundaryCutoff.clamp 1 ε _ = _
    rw [BoundaryCutoff.clamp_eq (by norm_num : |(1:ℝ)|=1) (by simpa [gap] using hx),hz]
    simp only [gap,Complex.ofReal_sub]
  constructor
  · change 2/clampRe ε _ = _; rw [hc]
  · unfold variation
    rw [hc]
    norm_cast

lemma gap_difference_deriv {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (x : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hx : ε ≤ gap hε hT U x t) (G : ℝ → ℂ)
    (hG : HasDerivAt G (2/(G t-(extendDriver T U t:ℂ))) t) :
    HasDerivAt (fun s => G s-position hε hT U (x:ℂ) s)
      (2/((gap hε hT U x t:ℂ)+(G t-position hε hT U (x:ℂ) t))-
        2/(gap hε hT U x t:ℂ)) t := by
  have hh := hG.sub (position_deriv hε hT U (x:ℂ) ht)
  rw [(gap_coefficients hε hT U x t hx).1] at hh
  have hz : position hε hT U (x:ℂ) t = ((position hε hT U (x:ℂ) t).re:ℂ) := by
    apply Complex.ext <;> simp [position_im_zero]
  have hg : G t-(extendDriver T U t:ℂ) = (gap hε hT U x t:ℂ)+(G t-position hε hT U (x:ℂ) t) := by
    unfold gap
    rw [Complex.ofReal_sub,← hz]
    ring
  rw [hg] at hh
  exact hh

lemma ratio_energy {ε T S : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (U : C(I, ℝ)) (x a δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) (haδ : a ≤ 2-4*δ)
    (G : ℝ → ℂ) (hGc : ContinuousOn G (Icc 0 S))
    (hGd : ∀ t ∈ Ioo 0 S, HasDerivAt G (2/(G t-(extendDriver T U t:ℂ))) t)
    (hgap : ∀ t ∈ Icc 0 S, ε ≤ gap hε hT U x t)
    (hratio : ∀ t ∈ Icc 0 S, ‖G t-position hε hT U (x:ℂ) t‖ ≤ δ*gap hε hT U x t) :
    Complex.normSq (G S-position hε hT U (x:ℂ) S) *
      Real.exp (-a*logDerivative hε hT U (x:ℂ) S) ≤ Complex.normSq (G 0-(x:ℂ)) := by
  let D : ℝ → ℂ := fun t => G t-position hε hT U (x:ℂ) t
  let l : ℝ → ℝ := logDerivative hε hT U (x:ℂ)
  let X : ℝ → ℝ := gap hε hT U x
  have hHc : Continuous (fun t => position hε hT U (x:ℂ) t) :=
    continuous_position_time hε hT U (x:ℂ)
  have hDc : ContinuousOn D (Icc 0 S) := hGc.sub hHc.continuousOn
  have hlc : Continuous l :=
    continuous_logDerivative_time hε hT U (x:ℂ)
  have hXd (t : ℝ) (ht : t ∈ Ioo 0 S) : 0 < X t := hε.trans_le (hgap t ⟨ht.1.le,ht.2.le⟩)
  have hDd (t : ℝ) (ht : t ∈ Ioo 0 S) : HasDerivAt D (2/((X t:ℂ)+D t)-2/(X t:ℂ)) t :=
    gap_difference_deriv hε hT U x ⟨ht.1,ht.2.trans_le hST⟩ (hgap t ⟨ht.1.le,ht.2.le⟩) G (hGd t ht)
  have hld (t : ℝ) (ht : t ∈ Ioo 0 S) : HasDerivAt l (-2/(X t)^2) t := by
    have hh := hasDerivAt_logDerivative hε hT U (x:ℂ) ⟨ht.1,ht.2.trans_le hST⟩
    rw [(gap_coefficients hε hT U x t (hgap t ⟨ht.1.le,ht.2.le⟩)).2] at hh
    exact hh
  have ha := energy_antitone hδ0 hδ haδ D l X hDc hlc hXd hDd hld
    (fun t ht => hratio t ⟨ht.1.le,ht.2.le⟩)
  have hh := ha ⟨le_rfl,hS⟩ ⟨hS,le_rfl⟩ hS
  change Complex.normSq (D S)*Real.exp (-a*l S) ≤ Complex.normSq (G 0-(x:ℂ))
  have he : Complex.normSq (D 0)*Real.exp (-a*l 0) = Complex.normSq (G 0-(x:ℂ)) := by
    dsimp only [D,l]
    rw [position_initial,logDerivative_initial,mul_zero,Real.exp_zero,mul_one]
  exact hh.trans_eq he

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open Swallowing

lemma energy_weight_bound {β a l d δ X ε N : ℝ} (hβ : 0 < β) (hd : 0 < d)
    (hδ : 0 ≤ δ) (hX : 0 < X) (hε0 : 0 ≤ ε) (hε : ε ≤ X) (_hN : 0 ≤ N)
    (henergy : N^2*Real.exp (-a*l) ≤ d^2)
    (hweight : Real.exp ((a*β/2)*l)*radial (-β) X ε ≤ (δ/(4*d))^β) :
    N ≤ (δ/2)*X := by
  let E := Real.exp ((a/2)*l)
  let Q := Real.sqrt (X^2+ε^2)
  have hE : 0 < E := Real.exp_pos _
  have hQ2 : 0 < X^2+ε^2 := by positivity
  have hQ : 0 < Q := Real.sqrt_pos.2 hQ2
  have hQsq : Q^2=X^2+ε^2 := Real.sq_sqrt hQ2.le
  have hQbound : Q ≤ 2*X := by nlinarith [sq_nonneg (X-ε)]
  have hep : Real.exp (-a*l)*E^2 = 1 := by
    dsimp only [E]
    rw [sq,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hNEsq : N^2 ≤ (d*E)^2 := by
    have hh := mul_le_mul_of_nonneg_right henergy (sq_nonneg E)
    rw [mul_assoc,hep,mul_one] at hh
    nlinarith only [hh]
  have hNE : N ≤ d*E := by nlinarith [mul_pos hd hE]
  have hEp : E^β=Real.exp ((a*β/2)*l) := by
    dsimp only [E]
    rw [← Real.exp_mul]
    congr 1
    ring
  have hQp : Q^β=(X^2+ε^2)^(β/2) := by
    dsimp only [Q]
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hQ2.le]
    congr 1
    ring
  have hwp : Real.exp ((a*β/2)*l)*radial (-β) X ε = (E/Q)^β := by
    rw [Real.div_rpow hE.le hQ.le,hEp,hQp]
    unfold radial
    rw [show (-β)/2 = -(β/2) by ring,Real.rpow_neg hQ2.le]
    rfl
  rw [hwp] at hweight
  have hR : 0 ≤ δ/(4*d) := by positivity
  have hER : E/Q ≤ δ/(4*d) := (Real.rpow_le_rpow_iff (div_nonneg hE.le hQ.le) hR hβ).1 hweight
  have heQ : E ≤ (δ/(4*d))*Q := (div_le_iff₀ hQ).1 hER
  calc
    N ≤ d*E := hNE
    _ ≤ d*((δ/(4*d))*Q) := mul_le_mul_of_nonneg_left heQ hd.le
    _ ≤ d*((δ/(4*d))*(2*X)) := by gcongr
    _ = (δ/2)*X := by field_simp; ring

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter
open scoped Topology
namespace SLEExactGauge.BoundaryGreen

lemma first_zero_of_nonpos {F : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hF : Continuous F) (h0 : 0 < F 0) (hSval : F S ≤ 0) :
    ∃ σ ∈ Ioc 0 S, F σ = 0 ∧ ∀ s ∈ Icc 0 σ, 0 ≤ F s := by
  let K : Set ℝ := Icc 0 S ∩ {s | F s ≤ 0}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le hF continuous_const)
  have hne : K.Nonempty := ⟨S,⟨hS,le_rfl⟩,hSval⟩
  let σ := sInf K
  have hmem : σ ∈ K := hK.sInf_mem hne
  have hσ : 0 < σ := by
    apply lt_of_le_of_ne hmem.1.1
    intro heq
    have hh := hmem.2
    rw [← heq] at hh
    exact (not_le_of_gt h0) hh
  have hbefore : ∀ s ∈ Ico 0 σ, 0 < F s := by
    intro s hs
    by_contra hn
    have hm : s ∈ K := ⟨⟨hs.1,hs.2.le.trans hmem.1.2⟩,not_lt.1 hn⟩
    exact (not_le_of_gt hs.2) (csInf_le hK.bddBelow hm)
  have hσval : 0 ≤ F σ := by
    apply ge_of_tendsto (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto F (𝓝[<] σ) (𝓝 (F σ)))
    filter_upwards [Ioo_mem_nhdsLT hσ] with s hs
    exact (hbefore s ⟨hs.1.le,hs.2⟩).le
  refine ⟨σ,⟨hσ,hmem.1.2⟩,le_antisymm hmem.2 hσval,?_⟩
  intro s hs
  rcases lt_or_eq_of_le hs.2 with hlt | rfl
  · exact (hbefore s ⟨hs.1,hlt⟩).le
  · exact hσval

lemma first_zero_of_nonpos_on {F : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hF : ContinuousOn F (Icc 0 S)) (h0 : 0 < F 0) (hSval : F S ≤ 0) :
    ∃ σ ∈ Ioc 0 S, F σ = 0 ∧ ∀ s ∈ Icc 0 σ, 0 ≤ F s := by
  let Fc : ℝ → ℝ := fun s => F (projIcc 0 S hS s)
  have hc : Continuous Fc := hF.comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc (h := hS))) (fun s => (projIcc 0 S hS s).property)
  have he (s : ℝ) (hs : s ∈ Icc 0 S) : Fc s=F s := by
    simp only [Fc,projIcc,max_eq_right hs.1,min_eq_right hs.2]
  obtain ⟨σ,hσ,hz,hpre⟩ := first_zero_of_nonpos hS hc (by rwa [he 0 ⟨le_rfl,hS⟩])
    (by rwa [he S ⟨hS,le_rfl⟩])
  refine ⟨σ,hσ,?_,?_⟩
  · rwa [he σ ⟨hσ.1.le,hσ.2⟩] at hz
  · intro s hs
    have hh := hpre s hs
    rwa [he s ⟨hs.1,hs.2.trans hσ.2⟩] at hh

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing

lemma tip_forces_reach {ε T S : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (hS : 0 ≤ S) (hST : S ≤ T)
    (U : C(I, ℝ)) (hu0 : extendDriver T U 0=0)
    (x a β δ d y : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (haδ : a ≤ 2-4*δ) (hd : 0 < d) (hdx : d < δ*x) (hεx : 2*ε < x) (hy : δ*ε < y)
    (G : ℝ → ℂ) (hGc : ContinuousOn G (Icc 0 S))
    (hGd : ∀ t ∈ Ioo 0 S, HasDerivAt G (2/(G t-(extendDriver T U t:ℂ))) t)
    (hG0 : ‖G 0-(x:ℂ)‖ ≤ d) (hheight : ∀ t ∈ Icc 0 S, y ≤ (G t).im)
    (hGend : (G S).re=extendDriver T U S) :
    reach U hε hT x β a ((δ/(4*d))^β) := by
  let H : ℝ → ℂ := position hε hT U (x:ℂ)
  let X : ℝ → ℝ := gap hε hT U x
  let D : ℝ → ℂ := fun t => G t-H t
  let F : ℝ → ℝ := fun t => min (X t-2*ε) (δ*X t-‖D t‖)
  have hXc : Continuous X := continuous_gap_time hε hT U x
  have hDc : ContinuousOn D (Icc 0 S) :=
    hGc.sub (continuous_position_time hε hT U (x:ℂ)).continuousOn
  have hFc : ContinuousOn F (Icc 0 S) := continuous_min.comp_continuousOn
    ((hXc.continuousOn.sub continuousOn_const).prodMk
      ((continuousOn_const.mul hXc.continuousOn).sub hDc.norm))
  have hX0 : X 0=x := by simp only [X,gap,position_initial,Complex.ofReal_re,hu0,sub_zero]
  have hF0 : 0 < F 0 := by
    change 0 < min (X 0-2*ε) (δ*X 0-‖G 0-H 0‖)
    rw [hX0,show H 0=(x:ℂ) from position_initial hε hT U (x:ℂ)]
    exact lt_min (sub_pos.mpr hεx) (sub_pos.mpr (hG0.trans_lt hdx))
  have hRe : (D S).re = -X S := by
    change (G S-position hε hT U (x:ℂ) S).re = -gap hε hT U x S
    simp only [Complex.sub_re,gap,hGend]
    ring
  have hnorm : X S ≤ ‖D S‖ := by
    have hh := Complex.abs_re_le_norm (D S)
    rw [hRe,abs_neg] at hh
    exact (le_abs_self _).trans hh
  have hFS : F S ≤ 0 := by
    by_contra hn
    have hh := lt_min_iff.mp (lt_of_not_ge hn)
    have hXp : 0 < X S := by linarith [hh.1]
    have hm := mul_le_mul_of_nonneg_right hδhalf hXp.le
    linarith [hh.2]
  obtain ⟨q,hq,hzero,hpre⟩ := first_zero_of_nonpos_on hS hFc hF0 hFS
  have hgap : ∀ t ∈ Icc 0 q, 2*ε ≤ X t := by
    intro t ht
    exact sub_nonneg.mp (le_min_iff.mp (hpre t ht)).1
  have hratio : ∀ t ∈ Icc 0 q, ‖D t‖ ≤ δ*X t := by
    intro t ht
    exact sub_nonneg.mp (le_min_iff.mp (hpre t ht)).2
  have hXp : 0 < X q := hε.trans_le (by linarith [hgap q ⟨hq.1.le,le_rfl⟩])
  have hqT : q ≤ T := hq.2.trans hST
  have henergy := ratio_energy hε hT hq.1.le hqT U x a δ hδ.le hδhalf haδ G
    (hGc.mono (Icc_subset_Icc_right hq.2)) (fun t ht => hGd t ⟨ht.1,ht.2.trans_le hq.2⟩)
    (fun t ht => by change ε ≤ X t; linarith [hgap t ht]) hratio
  have hEn : ‖D q‖^2*Real.exp (-a*logDerivative hε hT U (x:ℂ) q) ≤ d^2 := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at henergy
    exact henergy.trans (sq_le_sq₀ (norm_nonneg _) hd.le |>.2 hG0)
  by_contra hreach
  have hweight : weight hε hT U x β a q ≤ (δ/(4*d))^β := by
    apply (not_le.mp ?_).le
    intro hh
    exact hreach ⟨q,⟨hq.1.le,hqT⟩,(fun t ht => by change ε < X t; linarith [hgap t ht]),hh⟩
  have hW : Real.exp ((a*β/2)*logDerivative hε hT U (x:ℂ) q)*radial (-β) (X q) ε ≤ (δ/(4*d))^β := hweight
  have hsmall := energy_weight_bound hβ hd hδ.le hXp hε.le
    (show ε ≤ X q by linarith [hgap q ⟨hq.1.le,le_rfl⟩]) (norm_nonneg (D q)) hEn hW
  have hym : y ≤ ‖D q‖ := by
    have hh := hheight q ⟨hq.1.le,hq.2⟩
    have him : (D q).im=(G q).im := by simp [D,H,position_im_zero]
    rw [← him] at hh
    exact hh.trans (Complex.im_le_norm _)
  have hgt : 2*ε < X q := by nlinarith
  have hrat : ‖D q‖ < δ*X q := by nlinarith [mul_pos hδ hXp]
  have hpos : 0 < F q := lt_min (sub_pos.mpr hgt) (sub_pos.mpr hrat)
  exact (ne_of_gt hpos) hzero

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal unitInterval
namespace SLEExactGauge.BoundaryGreen

lemma inverse_tip_point {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {t : ℝ} (ht : 0 ≤ t)
    {x : ℂ} {d : ℝ} (hclose : dist (γ t) x < d) :
    ∃ (w : ℂ) (y : ℝ), 0 < y ∧ dist w x < d ∧
      w ∈ localizationDomain γ t ∧ g t w=(driver t:ℂ)+(y:ℂ)*Complex.I := by
  have htip := h.2.2.2.2.2.2.2.2.2.2.2.2.2 t ht
  have he : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), dist (f t ((driver t:ℂ)+(y:ℂ)*Complex.I)) x < d :=
    htip.eventually (isOpen_ball.mem_nhds hclose)
  have hp : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), 0 < y := self_mem_nhdsWithin
  obtain ⟨y,hy,hball⟩ := (hp.and he).exists
  have hz : (driver t:ℂ)+(y:ℂ)*Complex.I ∈ halfPlane := by
    change 0 < ((driver t:ℂ)+(y:ℂ)*Complex.I).im
    simpa using hy
  refine ⟨f t ((driver t:ℂ)+(y:ℂ)*Complex.I),y,hy,hball,?_,?_⟩
  · exact h.2.2.2.2.2.2.2.2.1 t ht hz
  · exact h.2.2.2.2.2.2.2.2.2.2.1 t ht _ hz

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ReverseLoewner
open LoewnerCutoff

def velocity (ε u : ℝ) (w : ℂ) : ℂ := -LoewnerCutoff.velocity ε u w

lemma velocity_lipschitz {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    LipschitzWith ⟨4 / ε^2, by positivity⟩ (velocity ε u) :=
  (LoewnerCutoff.velocity_lipschitz hε u).neg

end SLEExactGauge.ReverseLoewner

end

end

end OAI
