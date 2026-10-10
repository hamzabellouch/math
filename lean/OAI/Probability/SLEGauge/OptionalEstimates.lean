import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ProductGenerators

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator Metric
end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator
 

theorem discounted_regime_optional {m : ℕ} (s : Finset (Fin m)) {a ε : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hsize : ε*((s.card:ℝ)-1)≤regK a/2)
    (cap σ off : Fin m → ℝ) (hσ : ∀ i∈s, |σ i|≤regBeta a)
    (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (Z : ℝ≥0 → Driver → RegimeState m) (hZc : ∀ b, Continuous (fun t => Z t b))
    (hZm : ∀ t, Measurable[rawFiltration t] (Z t))
    (A : RegimeState m → RegimeState m) (hAc : Continuous A)
    (K : ℝ) (hK : 0≤K) (hAb : ∀ z, ‖A z‖≤K)
    (hZeq : ∀ (u h : ℝ≥0) b, Z (u+h) b = Z u b + increment u h b • (multiNoise m,0) +
      ∫ t in (u:ℝ)..((u+h:ℝ≥0):ℝ), A (Z t.toNNReal b))
    (S T : Driver → ℝ≥0) (B N : ℝ≥0) (η : ℝ) (hη : 0<η)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b≤T b) (hTB : ∀ b, T b≤B)
    (hsafe : ∀ b t, S b≤t → t≤T b → ‖Z t b‖≤N ∧
      ∀ i∈s, η≤Y ((Z t b).1 i) ∧ physicalDelta a (cap i) (σ i) (off i) ((Z t b).1 i)≤1)
    (hA : ∀ b t, S b≤t → t≤T b →
      (A (Z t b)).2 = regimeDiscount s a ε cap σ off (Z t b).1 ∧
      ∀ i∈s, (A (Z t b)).1 i = physicalDrift a ((Z t b).1 i))
    (U : Set Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    ∫ b in U, discountedProduct s a cap σ off (Z (T b) b) ∂W ≤
      ∫ b in U, discountedProduct s a cap σ off (Z (S b) b) ∂W := by

  let f := regimeCutoff s a η N cap σ off
  have he : ‖(multiNoise m, (0 : ℝ))‖≤1 := by
    apply max_le _ (by norm_num)
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    simp [multiNoise,noise,Prod.norm_def]
  have hg (b : Driver) (t : ℝ≥0) (hts : S b≤t) (htt : t≤T b) :
      generator f A (multiNoise m,0) (Z t b)≤0 := by
    have hx := hsafe b t hts htt
    have hnear := regimeCutoff_eq_near s a η hη N cap σ off (Z t b) hx.1
      (fun i hi => (hx.2 i hi).1)
    have hn : (fun w => fderiv ℝ f w (multiNoise m,0)) =ᶠ[𝓝 (Z t b)]
        (fun w => fderiv ℝ (discountedProduct s a cap σ off) w (multiNoise m,0)) :=
      hnear.fderiv.mono fun w hw => congrArg (fun D : RegimeState m →L[ℝ] ℝ => D (multiNoise m,0)) hw
    change (1/2:ℝ)*fderiv ℝ (fun w => fderiv ℝ f w (multiNoise m,0)) (Z t b) (multiNoise m,0)+
      fderiv ℝ f (Z t b) (A (Z t b))≤0
    rw [hn.fderiv_eq,hnear.fderiv_eq]
    exact discountedProduct_nonpos s ha hε hsize cap σ off (Z t b) (A (Z t b))
      (fun i hi => hη.trans_le (hx.2 i hi).1) (fun i hi => (hx.2 i hi).2) hσ (hA b t hts htt)
  have h := compact_test_optional_inequality W hW Z hZc hZm A hAc K hK hAb
    (multiNoise m,0) he hZeq f (regimeCutoff_smooth s a η hη N cap σ off)
    (regimeCutoff_compact s a η N cap σ off) S T B hS hT hST hTB hg U hU
  have hfS (b : Driver) : f (Z (S b) b)=discountedProduct s a cap σ off (Z (S b) b) :=
    (regimeCutoff_eq_near s a η hη N cap σ off _ (hsafe b _ le_rfl (hST b)).1
      (fun i hi => ((hsafe b _ le_rfl (hST b)).2 i hi).1)).eq_of_nhds
  have hfT (b : Driver) : f (Z (T b) b)=discountedProduct s a cap σ off (Z (T b) b) :=
    (regimeCutoff_eq_near s a η hη N cap σ off _ (hsafe b _ (hST b) le_rfl).1
      (fun i hi => ((hsafe b _ (hST b) le_rfl).2 i hi).1)).eq_of_nhds
  simpa only [hfS,hfT] using h
end ExactSLEGreen

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

theorem compact_test_optional_on_event
    (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration t] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (S T : Driver → ℝ≥0) (B : ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b ≤ T b) (hTB : ∀ b, T b ≤ B)
    (U : Set Driver) (hU : MeasurableSet[hS.measurableSpace] U)
    (hneg : ∀ b∈U, ∀ t, S b ≤ t → t ≤ T b → generator f A e (X t b) ≤ 0) :
    ∫ b in U, f (X (T b) b) ∂W ≤ ∫ b in U, f (X (S b) b) ∂W := by
  let M : ℝ≥0 → Driver → ℝ := fun t b => f (X t b) -
    ∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)
  have hM : Martingale M rawFiltration W :=
    compact_smooth_brownian_martingale W hW X hXc hXm A hAc K hK hAb e he hXeq f hf hfc
  have hgc (b : Driver) : Continuous (fun u : ℝ => generator f A e (X u.toNNReal b)) :=
    (generator_continuous f hf A hAc e).comp ((hXc b).comp continuous_real_toNNReal)
  have hmc (b : Driver) : Continuous (fun t => M t b) :=
    (hf.continuous.comp (hXc b)).sub
      ((intervalIntegral.continuous_primitive (fun s t => (hgc b).intervalIntegrable s t) 0).comp NNReal.continuous_coe)
  obtain ⟨C,D,hC,hD,hfb,hgb⟩ := compact_generator_bounds f hf hfc A K hK hAb e
  have hmb (t : ℝ≥0) (ht : t ≤ B+1) (b : Driver) : ‖M t b‖ ≤ C+D*(B+1) := by
    calc
      _ ≤ ‖f (X t b)‖ + ‖∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)‖ := norm_sub_le _ _
      _ ≤ C+D*(t : ℝ) := add_le_add (hfb _) (by
        simpa only [sub_zero,abs_of_nonneg t.coe_nonneg] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ))
            (fun u _ => hgb (X u.toNNReal b)))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hD)
  have hFa : StronglyAdapted rawFiltration (fun t b => f (X t b)) := fun t =>
    (hf.continuous.measurable.comp (hXm t)).stronglyMeasurable
  have hFm (R : Driver → ℝ≥0)
      (hR : IsStoppingTime rawFiltration (fun b => (R b : WithTop ℝ≥0))) :
      Measurable (fun b => f (X (R b) b)) :=
    (measurable_stoppedValue (hFa.isStronglyProgressive_of_continuous
      (fun b => hf.continuous.comp (hXc b))) hR).mono hR.measurableSpace_le le_rfl
  have hFi (R : Driver → ℝ≥0)
      (hR : IsStoppingTime rawFiltration (fun b => (R b : WithTop ℝ≥0))) :
      Integrable (fun b => f (X (R b) b)) (W.restrict U) :=
    Integrable.of_bound (hFm R hR).aestronglyMeasurable C (Filter.Eventually.of_forall fun b => hfb _)
  have hMi (R : Driver → ℝ≥0)
      (hR : IsStoppingTime rawFiltration (fun b => (R b : WithTop ℝ≥0))) (hRB : ∀ b, R b≤B) :
      Integrable (fun b => M (R b) b) (W.restrict U) :=
    Integrable.of_bound (ExactSLEOptional.stopped_measurable rawFiltration hM hmc R hR).aestronglyMeasurable
      (C+D*(B+1)) (Filter.Eventually.of_forall fun b => hmb _ ((hRB b).trans (le_add_of_nonneg_right zero_le_one)) b)
  have hpw (b : Driver) (hb : b∈U) : f (X (T b) b) - f (X (S b) b) ≤ M (T b) b - M (S b) b := by
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hgc b).intervalIntegrable 0 (S b)) ((hgc b).intervalIntegrable (S b) (T b))
    have hn : (∫ u in (S b : ℝ)..(T b : ℝ), generator f A e (X u.toNNReal b)) ≤ 0 := by
      rw [intervalIntegral.integral_of_le (by exact_mod_cast hST b)]
      apply setIntegral_nonpos measurableSet_Ioc
      intro u hu
      apply hneg b hb u.toNNReal
      · exact_mod_cast (show (S b : ℝ) ≤ (u.toNNReal : ℝ) by rw [Real.coe_toNNReal _ ((S b).coe_nonneg.trans hu.1.le)]; exact hu.1.le)
      · exact (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
    dsimp only [M]
    linarith
  have hcomp := integral_mono_ae ((hFi T hT).sub (hFi S hS))
    ((hMi T hT hTB).sub (hMi S hS (fun b => (hST b).trans (hTB b))))
    ((ae_restrict_mem (hS.measurableSpace_le U hU)).mono fun b hb => hpw b hb)
  simp only [Pi.sub_apply] at hcomp
  rw [integral_sub (hFi T hT) (hFi S hS),
    integral_sub (hMi T hT hTB) (hMi S hS (fun b => (hST b).trans (hTB b)))] at hcomp
  have heq := ExactSLEOptional.setIntegral_optional_sampling rawFiltration hM hmc B
    (C+D*(B+1)) hmb S T hS hT hST hTB U hU
  linarith
end ExactSLEGenerator

namespace ExactSLEPasting
open MeasureTheory
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} [IsFiniteMeasure μ]
 

lemma integral_weighted_le (hm : m ≤ m₀) {f g w : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : StronglyMeasurable[m] w) (hw0 : ∀ ω, 0≤w ω)
    {C : ℝ} (hwb : ∀ ω, ‖w ω‖≤C)
    (h : ∀ U, MeasurableSet[m] U → ∫ ω in U, f ω ∂μ ≤ ∫ ω in U, g ω ∂μ) :
    ∫ ω, w ω*f ω ∂μ ≤ ∫ ω, w ω*g ω ∂μ := by
  have hfm : StronglyMeasurable[m] (μ[f|m]) := stronglyMeasurable_condExp
  have hgm : StronglyMeasurable[m] (μ[g|m]) := stronglyMeasurable_condExp
  have hf' : Integrable (μ[f|m]) (μ.trim hm) := Integrable.trim hm integrable_condExp hfm
  have hg' : Integrable (μ[g|m]) (μ.trim hm) := Integrable.trim hm integrable_condExp hgm
  have hle : μ[f|m] ≤ᵐ[μ] μ[g|m] := by
    apply ae_of_ae_trim hm
    apply ae_le_of_forall_setIntegral_le hf' hg'
    intro U hU _
    rw [← setIntegral_trim hm hfm hU,← setIntegral_trim hm hgm hU,
      setIntegral_condExp hm hf hU,setIntegral_condExp hm hg hU]
    exact h U hU
  have hwm : AEStronglyMeasurable w μ := (hw.mono hm).aestronglyMeasurable
  have hwf := hf.bdd_mul hwm (Filter.Eventually.of_forall hwb)
  have hwg := hg.bdd_mul hwm (Filter.Eventually.of_forall hwb)
  have hwf' := (integrable_condExp (f := f) (m := m) (μ := μ)).bdd_mul hwm (Filter.Eventually.of_forall hwb)
  have hwg' := (integrable_condExp (f := g) (m := m) (μ := μ)).bdd_mul hwm (Filter.Eventually.of_forall hwb)
  have hEqf : ∫ ω, w ω*f ω ∂μ = ∫ ω, w ω*(μ[f|m]) ω ∂μ := by
    rw [← integral_condExp hm]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hw hwf hf)
  have hEqg : ∫ ω, w ω*g ω ∂μ = ∫ ω, w ω*(μ[g|m]) ω ∂μ := by
    rw [← integral_condExp hm]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hw hwg hg)
  rw [hEqf,hEqg]
  exact integral_mono_ae hwf' hwg' (hle.mono fun ω hω => mul_le_mul_of_nonneg_left hω (hw0 ω))
end ExactSLEPasting
namespace ExactSLEPasting
open MeasureTheory Set
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} [IsFiniteMeasure μ]
lemma integral_weighted_le_on_event (hm : m ≤ m₀) {f g w : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet[m] E) (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : StronglyMeasurable[m] w) (hw0 : ∀ ω, 0≤w ω)
    {C : ℝ} (hwb : ∀ ω, ‖w ω‖≤C) (hws : ∀ ω∉E, w ω=0)
    (h : ∀ U, MeasurableSet[m] U → ∫ ω in E∩U, f ω ∂μ ≤ ∫ ω in E∩U, g ω ∂μ) :
    ∫ ω, w ω*f ω ∂μ ≤ ∫ ω, w ω*g ω ∂μ := by
  have hE' : MeasurableSet[m₀] E := hm E hE
  have hcomp : ∫ ω, w ω*E.indicator f ω ∂μ ≤ ∫ ω, w ω*E.indicator g ω ∂μ := by
    apply integral_weighted_le hm (hf.indicator hE') (hg.indicator hE') hw hw0 hwb
    intro U hU
    simp_rw [integral_indicator hE',Measure.restrict_restrict hE']
    exact h U hU
  have he (q : Ω → ℝ) (ω : Ω) : w ω*E.indicator q ω=w ω*q ω := by
    by_cases hq : ω∈E
    · simp [hq]
    · simp [hq,hws ω hq]
  simpa only [he] using hcomp
end ExactSLEPasting

namespace ExactSLEGreen
open ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator
 

theorem discounted_regime_weighted_optional {m : ℕ} (s : Finset (Fin m)) {a ε : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hsize : ε*((s.card:ℝ)-1)≤regK a/2)
    (cap σ off : Fin m → ℝ) (hσ : ∀ i∈s, |σ i|≤regBeta a)
    (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (Z : ℝ≥0 → Driver → RegimeState m) (hZc : ∀ b, Continuous (fun t => Z t b))
    (hZm : ∀ t, Measurable[rawFiltration t] (Z t))
    (A : RegimeState m → RegimeState m) (hAc : Continuous A)
    (K : ℝ) (hK : 0≤K) (hAb : ∀ z, ‖A z‖≤K)
    (hZeq : ∀ (u h : ℝ≥0) b, Z (u+h) b = Z u b + increment u h b • (multiNoise m,0) +
      ∫ t in (u:ℝ)..((u+h:ℝ≥0):ℝ), A (Z t.toNNReal b))
    (S T : Driver → ℝ≥0) (B N : ℝ≥0) (η : ℝ) (hη : 0<η)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b≤T b) (hTB : ∀ b, T b≤B)
    (E : Set Driver) (hE : MeasurableSet[hS.measurableSpace] E)
    (w : Driver → ℝ) (hw : StronglyMeasurable[hS.measurableSpace] w)
    (hw0 : ∀ b, 0≤w b) (C : ℝ) (hwb : ∀ b, ‖w b‖≤C)
    (hws : ∀ b∉E, w b=0)
    (hsafe : ∀ b∈E, ∀ t, S b≤t → t≤T b → ‖Z t b‖≤N ∧
      ∀ i∈s, η≤Y ((Z t b).1 i) ∧ physicalDelta a (cap i) (σ i) (off i) ((Z t b).1 i)≤1)
    (hA : ∀ b∈E, ∀ t, S b≤t → t≤T b →
      (A (Z t b)).2 = regimeDiscount s a ε cap σ off (Z t b).1 ∧
      ∀ i∈s, (A (Z t b)).1 i = physicalDrift a ((Z t b).1 i))
    : ∫ b, w b*discountedProduct s a cap σ off (Z (T b) b) ∂W ≤
      ∫ b, w b*discountedProduct s a cap σ off (Z (S b) b) ∂W := by
  let f := regimeCutoff s a η N cap σ off
  have he : ‖(multiNoise m, (0 : ℝ))‖≤1 := by
    apply max_le _ (by norm_num)
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    simp [multiNoise,noise,Prod.norm_def]
  have hg (b : Driver) (hb : b∈E) (t : ℝ≥0) (hts : S b≤t) (htt : t≤T b) :
      generator f A (multiNoise m,0) (Z t b)≤0 := by
    have hx := hsafe b hb t hts htt
    have hnear := regimeCutoff_eq_near s a η hη N cap σ off (Z t b) hx.1
      (fun i hi => (hx.2 i hi).1)
    have hn : (fun w => fderiv ℝ f w (multiNoise m,0)) =ᶠ[𝓝 (Z t b)]
        (fun w => fderiv ℝ (discountedProduct s a cap σ off) w (multiNoise m,0)) :=
      hnear.fderiv.mono fun w hw => congrArg (fun D : RegimeState m →L[ℝ] ℝ => D (multiNoise m,0)) hw
    change (1/2:ℝ)*fderiv ℝ (fun w => fderiv ℝ f w (multiNoise m,0)) (Z t b) (multiNoise m,0)+
      fderiv ℝ f (Z t b) (A (Z t b))≤0
    rw [hn.fderiv_eq,hnear.fderiv_eq]
    exact discountedProduct_nonpos s ha hε hsize cap σ off (Z t b) (A (Z t b))
      (fun i hi => hη.trans_le (hx.2 i hi).1) (fun i hi => (hx.2 i hi).2) hσ (hA b hb t hts htt)
  have hfc := regimeCutoff_smooth s a η hη N cap σ off
  have hfcompact := regimeCutoff_compact s a η N cap σ off
  have hFa : StronglyAdapted rawFiltration (fun t b => f (Z t b)) := fun t =>
    (hfc.continuous.measurable.comp (hZm t)).stronglyMeasurable
  obtain ⟨D,hDb⟩ := hfcompact.exists_bound_of_continuous hfc.continuous
  have hFi (R : Driver → ℝ≥0)
      (hR : IsStoppingTime rawFiltration (fun b => (R b : WithTop ℝ≥0))) :
      Integrable (fun b => f (Z (R b) b)) W := by
    have hm := (measurable_stoppedValue (hFa.isStronglyProgressive_of_continuous
      (fun b => hfc.continuous.comp (hZc b))) hR).mono hR.measurableSpace_le le_rfl
    exact Integrable.of_bound hm.aestronglyMeasurable D (Filter.Eventually.of_forall fun b => hDb _)
  have hcomp : ∫ b, w b*f (Z (T b) b) ∂W ≤ ∫ b, w b*f (Z (S b) b) ∂W := by
    apply ExactSLEPasting.integral_weighted_le_on_event hS.measurableSpace_le hE
      (hFi T hT) (hFi S hS) hw hw0 hwb hws
    intro U hU
    apply compact_test_optional_on_event W hW Z hZc hZm A hAc K hK hAb
      (multiNoise m,0) he hZeq f hfc hfcompact S T B hS hT hST hTB
      (E∩U) (hE.inter hU)
    intro b hb t hts htt
    exact hg b hb.1 t hts htt
  have heq (b : Driver) (t : ℝ≥0) (hts : S b≤t) (htt : t≤T b) :
      w b*f (Z t b)=w b*discountedProduct s a cap σ off (Z t b) := by
    by_cases hb : b∈E
    · change w b*regimeCutoff s a η N cap σ off (Z t b)=_
      rw [(regimeCutoff_eq_near s a η hη N cap σ off _ (hsafe b hb t hts htt).1
        (fun i hi => ((hsafe b hb t hts htt).2 i hi).1)).eq_of_nhds]
    · simp [hws b hb]
  simpa only [heq _ _ (hST _) le_rfl,heq _ _ le_rfl (hST _)] using hcomp
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLECalculus ExactSLEFiniteTilt Metric
noncomputable def scalarClamp (L x : ℝ) : ℝ := max (-L) (min L x)
lemma scalarClamp_continuous (L : ℝ) : Continuous (scalarClamp L) :=
  continuous_const.max (continuous_const.min continuous_id)
lemma scalarClamp_bounds (L x : ℝ) (hL : 0≤L) : -L ≤ scalarClamp L x ∧ scalarClamp L x ≤ L := by
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
lemma scalarClamp_eq (L x : ℝ) (hx : |x|≤L) : scalarClamp L x=x := by
  rw [scalarClamp,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]
lemma scalarClamp_idem (L x : ℝ) (hL : 0≤L) : scalarClamp L (scalarClamp L x)=scalarClamp L x :=
  scalarClamp_eq L _ (abs_le.mpr (scalarClamp_bounds L x hL))
noncomputable def regimeClamp (η : ℝ) (N : ℝ≥0) (v : State) : State :=
  (⟨scalarClamp N (X v),max η (min ((N:ℝ)+η+1) (Y v))⟩,scalarClamp N (J v))
lemma regimeClamp_continuous (η : ℝ) (N : ℝ≥0) : Continuous (regimeClamp η N) := by
  have hc : Continuous (fun v : State =>
      ((scalarClamp N (X v) : ℂ) + (Complex.ofReal (max η (min ((N:ℝ)+η+1) (Y v))))*Complex.I,
        scalarClamp N (J v))) :=
    ((Complex.continuous_ofReal.comp ((scalarClamp_continuous N).comp X.continuous)).add
      ((Complex.continuous_ofReal.comp
        (continuous_const.max (continuous_const.min Y.continuous))).mul_const Complex.I)).prodMk
          ((scalarClamp_continuous N).comp J.continuous)
  convert hc using 1
  funext v
  apply Prod.ext
  · apply Complex.ext <;> simp [regimeClamp]
  · rfl
lemma regimeClamp_height (η : ℝ) (N : ℝ≥0) (v : State) : η≤Y (regimeClamp η N v) :=
  le_max_left _ _
lemma regimeClamp_idem (η : ℝ) (N : ℝ≥0) (v : State) :
    regimeClamp η N (regimeClamp η N v)=regimeClamp η N v := by
  have h : η≤(N:ℝ)+η+1 := by linarith [N.coe_nonneg]
  apply Prod.ext
  · apply Complex.ext
    · exact scalarClamp_idem _ _ N.coe_nonneg
    · change max η (min ((N:ℝ)+η+1) (max η (min ((N:ℝ)+η+1) (Y v)))) = _
      rw [min_eq_right (max_le h (min_le_left _ _)),max_eq_right (le_max_left _ _)]
      rfl
  · exact scalarClamp_idem _ _ N.coe_nonneg
lemma regimeClamp_bound (η : ℝ) (N : ℝ≥0) (v : State) :
    ‖regimeClamp η N v‖≤2*(N:ℝ)+|η|+1 := by
  have hr : |scalarClamp N (X v)|≤N := abs_le.mpr (scalarClamp_bounds N _ N.coe_nonneg)
  have hj : |scalarClamp N (J v)|≤N := abs_le.mpr (scalarClamp_bounds N _ N.coe_nonneg)
  have hy : |max η (min ((N:ℝ)+η+1) (Y v))|≤(N:ℝ)+|η|+1 := by
    apply abs_le.mpr
    constructor
    · calc
        -((N:ℝ)+|η|+1) ≤ -|η| := by linarith [N.coe_nonneg]
        _ ≤ η := neg_abs_le η
        _ ≤ _ := le_max_left _ _
    · apply max_le
      · exact (le_abs_self η).trans (by linarith [N.coe_nonneg])
      · exact (min_le_left _ _).trans (by linarith [le_abs_self η])
  rw [Prod.norm_def]
  apply max_le
  · exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
      change |scalarClamp N (X v)|+|max η (min ((N:ℝ)+η+1) (Y v))|≤_
      linarith)
  · change ‖scalarClamp N (J v)‖≤_
    rw [Real.norm_eq_abs]
    linarith [abs_nonneg η,N.coe_nonneg]
lemma regimeClamp_eq (η : ℝ) (N : ℝ≥0) (v : State) (hη : 0<η)
    (hn : ‖v‖≤N) (hy : η≤Y v) : regimeClamp η N v=v := by
  have hx : |X v|≤N := (Complex.abs_re_le_norm v.1).trans ((le_max_left ‖v.1‖ ‖v.2‖).trans hn)
  have hj : |J v|≤N := (le_max_right ‖v.1‖ ‖v.2‖).trans hn
  have hu : Y v≤(N:ℝ)+η+1 := by
    have h : Y v ≤ N := (Complex.im_le_norm v.1).trans ((le_max_left ‖v.1‖ ‖v.2‖).trans hn)
    linarith
  apply Prod.ext
  · apply Complex.ext
    · exact scalarClamp_eq _ _ hx
    · change max η (min ((N:ℝ)+η+1) (Y v))=Y v
      rw [min_eq_right hu,max_eq_right hy]
  · exact scalarClamp_eq _ _ hj

lemma regimeDiscount_continuousAt {m : ℕ} (s : Finset (Fin m)) (a ε : ℝ)
    (cap σ off : Fin m → ℝ) (v : Fin m → State) (hy : ∀ i∈s, 0<Y (v i)) :
    ContinuousAt (regimeDiscount s a ε cap σ off) v := by
  have hc (i) (hi : i∈s) : ContinuousAt (fun w : Fin m → State => physicalClock a (cap i) (w i)) v :=
    (physicalClock_smooth a (cap i) (v i) (hy i hi)).continuousAt.comp_of_eq (continuous_apply i).continuousAt rfl
  have hd (i) (hi : i∈s) : ContinuousAt (fun w : Fin m → State => physicalDelta a (cap i) (σ i) (off i) (w i)) v :=
    (continuousAt_const.add (continuousAt_const.mul (hc i hi))).rexp
  have hV (i) (hi : i∈s) : ContinuousAt (fun w : Fin m → State => physicalV (w i)) v :=
    ((Y.continuous.continuousAt.div ((X.continuous.pow 2).add (Y.continuous.pow 2)).continuousAt (Q_pos (hy i hi)).ne').comp_of_eq
      (continuous_apply i).continuousAt rfl)
  unfold regimeDiscount
  apply ContinuousAt.add
  · exact continuousAt_const.mul (tendsto_finsetSum s fun i hi => (hd i hi).mul ((hV i hi).pow 2))
  · apply ContinuousAt.mul continuousAt_const
    apply tendsto_finsetSum s
    intro i hi
    apply tendsto_finsetSum (s.erase i)
    intro j hj
    exact ((((hd i hi).mul (hd j (Finset.mem_of_mem_erase hj))).rpow_const
      (p := -regM a) (Or.inl (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne')).mul
        (hV i hi)).mul (hV j (Finset.mem_of_mem_erase hj))

noncomputable def regimeDiscountCut {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) (v : Fin m → State) : ℝ :=
  regimeDiscount s a ε cap σ off (fun i => regimeClamp η N (v i))
lemma regimeDiscountCut_continuous {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) : Continuous (regimeDiscountCut s a ε η N cap σ off) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  exact (regimeDiscount_continuousAt s a ε cap σ off _
    (fun i _ => hη.trans_le (regimeClamp_height η N (v i)) )).comp_of_eq
      ((continuous_pi fun i => (regimeClamp_continuous η N).comp (continuous_apply i)).continuousAt) rfl
lemma regimeDiscountCut_bound {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) : ∃ K : ℝ, 0≤K ∧ ∀ v, ‖regimeDiscountCut s a ε η N cap σ off v‖≤K := by
  have hc := regimeDiscountCut_continuous s a ε η hη N cap σ off
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0 : Fin m → State) (2*(N:ℝ)+|η|+1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 0,le_max_right _ _,fun v => ?_⟩
  have hv : (fun i => regimeClamp η N (v i))∈closedBall (0 : Fin m → State) (2*(N:ℝ)+|η|+1) := by
    rw [mem_closedBall_zero_iff]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact regimeClamp_bound η N (v i)
  have h := hK (fun i => regimeClamp η N (v i)) hv
  have he : regimeDiscountCut s a ε η N cap σ off (fun i => regimeClamp η N (v i))=
      regimeDiscountCut s a ε η N cap σ off v := by
    simp only [regimeDiscountCut,regimeClamp_idem]
  exact (he ▸ h).trans (le_max_left _ _)
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLECalculus ExactSLEFiniteTilt
noncomputable def vectorState {m : ℕ} (a η : ℝ) (hη : 0<η) (z : Fin m → ℂ)
    (t : ℝ≥0) (b : Driver) : Fin m → State := fun i => localState a η hη (z i) t b
lemma vectorState_continuous {m : ℕ} (a η : ℝ) (hη : 0<η) (z : Fin m → ℂ) (b : Driver) :
    Continuous (fun t => vectorState a η hη z t b) :=
  continuous_pi fun i => localState_continuous a η hη (z i) b
lemma vectorState_adapted {m : ℕ} (a η : ℝ) (hη : 0<η) (z : Fin m → ℂ) (t : ℝ≥0) :
    Measurable[rawFiltration t] (vectorState a η hη z t) := by
  let : MeasurableSpace Driver := rawFiltration t
  exact Measurable.of_eval fun index => localState_adapted a η hη (z index) t
noncomputable def regimeDrift {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) (v : RegimeState m) : RegimeState m :=
  (fun i => cutoffDrift a η (v.1 i),regimeDiscountCut s a ε η N cap σ off v.1)
lemma regimeDrift_continuous {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) : Continuous (regimeDrift s a ε η N cap σ off) :=
  (continuous_pi fun i => (cutoffDrift_lipschitz a η hη).continuous.comp
    ((continuous_apply i).comp continuous_fst)).prodMk
      ((regimeDiscountCut_continuous s a ε η hη N cap σ off).comp continuous_fst)
lemma regimeDrift_bound {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ) (hη : 0<η) (N : ℝ≥0)
    (cap σ off : Fin m → ℝ) : ∃ K : ℝ, 0≤K ∧ ∀ v, ‖regimeDrift s a ε η N cap σ off v‖≤K := by
  obtain ⟨K,hK,hKb⟩ := regimeDiscountCut_bound s a ε η hη N cap σ off
  refine ⟨max (max (|a|/η) (|a|/η^2)) K,(le_max_right _ _).trans' hK,fun v => ?_⟩
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg ((le_max_left _ _).trans' (by positivity))).mpr
    intro i
    exact (cutoffDrift_bound a η hη _).trans (le_max_left _ _)
  · exact (hKb _).trans (le_max_right _ _)
end ExactSLEGreen
end

end OAI
