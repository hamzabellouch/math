import Mathlib
import OAI.Probability.Perceptron.Variational.DecoratedTiltTotal

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma normalized_product_tilt_lintegral {S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [SFinite ν] [SFinite ρ]
    {f : S → ℝ≥0∞} {g : S×T → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcf : c ≠ ⊤)
    (hrow : ∀ s, (∫⁻ t, g (s,t) ∂ρ) = c)
    {H : S×T → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H p ∂normalizedMeasure ((ν.prod ρ).withDensity (fun p => f p.1*g p))) =
    ∫⁻ s, (∫⁻ t, H (s,t) ∂normalizedMeasure (ρ.withDensity (fun t => g (s,t))))
      ∂normalizedMeasure (ν.withDensity f) := by
  have hfg : Measurable (fun p : S×T => f p.1*g p) := (hf.comp measurable_fst).mul hg
  have hgh : Measurable (fun p : S×T => g p*H p) := hg.mul hH
  have hfgH : Measurable (fun p : S×T => (f p.1*g p)*H p) := hfg.mul hH
  have hgs (s : S) : Measurable (fun t => g (s,t)) := hg.comp (measurable_const.prodMk measurable_id)
  have hHs (s : S) : Measurable (fun t => H (s,t)) := hH.comp (measurable_const.prodMk measurable_id)
  have hmass : ((ν.prod ρ).withDensity (fun p => f p.1*g p)) univ =
      (ν.withDensity f) univ*c := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      lintegral_prod _ hfg.aemeasurable]
    simp_rw [lintegral_const_mul _ (hgs _),hrow]
    rw [lintegral_mul_const _ hf,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hi (s : S) : (∫⁻ t, H (s,t) ∂normalizedMeasure (ρ.withDensity (fun t => g (s,t)))) =
      c⁻¹ * ∫⁻ t, g (s,t)*H (s,t) ∂ρ := by
    rw [normalizedMeasure,lintegral_smul_measure,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hrow,
      lintegral_withDensity_eq_lintegral_mul ρ
        (hgs s) (hHs s)]
    rfl
  have hJ : Measurable (fun s => ∫⁻ t, g (s,t)*H (s,t) ∂ρ) :=
    (hg.mul hH).lintegral_prod_right
  simp_rw [hi]
  rw [normalizedMeasure,lintegral_smul_measure,hmass,
    lintegral_withDensity_eq_lintegral_mul _ hfg hH]
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ hfgH.aemeasurable,
    normalizedMeasure,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hf (hJ.const_mul _)]
  simp only [smul_eq_mul,Pi.mul_apply]
  have hinner (s : S) : (∫⁻ t, f s*(g (s,t)*H (s,t)) ∂ρ) =
      f s*(∫⁻ t, g (s,t)*H (s,t) ∂ρ) :=
    lintegral_const_mul (f s) (hgs s |>.mul (hHs s))
  simp_rw [mul_assoc,hinner]
  rw [ENNReal.mul_inv (Or.inr hcf) (Or.inr hc0)]
  simp_rw [← mul_assoc, mul_right_comm (f _) c⁻¹]
  have hfj : Measurable (fun s => f s * ∫⁻ t, g (s,t)*H (s,t) ∂ρ) := hf.mul hJ
  rw [lintegral_mul_const _ hfj]
  ac_rfl

lemma exponential_product_tilt_lintegral {S T : Type*}
    [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [SFinite ν] [SFinite ρ]
    {f : S → ℝ} {g : S×T → ℝ}
    (hf : Measurable f) (hg : Measurable g) (b : ℝ) {c : ℝ}
    (hc : 0 < c)
    (hI : ∀ s, Integrable (fun t => Real.exp (b*g (s,t))) ρ)
    (hrow : ∀ s, (∫ t, Real.exp (b*g (s,t)) ∂ρ) = c)
    {H : S×T → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H p ∂exponentialMarkTilt (ν.prod ρ) b (fun p => f p.1+g p)) =
    ∫⁻ s, (∫⁻ t, H (s,t) ∂exponentialMarkTilt ρ b (fun t => g (s,t)))
      ∂exponentialMarkTilt ν b f := by
  have he (p : S×T) : ENNReal.ofReal (Real.exp (b*(f p.1+g p))) =
      ENNReal.ofReal (Real.exp (b*f p.1))*ENNReal.ofReal (Real.exp (b*g p)) := by
    rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold exponentialMarkTilt
  simp_rw [he]
  apply normalized_product_tilt_lintegral ν ρ
    (hf.const_mul b |>.exp.ennreal_ofReal) (hg.const_mul b |>.exp.ennreal_ofReal)
    (c := ENNReal.ofReal c) (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top
  · intro s
    rw [← ofReal_integral_eq_lintegral_ofReal (hI s)
      (ae_of_all _ fun t => (Real.exp_pos _).le),hrow s]
  · exact hH

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma decoratedBiasedLaw_absolutelyContinuous (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ) (x : X) (a : ℝ) :
    decoratedBiasedLaw ν step n z F x a ≪ (decoratedCascadeLaw ν n z) :=
  Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

lemma decoratedRootTilt_disintegrate (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X)
    (H : S×DecoratedCascade S n → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p, H p ∂exponentialMarkTilt
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) (z 0)
      (fun p => decoratedRootPotential step n F (x,p))) =
    ∫⁻ s, (∫⁻ C, H (s,C) ∂decoratedBiasedLaw ν step n
      (fun i => z i.succ) (fun i => F i.succ) (step (x,s)) (z 0))
      ∂exponentialMarkTilt ν (z 0) (fun s => F 0 (x,s)) := by
  have htail : StrictMono (fun i : Fin n => z i.succ) :=
    fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
  have hrange : ∀ i : Fin n, z 0 < z i.succ := fun i => hz (by simp)
  have hC := cascadeLogTotalMoment_integrable n (fun i => z i.succ) htail
    (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) hrange
  have hG : Measurable (fun p : S×DecoratedCascade S n =>
      Real.log (decoratedWeightedTotal step n (fun i => F i.succ) (step (x,p.1),p.2))) :=
    ((decoratedWeightedTotal_measurable step hs n _ (fun i => hF i.succ)).comp
      ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)).log
  have he := exponential_product_tilt_lintegral (ν : Measure S)
    (decoratedCascadeLaw ν n (fun i => z i.succ) : Measure (DecoratedCascade S n))
    ((hF 0).comp ((measurable_const (a := x)).prodMk measurable_id)) hG (z 0)
    (integral_exp_pos hC)
    (fun s => decoratedLogTotalMoment_integrable ν step hs n (fun i => z i.succ)
      htail (fun i => hz0 i.succ) (fun i => hz1 i.succ) (fun i => F i.succ)
      (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ)
      (step (x,s)) (z 0) hrange)
    (fun s => decoratedLogTotalMoment_eq ν step hs n (fun i => z i.succ)
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (fun i => F i.succ)
      (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ)
      (step (x,s)) (z 0)) hH
  have hb (s : S) := decoratedBiasedLaw_eq_exponentialTilt ν step hs n
    (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
    (fun i => F i.succ) (fun i => hF i.succ) (fun i => hI i.succ)
    (fun i => hM i.succ) (step (x,s)) (z 0)
  simp_rw [hb]
  exact he

lemma decoratedRootBlock_factor (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X)
    (a : ℝ) (ha : a < z 0)
    (ns : List (ℕ×(S×DecoratedCascade S n → ℝ≥0∞))) (hne : ns ≠ [])
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) :
    (∫⁻ η, markedBlockProbability ns
      ((markedStableCountKernel η).map (logMarkShift
        (centeredLogMark ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))
          (z 0) (fun p => decoratedRootPotential step n F (x,p))))) (Fin.elim0 : Fin 0 → ℝ)
      ∂decoratedBiasedLaw ν step (n+1) z F x a) =
    (ns.map (fun nf => ∫⁻ s, (∫⁻ C, nf.2 (s,C) ∂decoratedBiasedLaw ν step n
      (fun i => z i.succ) (fun i => F i.succ) (step (x,s)) (z 0))
        ∂exponentialMarkTilt ν (z 0) (fun s => F 0 (x,s)))).prod *
      (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η (Fin.elim0 : Fin 0 → ℝ)
        ∂stableTotalBiasedLaw a (z 0)) := by
  have hreg := (decoratedBiasedLaw_absolutelyContinuous ν step (n+1) z F x a).ae_eq
    (markedStableCountKernel_ae_eq
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ) : Measure (DecoratedCascade S n)))
      (hz0 0) (hz1 0))
  let G : Measure (ℝ×(S×DecoratedCascade S n)) → ℝ≥0∞ := fun η =>
    markedBlockProbability ns (η.map (logMarkShift (centeredLogMark
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) (z 0)
      (fun p => decoratedRootPotential step n F (x,p))))) (Fin.elim0 : Fin 0 → ℝ)
  have he := lintegral_congr_ae (hreg.mono (fun η hη => congrArg G hη))
  dsimp [G] at he
  have hR : Measurable (fun p : S×DecoratedCascade S n =>
      decoratedRootPotential step n F (x,p)) :=
    (decoratedRootPotential_measurable step hs n F hF).comp
      (measurable_const.prodMk measurable_id)
  rw [he,decoratedBiasedLaw_succ_eq_weighted ν step hs n z hz hz0 hz1 F hF hI hM x a,
    weightedRootBlock_factor _ (hz0 0) (hz1 0) ha
      hR
      (decoratedRootPotential_integrable ν step hs n z hz hz0 hz1 F hF hI hM x) ns hne hn hm]
  congr 2
  apply List.map_congr_left
  intro nf hnf
  exact decoratedRootTilt_disintegrate ν step hs n z hz hz0 hz1 F hF hI hM x nf.2 (hm nf hnf)

end SphericalPerceptronFreeEnergy

end

end OAI
