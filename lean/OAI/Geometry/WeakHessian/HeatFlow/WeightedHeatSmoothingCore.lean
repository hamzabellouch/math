import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedReversePoincare

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile214
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_reverse_poincare_integral {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf CAf Cξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    (hξi : Integrable ξ (exponentialMeasure m (fun x => a*F x)))
    {T : ℝ} (hT : 0 ≤ T) :
    (2*T*Real.exp (-2*|K-a*CG| *T))*
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x))
        (cheegerHeat h T f) (cheegerHeat h T f) x ∂exponentialMeasure m (fun x => a*F x)) ≤
      Cf^2*(∫ x,ξ x ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hmass := cheegerHeat_submass hnfin o h ξ hξ0 hξi hT
  have hpos := cheegerHeat_nonneg h hT ξ hξ0
  have hsq : MemLp (fun x => (f x)^2) 2 ν := by
    simpa only [pow_two] using memLp_mul_bounded (Lp.memLp f) (Lp.aestronglyMeasurable f) hfb
  have hb : (∫ x,(f x)^2*cheegerHeat h T ξ x ∂ν) ≤ Cf^2*(∫ x,ξ x ∂ν) := by
    calc
      _ ≤ ∫ x,Cf^2*cheegerHeat h T ξ x ∂ν := by
        apply integral_mono_ae (hsq.integrable_mul (Lp.memLp _)) (hmass.1.const_mul _)
        filter_upwards [hfb,hpos] with x hx hp
        exact mul_le_mul_of_nonneg_right (by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hCf).mpr hx) hp
      _ = Cf^2*(∫ x,cheegerHeat h T ξ x ∂ν) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass.2 (sq_nonneg _)
  have hi : 0 ≤ ∫ x,(cheegerHeat h T f x)^2*ξ x ∂ν :=
    integral_nonneg_of_ae (hξ0.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
  have he : 0 ≤ ∫ x,ξ x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [hξ0,gamma_self (m := ν) (cheegerHeat h T f : X → ℝ)] with x hx hg
    rw [hg]; exact mul_nonneg hx (sq_nonneg _)
  have H := hHess.rcd_weighted_reverse_poincare_test hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hf hCf hCAf hCξ hfb hAfb hξb hξ0 hT
  have Hc := mul_le_mul_of_nonneg_right (weighted_reverse_coefficient_lower (K-a*CG) hT) he
  dsimp only [ν,V] at hb hi he Hc
  linarith only [H,Hc,hb,hi]

lemma WeakHessianUpperBound.rcd_weighted_reverse_poincare_pointwise {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf CAf : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),
      (2*T*Real.exp (-2*|K-a*CG| *T))*
        (weakGradient (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T f : X → ℝ) x)^2 ≤ Cf^2 := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hS := ((hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr
    ((cheeger_closedQuadraticEnergy h).formGenerator_heat ν hf T)).1
  let c := 2*T*Real.exp (-2*|K-a*CG| *T)
  have hgi : Integrable (fun x => c*(weakGradient ν (cheegerHeat h T f : X → ℝ) x)^2) ν :=
    hS.2.2.integrable_sq.const_mul c
  have H := ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    (f := fun x => Cf^2-c*(weakGradient ν (cheegerHeat h T f : X → ℝ) x)^2)
    (fun S hS hs => (integrableOn_const (C := Cf^2) hs.ne).sub hgi.integrableOn) (by
      intro S hS hs
      let hu2 := memLp_indicator_const (μ := ν) 2 hS (1:ℝ) (Or.inr hs.ne)
      let u := hu2.toLp (S.indicator (fun _ : X => (1:ℝ)))
      have hue : u =ᵐ[ν] S.indicator (fun _ : X => (1:ℝ)) := hu2.coeFn_toLp
      have hui : Integrable u ν :=
        ((integrableOn_const (C := (1:ℝ)) hs.ne).integrable_indicator hS).congr hue.symm
      have hun : ∀ᵐ x ∂ν,0 ≤ u x := hue.mono fun x hx => hx ▸ indicator_nonneg (fun _ _ => zero_le_one) x
      have hub : ∀ᵐ x ∂ν,|u x| ≤ 1 := by
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have HH := hHess.rcd_weighted_reverse_poincare_integral hN hrcd hfull hfin o hF hFb hGb hGc ha h
        hf hCf hCAf zero_le_one hfb hAfb hub hun hui hT
      have hg : (∫ x,u x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν) =
          ∫ x,u x*(weakGradient ν (cheegerHeat h T f : X → ℝ) x)^2 ∂ν :=
        integral_congr_ae ((EventuallyEq.rfl).fun_mul (gamma_self (m := ν) (cheegerHeat h T f : X → ℝ)))
      rw [hg] at HH
      have hpair (g : X → ℝ) : (∫ x,u x*g x ∂ν) = ∫ x in S,g x ∂ν := by
        rw [← integral_indicator hS]
        apply integral_congr_ae
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have hmass : (∫ x,u x ∂ν) = ∫ x in S,(1:ℝ) ∂ν := by simpa only [mul_one] using hpair (fun _ => (1:ℝ))
      rw [hpair,hmass] at HH
      rw [integral_sub (integrableOn_const (C := Cf^2) hs.ne) hgi.integrableOn,integral_const_mul]
      simpa only [c,integral_const,smul_eq_mul,mul_one,one_mul,mul_comm] using sub_nonneg.mpr HH)
  exact H.mono fun x hx => sub_nonneg.mp hx

lemma WeakHessianUpperBound.rcd_weighted_heat_smoothing_core {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf CAf : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    {T : ℝ} (hT : 0 < T) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (Real.sqrt (Cf^2/(2*T*Real.exp (-2*|K-a*CG| *T))))) g ∧
      g =ᵐ[exponentialMeasure m (fun x => a*F x)] cheegerHeat h T f := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hS := ((hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr
    ((cheeger_closedQuadraticEnergy h).formGenerator_heat ν hf T)).1
  apply hrcd.weighted_sobolev_to_lipschitz hN hfull hfin hVB hS.2.1.1
    (weakGradient_isMinimal hS.2.1.2).1
  have H := hHess.rcd_weighted_reverse_poincare_pointwise hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hf hCf hCAf hfb hAfb hT.le
  filter_upwards [H] with x hx
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have hc : 0 < 2*T*Real.exp (-2*|K-a*CG| *T) := by positivity
  have HH : (weakGradient ν (cheegerHeat h T f : X → ℝ) x)^2 ≤ Cf^2/(2*T*Real.exp (-2*|K-a*CG| *T)) :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hx)
  change weakGradient ν (cheegerHeat h T f : X → ℝ) x ≤ Real.sqrt (Cf^2/(2*T*Real.exp (-2*|K-a*CG| *T)))
  have hroot := Real.sq_sqrt (show 0 ≤ Cf^2/(2*T*Real.exp (-2*|K-a*CG| *T)) by positivity)
  nlinarith only [HH,hroot,Real.sqrt_nonneg (Cf^2/(2*T*Real.exp (-2*|K-a*CG| *T)))]
end WeakHessian

end
end InlinedFile214

end OAI
