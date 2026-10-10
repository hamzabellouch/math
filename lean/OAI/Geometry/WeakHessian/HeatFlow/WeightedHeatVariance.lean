import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatSobolev

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile212
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.weighted_heat_variance_hasDerivAt {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {f Af ξ Bξ : Lp ℝ 2 (exponentialMeasure m V)}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    {Cf CAf Cξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m V,|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m V,|Af x| ≤ CAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m V,|ξ x| ≤ Cξ)
    {t T : ℝ} (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ x,(cheegerHeat h (T-s) f x)^2*cheegerHeat h s ξ x
      ∂exponentialMeasure m V)
      (2*(∫ x,cheegerHeat h t ξ x*gamma (exponentialMeasure m V)
        (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) f) x ∂exponentialMeasure m V)) t := by
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hg {u A : Lp ℝ 2 ν} (hu : Q.IsFormGenerator u A) (s : ℝ) :
      IsLaplacian ν (cheegerHeat h s u) (cheegerHeat h s A) :=
    (hrcd.weighted_formGenerator_iff hfin o hBV h _ _).mpr (Q.formGenerator_heat ν hu s)
  obtain ⟨n,hn⟩ := exists_nat_ge Cf
  have hb : ∀ᶠ s in 𝓝 t,∀ᵐ x ∂ν,|cheegerHeat h (T-s) f x| ≤ (n:ℝ) := by
    filter_upwards [eventually_lt_nhds htT] with s hs
    exact (cheegerHeat_bounded h (sub_nonneg.mpr hs.le) hCf f hfb).mono fun x hx => hx.trans hn
  have HD := hasDerivAt_integral_square_mul
    (cheegerHeat_backwards_derivative hnfin h hf htT)
    (cheegerHeat_deriv_at_generator hnfin h hξ ht) n hb
    (cheegerHeat_bounded h ht.le hCξ ξ hξb)
  have HE := (hg hf (T-t)).square_gamma_pairing_ae hnfin hnpar (hg hξ t)
    (hrcd.weighted_heat_boundedLipschitzRepresentative hN hfull hfin o hV hBV h hf hCf hCAf hfb hAfb
      (sub_nonneg.mpr htT.le)) (cheegerHeat_bounded h ht.le hCξ ξ hξb)
  have Hneg := integral_triple_neg_middle (cheegerHeat h (T-t) f)
    (cheegerHeat h (T-t) Af) (cheegerHeat h t ξ)
  convert HD using 1
  rw [Hneg]
  linarith

lemma WeakHessianUpperBound.rcd_weighted_reverse_poincare_core {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ Bξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    {Cf CAf Cξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    (2*(∫ s in (0:ℝ)..T,Real.exp (2*(K-a*CG)*s)))*
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x))
        (cheegerHeat h T f) (cheegerHeat h T f) x ∂exponentialMeasure m (fun x => a*F x)) ≤
      (∫ x,(f x)^2*cheegerHeat h T ξ x ∂exponentialMeasure m (fun x => a*F x))-
      (∫ x,(cheegerHeat h T f x)^2*ξ x ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let I := fun s => ∫ x,(cheegerHeat h (T-s) f x)^2*cheegerHeat h s ξ x ∂ν
  let E := fun s => ∫ x,cheegerHeat h s ξ x*gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  let E0 := ∫ x,ξ x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν
  have hb : ContinuousOn (fun s => cheegerHeat h (T-s) f) (Icc 0 T) :=
    (cheegerHeat_continuousOn hnfin h f).comp (continuous_const.sub continuous_id).continuousOn
      (fun _ hs => sub_nonneg.mpr hs.2)
  have hp : ContinuousOn (fun s => cheegerHeat h s ξ) (Icc 0 T) :=
    (cheegerHeat_continuousOn hnfin h ξ).mono Icc_subset_Ici_self
  obtain ⟨n,hn⟩ := exists_nat_ge Cf
  have hc : ContinuousOn I (Icc 0 T) := continuousOn_integral_square_mul hb hp n
    (fun s hs => (cheegerHeat_bounded h (sub_nonneg.mpr hs.2) hCf f hfb).mono fun x hx => hx.trans hn)
  have hd : ∀ s ∈ Ioo 0 T,HasDerivWithinAt I (2*E s) (Ioi s) s := fun s hs =>
    (hrcd.weighted_heat_variance_hasDerivAt hN hfull hfin o hV hVB h hf hξ hCf hCAf hCξ
      hfb hAfb hξb hs.1 hs.2).hasDerivWithinAt
  have hEL : ∀ s ∈ Ioo 0 T,Real.exp (2*(K-a*CG)*s)*E0 ≤ E s := by
    intro s hs
    have hgs : Sobolev ν (cheegerHeat h (T-s) f) :=
      ((hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr (Q.formGenerator_heat ν hf (T-s))).1
    have H := hHess.rcd_weighted_heat_gradient_sobolev hN hrcd hfull hfin o hF hFb hGb hGc ha h
      hgs hCξ hξb hξ0 hs.1.le
    have he : cheegerHeat h s (cheegerHeat h (T-s) f) = cheegerHeat h T f := by
      rw [← mul_apply_eq_comp,← cheegerHeat_add h hs.1.le (sub_nonneg.mpr hs.2.le)]
      congr 2; ring
    rw [he] at H
    change E0 ≤ Real.exp (-(2*(K-a*CG))*s)*E s at H
    have H' := mul_le_mul_of_nonneg_left H (Real.exp_pos (2*(K-a*CG)*s)).le
    have hee : Real.exp (2*(K-a*CG)*s)*Real.exp (-(2*(K-a*CG))*s) = 1 := by
      rw [← Real.exp_add, ← add_mul, add_neg_cancel, zero_mul, Real.exp_zero]
    simpa only [← mul_assoc,hee,one_mul] using H'
  have hi : IntegrableOn (fun s => 2*(Real.exp (2*(K-a*CG)*s)*E0)) (Icc 0 T) :=
    (continuous_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const)).continuousOn.integrableOn_Icc
  have H := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT hc hd hi
    (fun s hs => mul_le_mul_of_nonneg_left (hEL s hs) (by norm_num : (0:ℝ) ≤ 2))
  simp only [intervalIntegral.integral_const_mul,intervalIntegral.integral_mul_const,
    I,sub_self,sub_zero,cheegerHeat_zero,one_apply_eq_self] at H
  change (2*(∫ s in (0:ℝ)..T,Real.exp (2*(K-a*CG)*s)))*E0 ≤ _
  nlinarith only [H]
end WeakHessian

end
end InlinedFile212

end OAI
