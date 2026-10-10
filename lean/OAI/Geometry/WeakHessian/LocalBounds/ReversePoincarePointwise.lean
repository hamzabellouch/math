import Mathlib
import OAI.Geometry.WeakHessian.Calculus.ReversePoincareIntegral
import OAI.Geometry.WeakHessian.Sobolev.CDSobolevLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile139
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_reversePoincare_pointwise {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) (n : ℕ) (hfb : ∀ x,|f x| ≤ (n:ℝ))
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂m,2*t*Real.exp (-2*|K| *t)*(weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2 ≤ (n:ℝ)^2 := by
  obtain ⟨A,hA,-⟩ := cheegerHeat_deriv_at_positive hfin h (hf2.toLp f) ht
  have hS := (hrcd.1.global_isLaplacian_of_formGenerator hfin o h _ _ hA).1
  let c := 2*t*Real.exp (-2*|K| *t)
  have hgi : Integrable (fun x => c*(weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2) m :=
    ((memLp_two_iff_integrable_sq hS.2.2.aestronglyMeasurable).mp hS.2.2).const_mul c
  have H := ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    (f := fun x => (n:ℝ)^2-c*(weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2)
    (fun S _hS hs => (integrableOn_const (C := (n:ℝ)^2) hs.ne).sub hgi.integrableOn) (by
      intro S hS hs
      let hu2 := memLp_indicator_const (μ := m) 2 hS (1:ℝ) (Or.inr hs.ne)
      let u := hu2.toLp (S.indicator (fun _ : X => (1:ℝ)))
      have hue : u =ᵐ[m] S.indicator (fun _ : X => (1:ℝ)) := hu2.coeFn_toLp
      have hui : Integrable u m :=
        ((integrableOn_const (C := (1:ℝ)) hs.ne).integrable_indicator hS).congr hue.symm
      have hun : ∀ᵐ x ∂m,0 ≤ u x := hue.mono fun x hx => hx ▸ indicator_nonneg (fun _ _ => zero_le_one) x
      have hub : ∀ᵐ x ∂m,|u x| ≤ 1 := by
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have HH := hrcd.cheegerHeat_reversePoincare_integral hN hfull hfin h o hf hf2 n hfb u hui hun zero_le_one hub ht
      have hpair (g : X → ℝ) : (∫ x,u x*g x ∂m) = ∫ x in S,g x ∂m := by
        rw [← integral_indicator hS]
        apply integral_congr_ae
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have hmass : (∫ x,u x ∂m) = ∫ x in S,(1:ℝ) ∂m := by simpa only [mul_one] using hpair (fun _ => (1:ℝ))
      rw [hpair,hmass] at HH
      rw [integral_sub (integrableOn_const (C := (n:ℝ)^2) hs.ne) hgi.integrableOn,integral_const_mul]
      simpa only [c,integral_const,smul_eq_mul,mul_one,one_mul,mul_comm] using sub_nonneg.mpr HH)
  exact H.mono fun x hx => sub_nonneg.mp hx

lemma RCD.cheegerHeat_reversePoincare_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) (n : ℕ) (hfb : ∀ x,|f x| ≤ (n:ℝ))
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (Real.sqrt ((n:ℝ)^2/(2*t*Real.exp (-2*|K| *t))))) g ∧
      g =ᵐ[m] cheegerHeat h t (hf2.toLp f) := by
  obtain ⟨A,hA,-⟩ := cheegerHeat_deriv_at_positive hfin h (hf2.toLp f) ht
  have hS := (hrcd.1.global_isLaplacian_of_formGenerator hfin o h _ _ hA).1
  apply hrcd.1.sobolev_to_lipschitz hN hfull hfin hS.2.1.1
    (weakGradient_isMinimal hS.2.1.2).1
  have H := hrcd.cheegerHeat_reversePoincare_pointwise hN hfull hfin h o hf hf2 n hfb ht
  filter_upwards [H] with x hx
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have hc : 0 < 2*t*Real.exp (-2*|K| *t) := by positivity
  have HH : (weakGradient m (cheegerHeat h t (hf2.toLp f) : X → ℝ) x)^2 ≤ (n:ℝ)^2/(2*t*Real.exp (-2*|K| *t)) :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hx)
  have hroot := Real.sq_sqrt (show 0 ≤ (n:ℝ)^2/(2*t*Real.exp (-2*|K| *t)) by positivity)
  nlinarith only [HH,hroot,Real.sqrt_nonneg ((n:ℝ)^2/(2*t*Real.exp (-2*|K| *t)))]
end WeakHessian

end
end InlinedFile139

end OAI
