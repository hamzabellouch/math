import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.PointwiseHeatGradient
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatSobolev

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile210
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_gradient_sobolev_pointwise {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    (hΓ : MemLp (gamma (exponentialMeasure m (fun x => a*F x)) f f) 2
      (exponentialMeasure m (fun x => a*F x))) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T f) (cheegerHeat h T f) x ≤
      Real.exp (-(2*(K-a*CG))*T)*cheegerHeat h T (hΓ.toLp _) x := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let U := cheegerHeat h T (hΓ.toLp _)
  have hID := fun g hg => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := g) hg
  have hfd := (identified_sobolev_iff_energy hnfin hID).mp hf
  have hheatf : Sobolev ν (cheegerHeat h T f) := (identified_sobolev_iff_energy hnfin hID).mpr
    (((cheeger_closedQuadraticEnergy h).heat_energy_le ν hT f).trans_lt hfd)
  have hLi (S : Set X) (_hS : ν S < ∞) :
      IntegrableOn (gamma ν (cheegerHeat h T f) (cheegerHeat h T f)) S ν :=
    (integrable_gamma hnfin hheatf hheatf).integrableOn
  have hRi (S : Set X) (hS : ν S < ∞) :
      IntegrableOn (fun x => Real.exp (-(2*(K-a*CG))*T)*U x) S ν := by
    let : IsFiniteMeasure (ν.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hS⟩
    exact ((Lp.memLp U).restrict S |>.integrable (by norm_num)).const_mul _
  have H := ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    (f := fun x => Real.exp (-(2*(K-a*CG))*T)*U x-
      gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x)
    (fun S _ hs => (hRi S hs).sub (hLi S hs)) (by
      intro S hS hs
      let hu2 := memLp_indicator_const (μ := ν) 2 hS (1:ℝ) (Or.inr hs.ne)
      let u := hu2.toLp (S.indicator (fun _ : X => (1:ℝ)))
      have hue : u =ᵐ[ν] S.indicator (fun _ : X => (1:ℝ)) := hu2.coeFn_toLp
      have hun : ∀ᵐ x ∂ν,0 ≤ u x := hue.mono fun x hx => hx ▸ indicator_nonneg (fun _ _ => zero_le_one) x
      have hub : ∀ᵐ x ∂ν,|u x| ≤ 1 := by
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have HH := hHess.rcd_weighted_heat_gradient_sobolev hN hrcd hfull hfin o hF hFb hGb hGc ha h
        hf zero_le_one hub hun hT
      rw [heat_pairing_Lp_density h T u hΓ] at HH
      have hpair (g : X → ℝ) : (∫ x,u x*g x ∂ν) = ∫ x in S,g x ∂ν := by
        rw [← integral_indicator hS]
        apply integral_congr_ae
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      rw [hpair,hpair] at HH
      rw [integral_sub (hRi S hs) (hLi S hs),integral_const_mul]
      exact sub_nonneg.mpr HH)
  exact H.mono fun _ hx => sub_nonneg.mp hx
end WeakHessian

end
end InlinedFile210

end OAI
