import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.PointwiseHeatGradient
import OAI.Geometry.WeakHessian.HeatFlow.SharpHeatGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile98
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_gradient_pointwise {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (hg : MemLp (fun x => (D x)^2) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂m,(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ≤ Real.exp (-2*K*t)*
      cheegerHeat h t (hg.toLp (fun x => (D x)^2)) x := by
  let V := cheegerHeat h t (hg.toLp (fun x => (D x)^2))
  have hgi : Integrable (fun x => (weakGradient m (cheegerHeat h t f : X → ℝ) x)^2) m :=
    (memLp_two_iff_integrable_sq (hrcd.cheegerHeat_sobolev hfin h o hD ht).2.2.aestronglyMeasurable).mp
      (hrcd.cheegerHeat_sobolev hfin h o hD ht).2.2
  have hVi (S : Set X) (hS : m S < ∞) : IntegrableOn (fun x => Real.exp (-2*K*t)*V x) S m := by
    let : IsFiniteMeasure (m.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hS⟩
    exact ((Lp.memLp V).restrict S |>.integrable (by norm_num)).const_mul _
  have H := ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    (f := fun x => Real.exp (-2*K*t)*V x-(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2)
    (fun S hS hs => (hVi S hs).sub hgi.integrableOn) (by
      intro S hS hs
      let hu2 := memLp_indicator_const (μ := m) 2 hS (1:ℝ) (Or.inr hs.ne)
      let u := hu2.toLp (S.indicator (fun _ : X => (1:ℝ)))
      have hue : u =ᵐ[m] S.indicator (fun _ : X => (1:ℝ)) := hu2.coeFn_toLp
      have hui : Integrable u m :=
        ((integrableOn_const (C := (1:ℝ)) hs.ne).integrable_indicator hS).congr hue.symm
      have hun : ∀ᵐ x ∂m,0 ≤ u x := hue.mono fun x hx => hx ▸ indicator_nonneg (fun _ _ => zero_le_one) x
      have hub : ∀ᵐ x ∂m,u x ≤ 1 := by
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have HH := hrcd.cheegerHeat_gradient_integral hN hfull hfin h o hD ht
        u hui hun zero_le_one hub
      rw [heat_pairing_Lp_density h t u hg] at HH
      have hpair (g : X → ℝ) : (∫ x,u x*g x ∂m) = ∫ x in S,g x ∂m := by
        rw [← integral_indicator hS]
        apply integral_congr_ae
        filter_upwards [hue] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      rw [hpair,hpair] at HH
      rw [integral_sub (hVi S hs) hgi.integrableOn,integral_const_mul]
      exact sub_nonneg.mpr HH)
  exact H.mono fun x hx => sub_nonneg.mp hx
end WeakHessian

end
end InlinedFile98

end OAI
