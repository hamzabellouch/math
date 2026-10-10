import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.PointwiseHeatGradient
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatSobolev
import OAI.Geometry.WeakHessian.LocalBounds.WeightedConservation

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile218
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_hopf_increment {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (φ : X →ᵇ ℝ) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    {u v ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hu : Sobolev (exponentialMeasure m (fun x => a*F x)) (u : X → ℝ))
    (hue : u =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ s)
    (hve : v =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ r)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    (hξi : Integrable ξ (exponentialMeasure m (fun x => a*F x)))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ x,ξ x*(cheegerHeat h T v x-cheegerHeat h T u x) ∂exponentialMeasure m (fun x => a*F x)) ≤
      (-(r-s)*s/(2*r))*Real.exp (2*(K-a*CG)*T)*
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x))
        (cheegerHeat h T u) (cheegerHeat h T u) x ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hpi := (hrcd.weighted_heat_mass_nonneg hN hfull hfin o hVB h ξ hξ0 hξi hT).1
  have hpn := cheegerHeat_nonneg h hT ξ hξ0
  have hpb := cheegerHeat_bounded h hT hCξ ξ hξb
  obtain ⟨Lq,hLq⟩ := boundedHopfMap_lipschitz φ hs
  have hJ := boundedHopfMap_L1_increment hnfin φ hpi hpn hs hsr
  have hG := hHess.rcd_weighted_heat_gradient_sobolev hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hu hCξ hξb hξ0 hT
  have hright : (∫ x,cheegerHeat h T ξ x*gamma ν u u x ∂ν) ≤
      ∫ x,cheegerHeat h T ξ x*(localSlope (boundedHopfMap φ s) x).toReal^2 ∂ν := by
    apply integral_mono_ae (integrable_bounded_gamma hnfin hu hu (Lp.memLp _).aestronglyMeasurable hpb)
      (integrable_density_slope_sq hnfin hpi hLq)
    filter_upwards [hpn,gamma_congr_ae (m := ν) hue hue,
      gamma_self (m := ν) (boundedHopfMap φ s),weakGradient_le_localSlope hnfin hLq,
      weakGradient_nonneg (m := ν) (boundedHopfMap φ s)] with x hp he hg hd hn
    rw [he,hg]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hn ENNReal.toReal_nonneg).mpr hd) hp
  have hG' := hG.trans (mul_le_mul_of_nonneg_left hright (Real.exp_pos _).le)
  have hexp : Real.exp (2*(K-a*CG)*T)*Real.exp (-(2*(K-a*CG))*T) = 1 := by
    rw [← Real.exp_add]
    have he : 2*(K-a*CG)*T + -(2*(K-a*CG))*T = 0 := by ring
    rw [he,Real.exp_zero]
  have hG'' := mul_le_mul_of_nonneg_left hG' (Real.exp_pos (2*(K-a*CG)*T)).le
  rw [← mul_assoc,hexp,one_mul] at hG''
  have hc : -(r-s)*s/(2*r) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hsr)) hs.le
    · exact mul_nonneg (by norm_num) (hs.le.trans hsr)
  have hbound := hJ.trans (mul_le_mul_of_nonpos_left hG'' hc)
  have hpair (w : Lp ℝ 2 ν) :
      (∫ x,ξ x*cheegerHeat h T w x ∂ν) = ∫ x,cheegerHeat h T ξ x*w x ∂ν := by
    simpa using (heat_pairing_Lp_density h T ξ (Lp.memLp w)).symm
  have hleft : (∫ x,ξ x*(cheegerHeat h T v x-cheegerHeat h T u x) ∂ν) =
      ∫ x,cheegerHeat h T ξ x*(boundedHopfMap φ r-boundedHopfMap φ s) x ∂ν := by
    have hiv : Integrable (fun x => ξ x*cheegerHeat h T v x) ν :=
      (Lp.memLp ξ).integrable_mul (Lp.memLp (cheegerHeat h T v))
    have hiu : Integrable (fun x => ξ x*cheegerHeat h T u x) ν :=
      (Lp.memLp ξ).integrable_mul (Lp.memLp (cheegerHeat h T u))
    have hip (w : Lp ℝ 2 ν) : Integrable (fun x => cheegerHeat h T ξ x*w x) ν :=
      (Lp.memLp _).integrable_mul (Lp.memLp w)
    simp_rw [mul_sub]
    rw [integral_sub hiv hiu,hpair,hpair,
      ← integral_sub (hip v) (hip u)]
    apply integral_congr_ae
    filter_upwards [hue,hve] with x he hf
    simp only [he,hf,BoundedContinuousFunction.sub_apply,mul_sub]
  rw [hleft]
  simpa only [mul_assoc] using hbound
end WeakHessian

end
end InlinedFile218

end OAI
