import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatHamiltonJacobi

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile219
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_hopf_pointwise {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (φ : X →ᵇ ℝ) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    {u v : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hu : Sobolev (exponentialMeasure m (fun x => a*F x)) (u : X → ℝ))
    (hue : u =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ s)
    (hve : v =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ r)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),
      cheegerHeat h T v x-cheegerHeat h T u x ≤
      (-(r-s)*s/(2*r))*Real.exp (2*(K-a*CG)*T)*
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u) (cheegerHeat h T u) x := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let c := (-(r-s)*s/(2*r))*Real.exp (2*(K-a*CG)*T)
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hHU : Sobolev ν (cheegerHeat h T u) := (identified_sobolev_iff_energy hnfin hID).mpr
    (((cheeger_closedQuadraticEnergy h).heat_energy_le ν hT u).trans_lt
      ((identified_sobolev_iff_energy hnfin hID).mp hu))
  let Γ := gamma ν (cheegerHeat h T u) (cheegerHeat h T u)
  let Δ := fun x => cheegerHeat h T v x-cheegerHeat h T u x
  have hiΓ : Integrable Γ ν := integrable_gamma hnfin hHU hHU
  have hiΔ (S : Set X) (hS : ν S < ∞) : IntegrableOn Δ S ν := by
    let : IsFiniteMeasure (ν.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hS⟩
    exact (((Lp.memLp _).restrict S).integrable (by norm_num)).sub
      (((Lp.memLp _).restrict S).integrable (by norm_num))
  have H := ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    (f := fun x => c*Γ x-Δ x)
    (fun S _ hs => (hiΓ.const_mul c).integrableOn.sub (hiΔ S hs)) (by
      intro S hS hsS
      let he := memLp_indicator_const (μ := ν) 2 hS (1:ℝ) (Or.inr hsS.ne)
      let ξ := he.toLp (S.indicator (fun _ : X => (1:ℝ)))
      have hξe : ξ =ᵐ[ν] S.indicator (fun _ : X => (1:ℝ)) := he.coeFn_toLp
      have hξi : Integrable ξ ν :=
        ((integrableOn_const (C := (1:ℝ)) hsS.ne).integrable_indicator hS).congr hξe.symm
      have hξn : ∀ᵐ x ∂ν,0 ≤ ξ x := hξe.mono fun x hx =>
        hx ▸ indicator_nonneg (fun _ _ => zero_le_one) x
      have hξb : ∀ᵐ x ∂ν,|ξ x| ≤ 1 := by
        filter_upwards [hξe] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      have HH := hHess.rcd_weighted_heat_hopf_increment hN hrcd hfull hfin o hF hFb hGb hGc ha h
        φ hs hsr hu hue hve zero_le_one hξb hξn hξi hT
      have hpair (g : X → ℝ) : (∫ x,ξ x*g x ∂ν) = ∫ x in S,g x ∂ν := by
        rw [← integral_indicator hS]
        apply integral_congr_ae
        filter_upwards [hξe] with x hx
        rw [hx]; by_cases hx : x ∈ S <;> simp [hx]
      change (∫ x,ξ x*Δ x ∂ν) ≤ c*(∫ x,ξ x*Γ x ∂ν) at HH
      rw [hpair,hpair] at HH
      rw [integral_sub (hiΓ.const_mul c).integrableOn (hiΔ S hsS),integral_const_mul]
      exact sub_nonneg.mpr HH)
  exact H.mono fun _ hx => sub_nonneg.mp hx

lemma WeakHessianUpperBound.rcd_weighted_heat_hopf_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (φ : X →ᵇ ℝ) (hφ : HasCompactSupport (φ : X → ℝ)) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ u v : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)),
      u =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ s ∧
      v =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ r ∧
      ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),
        cheegerHeat h T v x-cheegerHeat h T u x ≤
        (-(r-s)*s/(2*r))*Real.exp (2*(K-a*CG)*T)*
        gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u) (cheegerHeat h T u) x := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  have hqs := boundedHopfMap_memLp_compact hnfin φ o hφ hs
  have hqr := boundedHopfMap_memLp_compact hnfin φ o hφ (hs.trans_le hsr)
  let u := hqs.toLp (boundedHopfMap φ s)
  let v := hqr.toLp (boundedHopfMap φ r)
  have hSob : Sobolev ν (u : X → ℝ) := (sobolev_congr_ae hqs.coeFn_toLp).mpr
    (sobolev_of_lipschitz_compactSupport hnfin (boundedHopfMap_lipschitz φ hs).choose_spec
      (boundedHopfMap_compactSupport φ o hφ hs))
  exact ⟨u,v,hqs.coeFn_toLp,hqr.coeFn_toLp,
    hHess.rcd_weighted_heat_hopf_pointwise hN hrcd hfull hfin o hF hFb hGb hGc ha h
      φ hs hsr hSob hqs.coeFn_toLp hqr.coeFn_toLp hT⟩
end WeakHessian

end
end InlinedFile219

end OAI
