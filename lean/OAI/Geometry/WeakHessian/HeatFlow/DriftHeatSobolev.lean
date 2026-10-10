import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatFullDomain
import OAI.Geometry.WeakHessian.LocalBounds.EnergyGammaPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile209
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_gradient_sobolev {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) (f : X → ℝ))
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x))
      (cheegerHeat h T f) (cheegerHeat h T f) x ∂exponentialMeasure m (fun x => a*F x)) ≤
    Real.exp (-(2*(K-a*CG))*T)*
      (∫ x,cheegerHeat h T ξ x*gamma (exponentialMeasure m (fun x => a*F x)) f f x
        ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hfd : cheegerEnergy ν (f : X → ℝ) < ∞ := (identified_sobolev_iff_energy hnfin hID).mp hf
  let fd : Q.domain := ⟨f,hfd⟩
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let us := fun n => (Q.scale (hts n)).resolventLinear f
  let As := fun n => (ts n)⁻¹ • (us n-f)
  have hg (n : ℕ) : Q.IsFormGenerator (us n) (As n) := (Q.scaled_resolvent_iff (hts n) f _).mp rfl
  let ud : ℕ → Q.domain := fun n => ⟨us n,(hg n).1⟩
  have hb (n : ℕ) : Q.realEnergy (ud n) ≤ Q.realEnergy fd :=
    ENNReal.toReal_mono hfd.ne (Q.scaled_resolvent_energy_le (hts n) f)
  have he : Tendsto (fun n => Q.realEnergy (ud n-fd)) atTop (𝓝 0) :=
    Q.form_energy_sub_tendsto (cheeger_domain_dense h) ud fd
      (Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hts ht0 f)
      (Q.realEnergy_quadratic.nonneg fd) hb
      (Q.scaled_resolvent_energy_tendsto (cheeger_domain_dense h) hts ht0 fd)
  have hE : Tendsto (fun n => (cheegerEnergy ν ((us n-f : Lp ℝ 2 ν) : X → ℝ)).toReal) atTop (𝓝 0) := he
  have hus (n : ℕ) : Sobolev ν (us n : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr (hg n).1
  have hheatf : Sobolev ν (cheegerHeat h T f) := (identified_sobolev_iff_energy hnfin hID).mpr
    ((Q.heat_energy_le ν hT f).trans_lt hfd)
  have hheatu (n : ℕ) : Sobolev ν (cheegerHeat h T (us n)) := (identified_sobolev_iff_energy hnfin hID).mpr
    ((Q.heat_energy_le ν hT (us n)).trans_lt (hg n).1)
  have hEH : Tendsto (fun n => (cheegerEnergy ν
      ((cheegerHeat h T (us n)-cheegerHeat h T f : Lp ℝ 2 ν) : X → ℝ)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hE
    rw [← map_sub]
    exact ENNReal.toReal_mono (Q.domain.sub_mem (hg n).1 hfd).ne (Q.heat_energy_le ν hT (us n-f))
  have hright : Tendsto (fun n => ∫ x,cheegerHeat h T ξ x*gamma ν (us n) (us n) x ∂ν)
      atTop (𝓝 (∫ x,cheegerHeat h T ξ x*gamma ν f f x ∂ν)) := by
    apply energy_tendsto_gamma_bounded_pairing hnfin hID hus hf
    · simpa only [cheegerEnergy_congr_ae (Lp.coeFn_sub _ _),Pi.sub_def] using hE
    · exact (Lp.memLp _).aestronglyMeasurable
    · exact cheegerHeat_bounded h hT hCξ ξ hξb
  have hleft : Tendsto (fun n => ∫ x,ξ x*gamma ν (cheegerHeat h T (us n)) (cheegerHeat h T (us n)) x ∂ν)
      atTop (𝓝 (∫ x,ξ x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)) := by
    apply energy_tendsto_gamma_bounded_pairing hnfin hID hheatu hheatf
    · simpa only [cheegerEnergy_congr_ae (Lp.coeFn_sub _ _),Pi.sub_def] using hEH
    · exact (Lp.memLp ξ).aestronglyMeasurable
    · exact hξb
  exact le_of_tendsto_of_tendsto hleft (hright.const_mul _) (Eventually.of_forall fun n =>
    hHess.rcd_weighted_heat_gradient_full_generator hN hrcd hfull hfin o hF hFb hGb hGc ha h
      (hg n) hCξ hξb hξ0 hT)
end WeakHessian

end
end InlinedFile209

end OAI
