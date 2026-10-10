import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.VariableDissipationFullDomain

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_sobolev {K N : ℝ}
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
    HeatVariableDissipation h (fun x => K-a*G x) f ξ T := by
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
  have hkm : AEStronglyMeasurable (fun x => K-a*G x) ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hkb : ∀ᵐ x ∂ν, |K-a*G x| ≤ |K|+|a| *CG := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact hGb x)
  apply heatVariableDissipation_of_energy_tendsto hnfin hID h hus hf hE hb hCξ hξb hkm
    (by positivity : 0 ≤ |K|+|a| *CG) hkb hT
  intro n
  exact hHess.rcd_weighted_heat_variable_full_generator hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (hg n) hCξ hξb hξ0 hT
end WeakHessian

end
end

end OAI
