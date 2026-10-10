import Mathlib
import OAI.Geometry.WeakHessian.Calculus.QuadraticCostLimit
import OAI.Geometry.WeakHessian.Calculus.NoncompactCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile37
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma limit_energy_le_coupling_of_quadratic_contacts
    {us : ℕ → X → ℝ} {w W : X → ℝ}
    (hum : ∀ n, Measurable (us n)) (hwm : Measurable w)
    (huW : ∀ n, MemLp (fun x => us n x*W x) 2 m) (hwW : MemLp (fun x => w x*W x) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) atTop (𝓝 0))
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = squareDensityMeasure m (us n))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    (φ ψ : ℕ → X → ℝ) (hφ : ∀ n, Continuous (φ n)) (hψ : ∀ n, Continuous (ψ n))
    (hiψ : ∀ n, Integrable (ψ n) (ν:Measure X))
    (hb : ∀ n, ∀ᵐ x ∂m, |φ n x| ≤ W x^2)
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ n x y, y ∈ S → φ n x+ψ n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)),
      φ n (γ timeZero)+ψ n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    {E : ℝ} (hE : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E))
    {q : Measure (X×X)} (hq : IsCoupling q μ ν) : ENNReal.ofReal E ≤ QuadraticTransportCost q := by
  by_cases hqt : QuadraticTransportCost q = ∞
  · simp [hqt]
  have H (n : ℕ) : planEnergy (ps n:Measure (Curve X))-(∫ p : X×X,dist p.1 p.2^2 ∂q) ≤
      2*(∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) := by
    have ip := (squareDensity_integrable_of_quadratic_bound (hum n) (huW n) (hφ n).aestronglyMeasurable (hb n)).1
    have iq := (squareDensity_integrable_of_quadratic_bound hwm hwW (hφ n).aestronglyMeasurable (hb n)).1
    have I := planEnergy_le_coupling_of_restricted_contact hqt μ ν hq (h1 n)
      (hφ n) (hψ n) (h0 n ▸ ip) (hμ ▸ iq) (hiψ n) hS hs (hd n) (hc n)
    rw [h0 n,hμ] at I
    exact I.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans
      (squareDensity_quadratic_pairing_bound (hum n) hwm (huW n) hwW (hφ n).aestronglyMeasurable (hb n))) (by norm_num))
  have I := le_of_tendsto_of_tendsto' (hE.sub_const (∫ p : X×X,dist p.1 p.2^2 ∂q)) (hTV.const_mul 2) H
  simp only [mul_zero] at I
  rw [quadraticTransportCost_eq_integral hqt]
  exact ENNReal.ofReal_le_ofReal (sub_nonpos.mp I)

lemma exists_noncompact_optimal_of_quadratic_contacts
    {us : ℕ → X → ℝ} {w W : X → ℝ}
    (hum : ∀ n, Measurable (us n)) (hwm : Measurable w)
    (huW : ∀ n, MemLp (fun x => us n x*W x) 2 m) (hwW : MemLp (fun x => w x*W x) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) atTop (𝓝 0))
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (μs : ℕ → ProbabilityMeasure X) (hμs : ∀ n, (μs n:Measure X) = squareDensityMeasure m (us n))
    (hμT : Tendsto μs atTop (𝓝 μ))
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (hi : ∀ n, Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (ps n:Measure (Curve X)))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = (μs n:Measure X))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    (φ ψ : ℕ → X → ℝ) (hφ : ∀ n, Continuous (φ n)) (hψ : ∀ n, Continuous (ψ n))
    (hiψ : ∀ n, Integrable (ψ n) (ν:Measure X))
    (hb : ∀ n, ∀ᵐ x ∂m, |φ n x| ≤ W x^2)
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ n x y, y ∈ S → φ n x+ψ n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)),
      φ n (γ timeZero)+ψ n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧
      QuadraticTransportCost q ≠ ∞ ∧
      Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 (QuadraticTransportCost q).toReal) := by
  have h0' (n : ℕ) := (h0 n).trans (hμs n)
  have h1' (i j : ℕ) := (h1 i).trans (h1 j).symm
  have hiψ' (n : ℕ) : Integrable (ψ n) (interpolation (ps n:Measure (Curve X)) timeOne) := h1 n ▸ hiψ n
  have hs' (n : ℕ) : ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeOne ∈ S :=
    (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable hS).mp (by
      change ∀ᵐ y ∂interpolation (ps n:Measure (Curve X)) timeOne, y ∈ S
      rw [h1 n]; exact hs)
  obtain ⟨E,hEn,hE⟩ := exists_energy_limit_of_quadratic_contacts hum huW hwW hTV ps hi h0' h1' φ ψ hφ hψ hiψ' hb hs' hd hc
  obtain ⟨q,hqp,hq,hqc⟩ := exists_coupling_of_energy_limit μ ν μs hμT ps hi h0 h1 hE
  have hlower (q' : Measure (X×X)) (hq' : IsCoupling q' μ ν) : ENNReal.ofReal E ≤ QuadraticTransportCost q' :=
    limit_energy_le_coupling_of_quadratic_contacts hum hwm huW hwW hTV μ ν hμ ps h0' h1 φ ψ hφ hψ hiψ hb hS hs hd hc hE hq'
  have he : QuadraticTransportCost q = ENNReal.ofReal E := le_antisymm hqc (hlower q hq)
  refine ⟨q,hqp,⟨hq,fun q' hq' => hqc.trans (hlower q' hq')⟩,ne_top_of_le_ne_top ENNReal.ofReal_ne_top hqc,?_⟩
  simpa only [he,ENNReal.toReal_ofReal hEn] using hE
end WeakHessian

end
end InlinedFile37

end OAI
