import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.QuadraticCost
import OAI.Geometry.WeakHessian.LocalBounds.QuadraticContact

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile35
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma weighted_density_triangle {u v w W : X → ℝ}
    (hu : MemLp (fun x => u x*W x) 2 m) (hv : MemLp (fun x => v x*W x) 2 m)
    (hw : MemLp (fun x => w x*W x) 2 m) :
    (∫ x,|(u x*W x)^2-(v x*W x)^2| ∂m) ≤
      (∫ x,|(u x*W x)^2-(w x*W x)^2| ∂m)+(∫ x,|(v x*W x)^2-(w x*W x)^2| ∂m) := by
  have hiu : Integrable (fun x => |(u x*W x)^2-(w x*W x)^2|) m := (hu.integrable_sq.sub hw.integrable_sq).abs
  have hiv : Integrable (fun x => |(v x*W x)^2-(w x*W x)^2|) m := (hv.integrable_sq.sub hw.integrable_sq).abs
  rw [← integral_add hiu hiv]
  apply integral_mono (hu.integrable_sq.sub hv.integrable_sq).abs
    ((hu.integrable_sq.sub hw.integrable_sq).abs.add (hv.integrable_sq.sub hw.integrable_sq).abs)
  intro x
  change |(u x*W x)^2-(v x*W x)^2| ≤ |(u x*W x)^2-(w x*W x)^2|+|(v x*W x)^2-(w x*W x)^2|
  rw [abs_sub_comm ((v x*W x)^2) ((w x*W x)^2)]
  exact abs_sub_le _ _ _

lemma cost_difference_quadratic_contact {u v W φ ψ : X → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (huW : MemLp (fun x => u x*W x) 2 m) (hvW : MemLp (fun x => v x*W x) 2 m)
    {π η : Measure (Curve X)} [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hiη : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) η)
    (h0π : interpolation π timeZero = squareDensityMeasure m u)
    (h0η : interpolation η timeZero = squareDensityMeasure m v)
    (h1 : interpolation π timeOne = interpolation η timeOne)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hiψ : Integrable ψ (interpolation π timeOne))
    (hb : ∀ᵐ x ∂m, |φ x| ≤ W x^2)
    {S : Set X} (hs : ∀ᵐ γ ∂η, γ timeOne ∈ S)
    (hd : ∀ x y, y ∈ S → φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    planEnergy π-planEnergy η ≤ 2*(∫ x,|(u x*W x)^2-(v x*W x)^2| ∂m) := by
  have ip := (squareDensity_integrable_of_quadratic_bound hu huW hφ.aestronglyMeasurable hb).1
  have iq := (squareDensity_integrable_of_quadratic_bound hv hvW hφ.aestronglyMeasurable hb).1
  have H := planEnergy_le_of_restricted_contact hiη hφ hψ (h0π ▸ ip) (h0η ▸ iq) hiψ hs hd hc h1
  rw [h0π,h0η] at H
  have J := squareDensity_quadratic_pairing_bound hu hv huW hvW hφ.aestronglyMeasurable hb
  exact H.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans J) (by norm_num))

variable [SecondCountableTopology X]

omit [SecondCountableTopology X] in
lemma exists_energy_limit_of_quadratic_contacts
    {us : ℕ → X → ℝ} {w W : X → ℝ}
    (hum : ∀ n, Measurable (us n))
    (huW : ∀ n, MemLp (fun x => us n x*W x) 2 m)
    (hwW : MemLp (fun x => w x*W x) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m) atTop (𝓝 0))
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (hi : ∀ n, Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (ps n:Measure (Curve X)))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = squareDensityMeasure m (us n))
    (h1 : ∀ i j, interpolation (ps i:Measure (Curve X)) timeOne = interpolation (ps j:Measure (Curve X)) timeOne)
    (φ ψ : ℕ → X → ℝ) (hφ : ∀ n, Continuous (φ n)) (hψ : ∀ n, Continuous (ψ n))
    (hiψ : ∀ n, Integrable (ψ n) (interpolation (ps n:Measure (Curve X)) timeOne))
    (hb : ∀ n, ∀ᵐ x ∂m, |φ n x| ≤ W x^2)
    {S : Set X} (hs : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeOne ∈ S)
    (hd : ∀ n x y, y ∈ S → φ n x+ψ n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)),
      φ n (γ timeZero)+ψ n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    ∃ E : ℝ, 0 ≤ E ∧ Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E) := by
  let e (n : ℕ) := ∫ x,|(us n x*W x)^2-(w x*W x)^2| ∂m
  have hbnd (i j : ℕ) : |planEnergy (ps i:Measure (Curve X))-planEnergy (ps j:Measure (Curve X))| ≤ 2*(e i+e j) := by
    have aux (a b : ℕ) : planEnergy (ps a:Measure (Curve X))-planEnergy (ps b:Measure (Curve X)) ≤ 2*(e a+e b) :=
      (cost_difference_quadratic_contact (hum a) (hum b) (huW a) (huW b) (hi b) (h0 a) (h0 b)
        (h1 a b) (hφ a) (hψ a) (hiψ a) (hb a) (hs b) (hd a) (hc a)).trans
        (mul_le_mul_of_nonneg_left (weighted_density_triangle (huW a) (huW b) hwW) (by norm_num))
    exact abs_le.mpr ⟨by have H := aux j i; linarith,aux i j⟩
  have hC : CauchySeq (fun n => planEnergy (ps n:Measure (Curve X))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k,hk⟩ := eventually_atTop.1 (hTV.eventually (eventually_lt_nhds (show (0:ℝ)<ε/4 by positivity)))
    refine ⟨k,fun i hi j hj => ?_⟩
    rw [Real.dist_eq]
    exact (hbnd i j).trans_lt (by have H := hk i hi; have J := hk j hj; dsimp [e]; linarith)
  obtain ⟨E,hE⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨E,ge_of_tendsto' hE (fun n => planEnergy_nonneg _),hE⟩
end WeakHessian

end
end InlinedFile35

end OAI
