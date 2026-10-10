import Mathlib
import OAI.Geometry.WeakHessian.Transport.EntropyCoupling

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma cheegerHeat_plan_entropy_coupling
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m) {k : ℝ}
    (hgrad : ∀ (f u : Lp ℝ 2 m), Sobolev m (f : X → ℝ) →
      (∀ᵐ x ∂m, 0 ≤ u x) → ∀ B : ℝ, 0 ≤ B → (∀ᵐ x ∂m, |u x| ≤ B) →
      ∀ t : ℝ, 0 ≤ t → Real.exp (2*k*t)*(∫ x, u x*(weakGradient m (cheegerHeat h t f) x)^2 ∂m) ≤
        ∫ x, cheegerHeat h t u x*(weakGradient m f x)^2 ∂m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1)
    {T : ℝ} (hT : 0 ≤ T)
    (hPm : ∫ x,cheegerHeat h T (smoothDensity κ u 0) x ∂m = 1)
    {V : X → ℝ} (huV : Integrable (fun x => smoothDensity κ u 1 x*V x) m)
    (hPV : Integrable (fun x => cheegerHeat h T (smoothDensity κ u 0) x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure m (smoothDensity κ u 1) ∧
      p.map Prod.snd = densityMeasure m (cheegerHeat h T (smoothDensity κ u 0)) ∧
      QuadraticTransportCost p ≠ ∞ ∧ (QuadraticTransportCost p).toReal ≤
        2*((∫ s in (0:ℝ)..1,planKineticCost π/Real.exp (2*k*T*(1-s))/2)+
          T*((∫ x,reducedEntropy (smoothDensity κ u 1 x) ∂m)-
            (∫ x,reducedEntropy (cheegerHeat h T (smoothDensity κ u 0) x) ∂m))) := by
  have hprop := fun s => hπ.smoothDensity_properties hB hu hun hlaw hnorm
    hc.continuous (hc.continuous.integrable_of_hasCompactSupport hκ) hn hm s
  have hPn := cheegerHeat_nonneg h hT (smoothDensity κ u 0) (hprop 0).1
  let := densityMeasure_probability_of_integrable (smoothDensity κ u 1) (hprop 1).1
    (hprop 1).2.2.1 (hprop 1).2.2.2.1
  let := densityMeasure_probability_of_integrable (cheegerHeat h T (smoothDensity κ u 0)) hPn
    (integrable_of_integral_eq_one hPm) hPm
  let A := ∫ s in (0:ℝ)..1,planKineticCost π/Real.exp (2*k*T*(1-s))/2
  let E := (∫ x,reducedEntropy (smoothDensity κ u 1 x) ∂m)-
    (∫ x,reducedEntropy (cheegerHeat h T (smoothDensity κ u 0) x) ∂m)
  have HD : ∀ (f : X →ᵇ ℝ),HasCompactSupport (f : X → ℝ) → ∀ q : ℝ,0 < q →
      (∫ x,smoothDensity κ u 1 x*boundedHopfMap f (q+1) x ∂m)-
      (∫ x,cheegerHeat h T (smoothDensity κ u 0) x*boundedHopfMap f q x ∂m)+(-T)*E ≤ A := by
    intro f hf q hq
    apply entropy_dual_of_regularized (smoothDensity κ u 1)
      (cheegerHeat h T (smoothDensity κ u 0)) (hprop 1).2.2.1
      (integrable_of_integral_eq_one hPm) ((hprop 1).2.2.2.1.trans hPm.symm)
      (hprop 1).1 hPn huV hPV hV (D := compactHopfDualBound hfin o f hf hq/2)
    intro ε hε
    have H := compact_dual_heat_offset_limit hfin h (smoothDensity κ u 0) (smoothDensity κ u 1)
      (boundedHopfMap_memLp_compact hfin f o hf hq)
      (boundedHopfMap_memLp_compact hfin f o hf (by linarith : 0 < q+1)) hT hε
      (fun δ hδ => cheegerHeat_plan_entropy_dual hfin o hID hpar h hgrad hπ hb hgeo
        hB hu hun hlaw hnorm hκ hc hn hm hδ hT hq f hf ε hε)
    convert H using 1 <;> ring
  have hz (t : ℝ) : boundedHopfMap (0 : X →ᵇ ℝ) t = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using boundedHopfMap_norm_le (0 : X →ᵇ ℝ) t) (norm_nonneg _)
  have HZ := HD 0 (by simp [HasCompactSupport]) 1 (by norm_num)
  simp only [hz,BoundedContinuousFunction.coe_zero,Pi.zero_apply,mul_zero,integral_zero,sub_zero,zero_add] at HZ
  have hnon : 0 ≤ 2*(A-(-T)*E) := by linarith
  obtain ⟨p,hp,hp0,hp1,hcost⟩ := coupling_of_entropy_dual o (smoothDensity κ u 1)
    (cheegerHeat h T (smoothDensity κ u 0)) (hprop 1).1 hPn (T := -T) (A := A)
    (fun f hf _ q hq => HD f hf q hq)
  refine ⟨p,hp,hp0,hp1,ne_of_lt (hcost.trans_lt ENNReal.ofReal_lt_top),?_⟩
  have HH := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcost
  rw [ENNReal.toReal_ofReal hnon] at HH
  simpa only [A,E,neg_mul,sub_neg_eq_add,QuadraticTransportCost] using HH

end WeakHessian

end
end

end OAI
