import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.VariableEnergyClosure

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma ClosedQuadraticEnergy.graph_energy_limits {Q : E → ℝ≥0∞}
    (hQ : ClosedQuadraticEnergy Q) {us As : ℕ → E} {u A : E}
    (hs : ∀ n, hQ.IsFormGenerator (us n) (As n)) (hu : hQ.IsFormGenerator u A)
    (hus : Tendsto us atTop (𝓝 u)) (hAs : Tendsto As atTop (𝓝 A)) :
    Tendsto (fun n => (Q (us n-u)).toReal) atTop (𝓝 0) ∧
      ∃ M : ℝ, ∀ n, (Q (us n)).toReal ≤ M := by
  have hsub (n : ℕ) : (Q (us n-u)).toReal = -⟪As n-A,us n-u⟫_ℝ/2 := by
    linarith only [hQ.formGenerator_energy (hQ.formGenerator_sub (hs n) hu)]
  have he (n : ℕ) : (Q (us n)).toReal = -⟪As n,us n⟫_ℝ/2 := by
    linarith only [hQ.formGenerator_energy (hs n)]
  constructor
  · simp only [hsub]
    simpa only [sub_self,inner_zero_right,neg_zero,zero_div] using
      (((hAs.sub_const A).inner (𝕜 := ℝ) (hus.sub_const u)).neg.div_const 2)
  · have H : Tendsto (fun n => (Q (us n)).toReal) atTop (𝓝 (-⟪A,u⟫_ℝ/2)) := by
      simp only [he]
      exact (hAs.inner hus).neg.div_const 2
    obtain ⟨M,hM⟩ := H.bddAbove_range
    exact ⟨M,fun n => hM (mem_range_self n)⟩
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def HeatVariableDissipation {m : Measure X} (h : QuadraticCheegerEnergy m)
    (k : X → ℝ) (f ξ : Lp ℝ 2 m) (T : ℝ) : Prop :=
  IntervalIntegrable (fun s => ∫ x, (cheegerHeat h s ξ x*k x)*
    gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m) volume 0 T ∧
  2*(∫ s in 0..T, ∫ x, (cheegerHeat h s ξ x*k x)*
    gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m) ≤
      (∫ x, cheegerHeat h T ξ x*gamma m f f x ∂m) -
      (∫ x, ξ x*gamma m (cheegerHeat h T f) (cheegerHeat h T f) x ∂m)

variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma heatVariableDissipation_of_energy_tendsto
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {fs : ℕ → Lp ℝ 2 m} {f ξ : Lp ℝ 2 m}
    (hfs : ∀ n, Sobolev m (fs n : X → ℝ)) (hf : Sobolev m (f : X → ℝ))
    (hE : Tendsto (fun n => (cheegerEnergy m ((fs n-f : Lp ℝ 2 m) : X → ℝ)).toReal)
      atTop (𝓝 0)) {M : ℝ} (hM : ∀ n, (cheegerEnergy m (fs n : X → ℝ)).toReal ≤ M)
    {Cξ : ℝ} (hCξ : 0 ≤ Cξ) (hξb : ∀ᵐ x ∂m, |ξ x| ≤ Cξ)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k m)
    {B : ℝ} (hB : 0 ≤ B) (hkb : ∀ᵐ x ∂m, |k x| ≤ B)
    {T : ℝ} (hT : 0 ≤ T) (hs : ∀ n, HeatVariableDissipation h k (fs n) ξ T) :
    HeatVariableDissipation h k f ξ T := by
  obtain ⟨hi,ht⟩ := energy_tendsto_variable_heat_integral hfin hID h hfs hf hE hM
    hCξ hξb hkm hB hkb hT (fun n => (hs n).1)
  have hleft := energy_tendsto_heat_gamma_bounded_pairing hfin hID h hfs hf hE
    (Lp.aestronglyMeasurable ξ) hξb hT
  have hright : Tendsto (fun n => ∫ x, cheegerHeat h T ξ x*gamma m (fs n) (fs n) x ∂m)
      atTop (𝓝 (∫ x, cheegerHeat h T ξ x*gamma m f f x ∂m)) := by
    apply energy_tendsto_gamma_bounded_pairing hfin hID hfs hf _ (Lp.aestronglyMeasurable _)
      (cheegerHeat_bounded h hT hCξ ξ hξb)
    simpa only [cheegerEnergy_congr_ae (Lp.coeFn_sub _ _),Pi.sub_def] using hE
  exact ⟨hi, le_of_tendsto_of_tendsto (ht.const_mul 2) (hright.sub hleft)
    (Eventually.of_forall fun n => (hs n).2)⟩
end WeakHessian

end
end

end OAI
