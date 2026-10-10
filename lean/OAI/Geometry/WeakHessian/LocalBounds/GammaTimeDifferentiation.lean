import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TripleTimePairing
import OAI.Geometry.WeakHessian.LocalBounds.GammaRepresentativePairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile191
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_triple_neg_left (u v w : Lp ℝ 2 m) :
    (∫ x,(-u) x*v x*w x ∂m) = -(∫ x,u x*v x*w x ∂m) := by
  calc
    _ = ∫ x,-(u x*v x*w x) ∂m := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_neg u] with x hx
      rw [hx]; simp only [Pi.neg_apply]; ring
    _ = _ := integral_neg _

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_triple_neg_middle (u v w : Lp ℝ 2 m) :
    (∫ x,u x*(-v) x*w x ∂m) = -(∫ x,u x*v x*w x ∂m) := by
  calc
    _ = ∫ x,-(u x*v x*w x) ∂m := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_neg v] with x hx
      rw [hx]; simp only [Pi.neg_apply]; ring
    _ = _ := integral_neg _

omit [SigmaFinite m] in
lemma hasDerivAt_gamma_interpolation (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m)
    {u A ξ B : ℝ → Lp ℝ 2 m} {C D : Lp ℝ 2 m} {a : ℝ}
    (hud : HasDerivAt u (-A a) a) (hAd : HasDerivAt A (-C) a)
    (hξd : HasDerivAt ξ (B a) a) (hBd : HasDerivAt B D a)
    (huG : ∀ᶠ t in 𝓝 a,IsLaplacian m (u t : X → ℝ) (A t))
    (hAG : IsLaplacian m (A a : X → ℝ) C)
    (hξG : ∀ᶠ t in 𝓝 a,IsLaplacian m (ξ t : X → ℝ) (B t))
    (hBG : IsLaplacian m (B a : X → ℝ) D)
    (huR : ∀ᶠ t in 𝓝 a,BoundedLipschitzRepresentative m (u t))
    (hAR : BoundedLipschitzRepresentative m (A a))
    (n : ℕ) (hub : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
    (hAb : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|A t x| ≤ (n:ℝ))
    {Cξ CB : ℝ} (hξb : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|ξ t x| ≤ Cξ)
    (hBb : ∀ᵐ x ∂m,|B a x| ≤ CB) :
    HasDerivAt (fun t => ∫ x,ξ t x*gamma m (u t : X → ℝ) (u t) x ∂m)
      ((∫ x,B a x*gamma m (u a : X → ℝ) (u a) x ∂m)-
        2*(∫ x,ξ a x*gamma m (u a : X → ℝ) (A a) x ∂m)) a := by
  have huga := mem_of_mem_nhds huG
  have hξga := mem_of_mem_nhds hξG
  have hura := mem_of_mem_nhds huR
  have hξba := mem_of_mem_nhds hξb
  have hd1 := (hasDerivAt_integral_square_mul hud hBd n hub hBb).const_mul (1/2:ℝ)
  have hd2 := hasDerivAt_integral_mul_mul hud hAd hξd n hub hAb hξba
  have hd := hd1.sub hd2
  have heq : (fun t => ∫ x,ξ t x*gamma m (u t : X → ℝ) (u t) x ∂m) =ᶠ[𝓝 a]
      (fun t => (1/2)*(∫ x,(u t x)^2*B t x ∂m)-(∫ x,u t x*A t x*ξ t x ∂m)) := by
    filter_upwards [huG,hξG,huR,hξb] with t h1 h2 h3 h4
    exact h1.square_gamma_pairing_ae hfin hpar h2 h3 h4
  have H := hd.congr_of_eventuallyEq heq
  rw [integral_triple_neg_middle,integral_triple_neg_left,integral_triple_neg_middle] at H
  have e1 := huga.square_gamma_pairing_ae hfin hpar hBG hura hBb
  have e2 := huga.mixed_pairing_ae hfin hpar hAG hξga hura hAR hξba
  convert! H using 1
  rw [e1,e2]
  ring
end WeakHessian

end
end InlinedFile191

end OAI
