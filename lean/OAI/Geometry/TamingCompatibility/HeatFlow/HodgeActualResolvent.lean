import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeSmoothResolvent
import OAI.Geometry.TamingCompatibility.Hodge.HodgeActualGram

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_actual_gram (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L Q : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T Q (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ a b : PreL2 A J α hs ht true, ∀ x y : X,
        ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫ =
          framePairing A J α ht E b.val x
            ((HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y +
              HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y)
                (frameEncode J α ht A E y (a.val y))) +
          B.pairingGammaTail T hT.le r a b x y := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,hpair⟩ :=
    same_resolvent_smooth_spatial A J α hs ht E hE D hD n
  refine ⟨T,L,Q,hT,hT1,hL,hQ,hcont,hbound,?_⟩
  intro r hr C ρ hρ B hρT a b x y
  let KL := HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r
  let KE := HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r
  have hcL : Continuous (fun p : X × X => KL p.1 p.2) := (hcont r hr).1
  have hcE : Continuous (fun p : X × X => KE p.1 p.2) := (hcont r hr).2
  apply actual_gram_eq_of_smooth_tests hE C B T hT.le (fun x y => KL x y + KE x y)
    (hcL.add hcE) ?_ a b x y
  intro a b
  let FL : X → X → ℝ := fun x y => framePairing A J α ht E b.val x
    (KL x y (frameEncode J α ht A E y (a.val y)))
  let FE : X → X → ℝ := fun x y => framePairing A J α ht E b.val x
    (KE x y (frameEncode J α ht A E y (a.val y)))
  let FT : X → X → ℝ := B.pairingGammaTail T hT.le r a b
  have hFL : Continuous (fun p : X × X => FL p.1 p.2) :=
    frame_kernel_pairing_continuous A J α hs ht E hE KL hcL b.val a.val b.property a.property
  have hFE : Continuous (fun p : X × X => FE p.1 p.2) :=
    frame_kernel_pairing_continuous A J α hs ht E hE KE hcE b.val a.val b.property a.property
  have hFT : Continuous (fun p : X × X => FT p.1 p.2) :=
    B.pairingGammaTail_continuous T hT.le r a b
  have hIL := hFL.integrable_of_hasCompactSupport (μ := (geometricVolume A J α).prod (geometricVolume A J α))
    (HasCompactSupport.of_compactSpace _)
  have hIE := hFE.integrable_of_hasCompactSupport (μ := (geometricVolume A J α).prod (geometricVolume A J α))
    (HasCompactSupport.of_compactSpace _)
  have hIT := hFT.integrable_of_hasCompactSupport (μ := (geometricVolume A J α).prod (geometricVolume A J α))
    (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, ∫ y, ⟪C.pairingEvaluationVector b x,C.pairingEvaluationVector a y⟫
      ∂geometricVolume A J α ∂geometricVolume A J α) =
      (∫ x, ∫ y, FL x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FE x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FT x y ∂geometricVolume A J α ∂geometricVolume A J α) := by
    have hsL := integral_integral_swap_of_hasCompactSupport (f := FL) (μ := geometricVolume A J α) (ν := geometricVolume A J α) hFL
      (HasCompactSupport.of_compactSpace _)
    have hsE := integral_integral_swap_of_hasCompactSupport (f := FE) (μ := geometricVolume A J α) (ν := geometricVolume A J α) hFE
      (HasCompactSupport.of_compactSpace _)
    rw [C.pairingEvaluationVector_gram,hpair a r hr b,← hsL,← hsE,
      B.pairingGammaTail_integral T hT.le r hr hρT a b]
  rw [he]
  have hz : (∫ x, ∫ y, FL x y + FE x y + FT x y ∂geometricVolume A J α ∂geometricVolume A J α) =
      (∫ x, ∫ y, FL x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FE x y ∂geometricVolume A J α ∂geometricVolume A J α) +
      (∫ x, ∫ y, FT x y ∂geometricVolume A J α ∂geometricVolume A J α) := by
    have hIS : Integrable (fun p : X × X => FL p.1 p.2 + FE p.1 p.2 + FT p.1 p.2)
        ((geometricVolume A J α).prod (geometricVolume A J α)) := (hIL.add hIE).add hIT
    rw [← integral_prod _ hIS]
    have hsum := integral_add (hIL.add hIE) hIT
    simp only [Pi.add_apply] at hsum
    rw [hsum]
    have hsum' := integral_add hIL hIE
    rw [hsum',integral_prod _ hIL,integral_prod _ hIE,integral_prod _ hIT]
  rw [← hz]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [_root_.add_apply,map_add,FL,FE,FT]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
