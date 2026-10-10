import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeUnitKernelBounds
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeWedgeResolvent

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
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
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

def unitWedgeKernel (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (u v : MetricUnit g) : ℝ :=
  unitFrameFunctional A J α ht E g u (K u.val.proj v.val.proj (unitStarDirection A J α ht E g v))

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma unitWedgeKernel_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ K : X → X → FrameSpace A →L[ℝ] FrameSpace A, ∀ u v : MetricUnit g,
      |unitWedgeKernel A J α ht E g K u v| ≤ B * ‖K u.val.proj v.val.proj‖ := by
  obtain ⟨B,hB,hbound⟩ := wedgeFrame_bound A J α hs ht E hE g
  refine ⟨B,hB,fun K u v => ?_⟩
  have h := hbound u v (K u.val.proj v.val.proj)
  rw [unitDual_star_encode,← unitFrameFunctional_eq A J α hs ht E hE g] at h
  exact h

include hE D hD in
lemma same_resolvent_wedge_quantitative (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T C : ℝ, ∃ hT : 0 < T, 0 ≤ C ∧ T ≤ 1 ∧
      (∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| ≤ C/r^4 ∧
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤ C/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ u v : MetricUnit g,
        S.wedgeKernel g u v =
          unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v +
          unitWedgeKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v +
          B.gammaWedgeTailKernel g T hT.le r u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,Q,hT,hT1,_,_,_,hbound,hker⟩ :=
    same_resolvent_wedge_kernel A J α hs ht E hE D hD n
  obtain ⟨B,hB,hscalar⟩ := unitWedgeKernel_bound A J α hs ht E hE g
  let a := (1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1)
  let b := (1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1)
  let C := max 0 (max (B*a) (B*b))
  have hCa : B*a ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCb : B*b ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T,C,hT,le_max_left _ _,hT1,?_,?_⟩
  · intro r hr u v
    have hw : 0 ≤ VolterraBounds.weight n (r^2) u.val.proj v.val.proj :=
      (VolterraBounds.weight_pos n (sq_pos_of_pos hr) _ _).le
    have htransfer (K : X → X → FrameSpace A →L[ℝ] FrameSpace A) (c : ℝ) (k : ℕ)
        (hk : VolterraBounds.weight n (r^2) u.val.proj v.val.proj * ‖K u.val.proj v.val.proj‖ ≤ c/r^k)
        (hc : B*c ≤ C) :
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitWedgeKernel A J α ht E g K u v| ≤ C/r^k := by
      calc
        _ ≤ VolterraBounds.weight n (r^2) u.val.proj v.val.proj * (B*‖K u.val.proj v.val.proj‖) :=
          mul_le_mul_of_nonneg_left (hscalar K u v) hw
        _ = B*(VolterraBounds.weight n (r^2) u.val.proj v.val.proj * ‖K u.val.proj v.val.proj‖) := by ring
        _ ≤ B*(c/r^k) := mul_le_mul_of_nonneg_left hk hB
        _ = (B*c)/r^k := by ring
        _ ≤ C/r^k := div_le_div_of_nonneg_right hc (pow_nonneg hr.le _)
    exact ⟨htransfer _ a 4 (hbound r hr u.val.proj v.val.proj).1 hCa,
      htransfer _ b 2 (hbound r hr u.val.proj v.val.proj).2 hCb⟩
  · intro r hr S ρ hρ R hρT u v
    have h := hker r hr S ρ hρ R hρT g u v
    rw [unitDual_star_encode,← unitFrameFunctional_eq A J α hs ht E hE g,
      _root_.add_apply,map_add] at h
    exact h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma frameDecode_eq_of_smooth_pairings (x : X) (v w : FrameSpace A)
    (htest : ∀ a : TwoForm X, IsSmooth a →
      framePairing A J α ht E a x v = framePairing A J α ht E a x w) :
    frameDecode J α ht A E x v = frameDecode J α ht A E x w := by
  have he : frameEncode J α ht A E x (frameDecode J α ht A E x v) =
      frameEncode J α ht A E x (frameDecode J α ht A E x w) := by
    ext i
    have h := htest (globalFrame J α ht A E i.1 i.2)
      (globalFrame_smooth J α ht A E hE hs i.1 i.2)
    erw [framePairing_apply,framePairing_apply] at h
    change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
      (globalFrame J α ht A E i.1 i.2 x) (frameDecode J α ht A E x v) =
      MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
        (globalFrame J α ht A E i.1 i.2 x) (frameDecode J α ht A E x w) at h
    change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
      (frameDecode J α ht A E x v) (globalFrame J α ht A E i.1 i.2 x) =
      MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
        (frameDecode J α ht A E x w) (globalFrame J α ht A E i.1 i.2 x)
    exact (MetricForms.pairing_symm _ _ _).trans (h.trans (MetricForms.pairing_symm _ _ _))
  calc
    _ = frameDecode J α ht A E x (frameEncode J α ht A E x (frameDecode J α ht A E x v)) :=
      (frameDecode_encode J α ht A E hE x _).symm
    _ = frameDecode J α ht A E x (frameEncode J α ht A E x (frameDecode J α ht A E x w)) :=
      congrArg (frameDecode J α ht A E x) he
    _ = _ := frameDecode_encode J α ht A E hE x _

include hs hE in
omit [ConnectedSpace X] in
lemma intrinsic_kernel_eq_of_smooth_tests
    (K L : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hL : Continuous (fun p : X × X => L p.1 p.2))
    (htest : ∀ a b : TwoForm X, IsSmooth a → IsSmooth b →
      (∫ x, ∫ y, framePairing A J α ht E a x (K x y (frameEncode J α ht A E y (b y)))
        ∂geometricVolume A J α ∂geometricVolume A J α) =
      ∫ x, ∫ y, framePairing A J α ht E a x (L x y (frameEncode J α ht A E y (b y)))
        ∂geometricVolume A J α ∂geometricVolume A J α)
    (x y : X) :
    (frameDecode J α ht A E x) ∘L K x y ∘L (frameEncode J α ht A E y) =
      (frameDecode J α ht A E x) ∘L L x y ∘L (frameEncode J α ht A E y) := by
  let F := (frameDecode J α ht A E x) ∘L K x y ∘L (frameEncode J α ht A E y)
  let G := (frameDecode J α ht A E x) ∘L L x y ∘L (frameEncode J α ht A E y)
  have hgen (p : A.centers) (j : Fin 6) :
      F (globalFrame J α ht A E p j y) = G (globalFrame J α ht A E p j y) := by
    apply frameDecode_eq_of_smooth_pairings A J α hs ht E hE
    intro a ha
    exact frame_kernel_scalar_eq_of_smooth_tests A J α hs ht E hE K L hK hL htest
      a (globalFrame J α ht A E p j) ha (globalFrame_smooth J α ht A E hE hs p j) x y
  apply ContinuousLinearMap.ext
  intro β
  change F β = G β
  have hr := globalFrame_full_resolution J α ht A E hE (fun _ => β) y
  calc
    F β = F (∑ p : A.centers, ∑ j : Fin 6,
      ((squareMass A y)⁻¹ * GeometricAdjoint.pairing J α ht (fun _ => β)
        (globalFrame J α ht A E p j) y) • globalFrame J α ht A E p j y) := congrArg F hr.symm
    _ = G (∑ p : A.centers, ∑ j : Fin 6,
      ((squareMass A y)⁻¹ * GeometricAdjoint.pairing J α ht (fun _ => β)
        (globalFrame J α ht A E p j) y) • globalFrame J α ht A E p j y) := by
      let z : A.centers → Fin 6 → MetricForms.Form Space 2 := fun p j => globalFrame J α ht A E p j y
      let c : A.centers → Fin 6 → ℝ := fun p j => (squareMass A y)⁻¹ *
        GeometricAdjoint.pairing J α ht (fun _ => β) (globalFrame J α ht A E p j) y
      change F (∑ p : A.centers, ∑ j : Fin 6, c p j • z p j) =
        G (∑ p : A.centers, ∑ j : Fin 6, c p j • z p j)
      simp only [map_sum,map_smul]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => c p j • v) (hgen p j)
    _ = G β := congrArg G hr

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
