import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeResolvent2
import OAI.Geometry.TamingCompatibility.Hodge.HodgeUnitKernelBounds

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

def unitCurrentKernel (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (u v : MetricUnit g) : ℝ :=
  unitFrameFunctional A J α ht E g u (K u.val.proj v.val.proj (unitFrameDirection A J α ht E g v))

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma unitCurrentKernel_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ K : X → X → FrameSpace A →L[ℝ] FrameSpace A, ∀ u v : MetricUnit g,
      |unitCurrentKernel A J α ht E g K u v| ≤ B * ‖K u.val.proj v.val.proj‖ := by
  obtain ⟨B,hB,hbound⟩ := currentFrame_bound A J α hs ht E hE g
  refine ⟨B,hB,fun K u v => ?_⟩
  have h := hbound u v (K u.val.proj v.val.proj)
  rw [unitDual_encode,← unitFrameFunctional_eq A J α hs ht E hE g] at h
  exact h

include hE D hD in
lemma same_resolvent_current_quantitative (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T C : ℝ, ∃ hT : 0 < T, 0 ≤ C ∧ T ≤ 1 ∧
      (∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| ≤ C/r^4 ∧
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤ C/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ u v : MetricUnit g,
        S.innerKernel g u v =
          unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v +
          unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v +
          B.gammaTailKernel g T hT.le r u v := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,Q,hT,hT1,_,_,_,hbound,hker⟩ :=
    same_resolvent_current_kernel A J α hs ht E hE D hD n
  obtain ⟨B,hB,hscalar⟩ := unitCurrentKernel_bound A J α hs ht E hE g
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
          |unitCurrentKernel A J α ht E g K u v| ≤ C/r^k := by
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
    rw [unitDual_encode,← unitFrameFunctional_eq A J α hs ht E hE g,
      _root_.add_apply,map_add] at h
    exact h

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

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

include hE D hD in
lemma same_resolvent_current_point_bound :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
        ∀ u v : MetricUnit g,
        |S.innerKernel g u v| ≤
          (C/r^4+C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 + B := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,C,hT,hC,_,hbound,hker⟩ :=
    same_resolvent_current_quantitative A J α hs ht E hE D hD g 6
  let ρ := Real.sqrt T/2
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.mpr hT) (by norm_num)
  have hρT : 2*ρ^2 ≤ T := by
    have hsqrt := Real.sq_sqrt hT.le
    dsimp [ρ]
    nlinarith
  let R := hodgeSmoothingCover A J α hs ht D hD ρ hρ
  obtain ⟨B,hB,hBR⟩ := R.gammaTailKernel_rapid g hT 0
  refine ⟨C,B,hC,hB,fun r hr S u v => ?_⟩
  have hb := hbound r hr u v
  have ha : 0 < 1+dist u.val.proj v.val.proj/r := by positivity
  have hw : VolterraBounds.weight 6 (r^2) u.val.proj v.val.proj =
      (1+dist u.val.proj v.val.proj/r)^6 := by
    simp only [VolterraBounds.weight,Real.sqrt_sq_eq_abs,abs_of_pos hr]
  rw [hw] at hb
  have hdiv (x c : ℝ) (h : (1+dist u.val.proj v.val.proj/r)^6 * |x| ≤ c) :
      |x| ≤ c*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 := by
    rw [inv_pow,← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ha _)).mpr (by simpa only [mul_comm] using h)
  have htbound : |R.gammaTailKernel g T hT.le r u v| ≤ B := by
    simpa using hBR r hr u v
  rw [hker r hr S ρ hρ R hρT u v]
  calc
    _ ≤ |unitCurrentKernel A J α ht E g
          (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| +
        |unitCurrentKernel A J α ht E g
          (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| +
        |R.gammaTailKernel g T hT.le r u v| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C/r^4*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 +
        C/r^2*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 + B :=
      add_le_add (add_le_add (hdiv _ _ hb.1) (hdiv _ _ hb.2)) htbound
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
