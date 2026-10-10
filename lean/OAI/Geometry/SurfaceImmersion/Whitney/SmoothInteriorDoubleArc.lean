import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleArcParameterization
import OAI.Geometry.SurfaceImmersion.Whitney.SimpleCrosscapArc

namespace OAI

/-! Compact interior segments of the actual crosscap-connecting path
inherit smooth regular embedded double-curve parameterizations. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem smooth_interior_double_arc
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish =
        Γ '' {t : I | a ≤ (t:ℝ) ∧ (t:ℝ) ≤ b} ∧
      P.arc.curve P.arc.start = Γ ⟨a,⟨ha.le,(hab.trans hb).le⟩⟩ ∧
      P.arc.curve P.arc.finish = Γ ⟨b,⟨(ha.trans hab).le,hb.le⟩⟩ := by
  let κ := projIcc a b hab.le
  let θ : ℝ → I := fun t => ⟨(κ t).val,⟨ha.le.trans (κ t).property.1,(κ t).property.2.trans hb.le⟩⟩
  have hκc : Continuous κ := continuous_projIcc
  have hθ : Continuous θ := (continuous_subtype_val.comp hκc).subtype_mk _
  let γ : ℝ → surfaceDoublePairs f := fun t =>
    ⟨Γ (θ t),hne (θ t) (ha.trans_le (κ t).property.1) ((κ t).property.2.trans_lt hb),heq (θ t)⟩
  have hγ : Continuous γ := (hΓ.comp hθ).subtype_mk _
  have hκ : ∀ t ∈ Icc a b, (κ t).val = t := by
    intro t ht
    exact congrArg Subtype.val (projIcc_of_mem hab.le ht)
  have hγinj : InjOn γ (Icc a b) := by
    intro t ht u hu he
    have hθeq : θ t = θ u := hinj (congrArg Subtype.val he)
    have hval := congrArg Subtype.val hθeq
    change (κ t).val = (κ u).val at hval
    rwa [hκ t ht,hκ u hu] at hval
  obtain ⟨P,hPi,hPl,hPr⟩ := smooth_double_arc_parameterization hf hreg hab hγ.continuousOn hγinj
  have hi : (fun t => (γ t).val) '' Icc a b = Γ '' {t : I | a ≤ (t:ℝ) ∧ (t:ℝ) ≤ b} := by
    apply Set.Subset.antisymm
    · rintro y ⟨t,ht,rfl⟩
      exact ⟨θ t,⟨(κ t).property.1,(κ t).property.2⟩,rfl⟩
    · rintro y ⟨t,ht,rfl⟩
      refine ⟨(t:ℝ),ht,?_⟩
      change Γ (θ (t:ℝ)) = Γ t
      apply congrArg Γ
      apply Subtype.ext
      exact hκ t ht
  refine ⟨P,hPi.trans hi,?_,?_⟩
  · rw [P.curve_eq,hPl]
    change Γ (θ a) = _
    apply congrArg Γ
    apply Subtype.ext
    exact hκ a (left_mem_Icc.mpr hab.le)
  · rw [P.curve_eq,hPr]
    change Γ (θ b) = _
    apply congrArg Γ
    apply Subtype.ext
    exact hκ b (right_mem_Icc.mpr hab.le)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
