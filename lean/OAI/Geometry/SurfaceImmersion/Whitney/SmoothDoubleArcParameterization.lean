import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleArcExtension
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleArcChartPartition

namespace OAI

/-! An embedded compact topological arc in the actual transverse double
locus admits a smooth regular parameterization with the same image and endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

theorem smooth_double_arc_parameterization
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    {γ : ℝ → surfaceDoublePairs f} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (hi : InjOn γ (Icc a b)) :
    ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a b ∧
      P.lift P.arc.start = γ a ∧ P.lift P.arc.finish = γ b := by
  obtain ⟨τ,N,hzero,hmono,hbounds,hend,hcharts⟩ :=
    double_arc_chart_partition hf hreg hab.le hγ
  have hstep : ∀ n, τ n = a ∨ (a < τ n ∧ ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a (τ n) ∧
      P.lift P.arc.start = γ a ∧ P.lift P.arc.finish = γ (τ n)) := by
    intro n
    induction n with
    | zero => exact Or.inl hzero
    | succ n ih =>
      have hle : τ n ≤ τ (n+1) := hmono (Nat.le_succ n)
      by_cases heq : τ n = τ (n+1)
      · simpa only [Nat.succ_eq_add_one,← heq] using ih
      have hlt : τ n < τ (n+1) := lt_of_le_of_ne hle heq
      obtain ⟨c,hc⟩ := hcharts n
      have hsub : Icc (τ n) (τ (n+1)) ⊆ Icc a b :=
        Icc_subset_Icc (hbounds n).1 (hbounds (n+1)).2
      rcases ih with hna | ⟨han,P,hPi,hPl,hPr⟩
      · obtain ⟨P,hPi,hPl,hPr⟩ := c.smooth_double_arc hlt (hγ.mono hsub) (hi.mono hsub) hc
        refine Or.inr ⟨hna ▸ hlt,P,?_,?_,hPr⟩
        · simpa only [hna] using hPi
        · simpa only [hna] using hPl
      · have hsub' : Icc a (τ (n+1)) ⊆ Icc a b := Icc_subset_Icc le_rfl (hbounds (n+1)).2
        obtain ⟨R,hRi,hRl,hRr⟩ := extend_smooth_double_arc han hlt
          (hγ.mono hsub') (hi.mono hsub') P hPi hPl hPr c hc
        exact Or.inr ⟨han.trans hlt,R,hRi,hRl,hRr⟩
  have hN : τ N = b := hend N le_rfl
  rcases hstep N with he | ⟨_,P,hPi,hPl,hPr⟩
  · exact False.elim (hab.ne (he.symm.trans hN))
  · exact ⟨P,by simpa only [hN] using hPi,hPl,by simpa only [hN] using hPr⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
