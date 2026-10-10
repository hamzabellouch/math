import OAI.Geometry.SurfaceImmersion.Geometry.RegularPairTranslation

namespace OAI

/-! A regular translation can simultaneously avoid an additional null set
of parameter values. This refines the proved local Sard selection. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_regular_pair_translation_avoiding_null {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (U V : Set Base) (hU : IsOpen U) (hV : IsOpen V)
    (A : Set (ProjectionTarget 3)) (hA : IsOpen A) (hAn : A.Nonempty)
    (N : Set (ProjectionTarget 3)) (hN : volume N = 0) :
    ∃ a ∈ A, a ∉ N ∧ ∀ x ∈ U, ∀ y ∈ V, f x-g y = a →
      Function.Surjective (fderiv ℝ (fun z : Base × Base => f z.1-g z.2) (x,y)) := by
  let h : Base × Base → ProjectionTarget 3 := fun z => f z.1-g z.2
  let B := h '' {z | z ∈ U ×ˢ V ∧ ¬ Function.Surjective (fderiv ℝ h z)}
  have hh : ContDiff ℝ ∞ h := (hf.comp contDiff_fst).sub (hg.comp contDiff_snd)
  have hB : volume B = 0 := pair_chart_local_critical_values_null (hU.prod hV) hh.contDiffOn
  have hnull : volume (B ∪ N) = 0 := measure_union_null hB hN
  have hae : ∀ᵐ a ∂volume, a ∉ B ∪ N := by
    simp only [ae_iff,not_not]
    exact hnull
  obtain ⟨a,haA,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty A hA hAn
  refine ⟨a,haA,(fun h => ha (Or.inr h)),?_⟩
  intro x hx y hy he
  by_contra hn
  exact ha (Or.inl ⟨(x,y),⟨⟨hx,hy⟩,hn⟩,he⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
