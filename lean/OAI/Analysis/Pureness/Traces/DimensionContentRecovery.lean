import OAI.Analysis.Pureness.Traces.DimensionContentMeasure
import Mathlib.Topology.Instances.NNReal.Lemmas

namespace OAI
noncomputable section
namespace CuntzPureness
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [TopologicalSpace X]

def continuousNNRealCut (ε : ℝ≥0) (f : C(X, ℝ≥0)) : C(X, ℝ≥0) :=
  ⟨fun x => f x-ε, f.continuous.sub continuous_const⟩

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem dimensionContent_measure_support
    (r : C(X, ℝ≥0) → ℝ≥0∞) (hfinite : r 1 ≠ ⊤)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g)
    (hsupport : ∀ f g, (∀ x, 0 < f x → 0 < g x) → r f ≤ r g)
    (hcuts : ∀ f, r f = ⨆ (ε : ℝ≥0) (_ : 0 < ε), r (continuousNNRealCut ε f))
    (f : C(X, ℝ≥0)) :
    (dimensionContent r hfinite hmono hsub horth).measure {x | 0 < f x} = r f := by
  let c := dimensionContent r hfinite hmono hsub horth
  have hU : IsOpen {x | 0 < f x} := isOpen_lt continuous_const f.continuous
  rw [Content.measure_apply _ hU.measurableSet,Content.outerMeasure_of_isOpen _ _ hU]
  apply le_antisymm
  · apply iSup₂_le
    intro K hK
    obtain ⟨g,hgK,hgc,hgU,hg⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen K.isCompact hU hK
    let g' : C(X, ℝ≥0) := ⟨fun x => (g x).toNNReal, continuous_real_toNNReal.comp g.continuous⟩
    have hg'K : ∀ x ∈ K, 1 ≤ g' x := by
      intro x hx
      change 1 ≤ (g x).toNNReal
      rw [hgK hx]
      norm_num
    rw [dimensionContent_apply]
    apply (dimensionCompactCapacity_le r K g' hg'K).trans
    apply hsupport
    intro x hx
    apply hgU
    apply subset_closure
    change g x ≠ 0
    have hp : 0 < g x := Real.toNNReal_pos.mp hx
    exact hp.ne'
  · rw [hcuts f]
    apply iSup₂_le
    intro ε hε
    let K : Compacts X := ⟨{x | ε ≤ f x}, (isClosed_le continuous_const f.continuous).isCompact⟩
    have hKU : (K : Set X) ⊆ {x | 0 < f x} := fun x hx => hε.trans_le hx
    apply le_trans _ (c.le_innerContent K ⟨_,hU⟩ hKU)
    rw [dimensionContent_apply]
    apply le_iInf₂
    intro g hg
    apply hsupport
    intro x hx
    have hxε : ε < f x := tsub_pos_iff_lt.mp hx
    exact zero_lt_one.trans_le (hg x hxε.le)
end CuntzPureness

end

end OAI
