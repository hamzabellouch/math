import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionFunctions.DimensionContent
import OAI.Analysis.JiangSu.CStarAlgebras.ContinuousOrthogonalSeparation

namespace OAI

noncomputable section


namespace Pureness
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]

lemma dimensionCompactCapacity_sup_disjoint (r : C(X, ℝ≥0) → ℝ≥0∞)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g)
    (K L : Compacts X) (hKL : Disjoint (K : Set X) L) :
    dimensionCompactCapacity r (K ⊔ L) = dimensionCompactCapacity r K + dimensionCompactCapacity r L := by
  apply le_antisymm (dimensionCompactCapacity_sup_le r hsub K L)
  obtain ⟨u,v,hu,hv,hu1,hv1,huv⟩ := continuous_nnreal_orthogonal_separators K.isCompact.isClosed L.isCompact.isClosed hKL
  apply le_iInf₂
  intro f hf
  have hfu : ∀ x ∈ K, 1 ≤ (f*u) x := by
    intro x hx
    simpa only [ContinuousMap.mul_apply,hu x hx,mul_one] using hf x (Or.inl hx)
  have hfv : ∀ x ∈ L, 1 ≤ (f*v) x := by
    intro x hx
    simpa only [ContinuousMap.mul_apply,hv x hx,mul_one] using hf x (Or.inr hx)
  have huv1 : u+v ≤ 1 := by
    intro x
    change u x+v x ≤ 1
    have hz : u x*v x = 0 := congrArg (fun g : C(X, ℝ≥0) => g x) huv
    rcases mul_eq_zero.mp hz with hz | hz
    · rw [hz,zero_add]
      exact hv1 x
    · rw [hz,add_zero]
      exact hu1 x
  have horth' : (f*u)*(f*v) = 0 := by
    calc
      (f*u)*(f*v) = (f*f)*(u*v) := by ring
      _ = 0 := by rw [huv,mul_zero]
  calc
    dimensionCompactCapacity r K + dimensionCompactCapacity r L ≤ r (f*u)+r (f*v) :=
      add_le_add (dimensionCompactCapacity_le r K (f*u) hfu) (dimensionCompactCapacity_le r L (f*v) hfv)
    _ = r (f*u+f*v) := (horth (f*u) (f*v) horth').symm
    _ ≤ r f := hmono (by
      intro x
      change f x*u x+f x*v x ≤ f x
      have h := mul_le_mul_of_nonneg_left (huv1 x) (show 0 ≤ f x from bot_le)
      change f x*(u x+v x) ≤ f x*1 at h
      simpa only [mul_add,mul_one] using h)

def dimensionContent (r : C(X, ℝ≥0) → ℝ≥0∞) (hfinite : r 1 ≠ ⊤)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g) : Content X where
  toFun K := (dimensionCompactCapacity r K).toNNReal
  mono' K L h := ENNReal.toNNReal_mono (dimensionCompactCapacity_ne_top r hfinite L)
    (dimensionCompactCapacity_mono r h)
  sup_disjoint' K L h _ _ := by
    rw [dimensionCompactCapacity_sup_disjoint r hmono hsub horth K L h,
      ENNReal.toNNReal_add (dimensionCompactCapacity_ne_top r hfinite K) (dimensionCompactCapacity_ne_top r hfinite L)]
  sup_le' K L := by
    rw [← ENNReal.toNNReal_add (dimensionCompactCapacity_ne_top r hfinite K) (dimensionCompactCapacity_ne_top r hfinite L)]
    exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr ⟨dimensionCompactCapacity_ne_top r hfinite K,
      dimensionCompactCapacity_ne_top r hfinite L⟩) (dimensionCompactCapacity_sup_le r hsub K L)

lemma dimensionContent_apply (r : C(X, ℝ≥0) → ℝ≥0∞) (hfinite : r 1 ≠ ⊤)
    (hmono : Monotone r) (hsub : ∀ f g, r (f+g) ≤ r f+r g)
    (horth : ∀ f g, f*g = 0 → r (f+g) = r f+r g) (K : Compacts X) :
    dimensionContent r hfinite hmono hsub horth K = dimensionCompactCapacity r K :=
  ENNReal.coe_toNNReal (dimensionCompactCapacity_ne_top r hfinite K)

end Pureness


namespace Pureness
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

end Pureness

end

end OAI
