import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagGerms
import OAI.GroupTheory.SimpleAmenable.Arithmetic.QuadraticRectangleCounts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagSeparatingLevels
open Classical

def FlagSeparates {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (c : CutRing)
    (z w : SquareFlag a v) : Prop :=
  ¬ (flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
     flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ w)

theorem flagSeparates_ordinary_bound {a : ℕ} {v : ℝ×ℝ} {j : Fin 4} {c : CutRing}
    {z w : SquareFlag a v} (h : FlagSeparates j c z w) :
    ordinary c ∈ Set.Icc (min (cutForm a j z.val) (cutForm a j w.val))
      (max (cutForm a j z.val) (cutForm a j w.val)) := by
  unfold FlagSeparates at h
  simp only [flagMem_halfPlane] at h
  constructor
  · by_contra hn
    have hz : ordinary c < cutForm a j z.val := lt_of_lt_of_le (lt_of_not_ge hn) (min_le_left _ _)
    have hw : ordinary c < cutForm a j w.val := lt_of_lt_of_le (lt_of_not_ge hn) (min_le_right _ _)
    simp [ne_of_gt hz,ne_of_gt hw,not_lt_of_ge hz.le,not_lt_of_ge hw.le] at h
  · by_contra hn
    have hz : cutForm a j z.val < ordinary c := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hn)
    have hw : cutForm a j w.val < ordinary c := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hn)
    simp [ne_of_lt hz,ne_of_lt hw,hz,hw] at h

theorem flagSeparates_bounded_finite {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (R : ℝ) :
    {c : CutRing | FlagSeparates j c z w ∧ |conjugate c| ≤ R}.Finite := by
  let b := |R|+1
  have hb : 0 < b := by dsimp [b]; positivity
  let x := min (cutForm a j z.val) (cutForm a j w.val)
  let y := max (cutForm a j z.val) (cutForm a j w.val)
  apply (cutRectangle_finite x (-b) (y-x) (2*b) (by positivity)).subset
  intro c hc
  have ho := flagSeparates_ordinary_bound hc.1
  have ht := abs_le.mp hc.2
  change _ ∧ _
  constructor
  · simpa [x,y] using ho
  · constructor <;> dsimp [b] <;> linarith [le_abs_self R]

theorem flagSeparates_exists_min {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (h : ∃ c,FlagSeparates j c z w) :
    ∃ c,FlagSeparates j c z w ∧ ∀ d,FlagSeparates j d z w →
      |conjugate c| ≤ |conjugate d| := by
  obtain ⟨c,hc⟩ := h
  let S : Set CutRing := {d : CutRing | FlagSeparates j d z w ∧ |conjugate d| ≤ |conjugate c|}
  have hS : S.Finite := flagSeparates_bounded_finite j z w _
  have hn : S.Nonempty := ⟨c,hc,le_rfl⟩
  obtain ⟨d,hd,hmin⟩ := Set.exists_min_image S (fun e => |conjugate e|) hS hn
  refine ⟨d,hd.1,fun e he => ?_⟩
  by_cases hec : |conjugate e| ≤ |conjugate c|
  · exact hmin e ⟨he,hec⟩
  · exact hd.2.trans (le_of_not_ge hec)

theorem flagMem_halfPlane_local_translation {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (j : Fin 4) (c : CutRing) (z z' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2)) :
    flagMem ⟨halfPlane a j (c+integralCutForm a j u),halfPlane_mem _ _ _⟩ z' ↔
      flagMem ⟨halfPlane a j c,halfPlane_mem _ _ _⟩ z := by
  rw [flagMem_halfPlane,flagMem_halfPlane,hz,cutForm_add,cutForm_ordinary,map_add]
  simp only [add_left_inj,add_lt_add_iff_right]

theorem flagSeparates_local_translation {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (j : Fin 4) (c : CutRing) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2)) :
    FlagSeparates j (c+integralCutForm a j u) z' w' ↔ FlagSeparates j c z w := by
  unfold FlagSeparates
  rw [flagMem_halfPlane_local_translation u j c z z' hz,
    flagMem_halfPlane_local_translation u j c w w' hw]

theorem separating_min_translation_bound {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (j : Fin 4) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2))
    (c d : CutRing) (hc : FlagSeparates j c z w) (hd : FlagSeparates j d z' w')
    (hcmin : ∀ e,FlagSeparates j e z w → |conjugate c| ≤ |conjugate e|)
    (hdmin : ∀ e,FlagSeparates j e z' w' → |conjugate d| ≤ |conjugate e|) :
    abs (|conjugate c|-|conjugate d|) ≤ |conjugate (integralCutForm a j u)| := by
  have hd' := hdmin (c+integralCutForm a j u)
    ((flagSeparates_local_translation u j c z w z' w' hz hw).mpr hc)
  have hc' := hcmin (d-integralCutForm a j u) (by
    apply (flagSeparates_local_translation u j (d-integralCutForm a j u) z w z' w' hz hw).mp
    simpa only [sub_add_cancel] using hd)
  have h₁ := abs_add_le (conjugate c) (conjugate (integralCutForm a j u))
  have h₂ : |conjugate d-conjugate (integralCutForm a j u)| ≤ |conjugate d|+|conjugate (integralCutForm a j u)| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (conjugate d) 0 (conjugate (integralCutForm a j u))
  simp only [map_add,map_sub] at hd' hc'
  apply abs_le.mpr
  constructor <;> linarith

end FlagSeparatingLevels

end SimpleAmenable
end
end

end OAI
