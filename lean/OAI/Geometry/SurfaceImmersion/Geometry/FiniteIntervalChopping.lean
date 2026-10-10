import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

/-! Cutting a real interval at a finite vertex set produces uniquely
determined consecutive open subintervals. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def ConsecutiveVertices (S : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ t ∈ S, ¬ (a < t ∧ t < b)

theorem exists_consecutive_interval (S : Finset ℝ) {x : ℝ} (hx : x ∉ S)
    (hleft : ∃ a ∈ S, a < x) (hright : ∃ b ∈ S, x < b) :
    ∃ a b, ConsecutiveVertices S a b ∧ a < x ∧ x < b := by
  classical
  let L := S.filter (fun a => a < x)
  let R := S.filter (fun b => x < b)
  have hL : L.Nonempty := by
    obtain ⟨a,ha,hax⟩ := hleft
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hax⟩⟩
  have hR : R.Nonempty := by
    obtain ⟨b,hb,hxb⟩ := hright
    exact ⟨b,Finset.mem_filter.mpr ⟨hb,hxb⟩⟩
  let a := L.max' hL
  let b := R.min' hR
  have ha : a ∈ S ∧ a < x := Finset.mem_filter.mp (L.max'_mem hL)
  have hb : b ∈ S ∧ x < b := Finset.mem_filter.mp (R.min'_mem hR)
  refine ⟨a,b,⟨ha.1,hb.1,ha.2.trans hb.2,?_⟩,ha.2,hb.2⟩
  intro t ht hab
  rcases lt_trichotomy t x with htx | rfl | hxt
  · have hta : t ≤ a := L.le_max' t (Finset.mem_filter.mpr ⟨ht,htx⟩)
    linarith [hab.1]
  · exact hx ht
  · have hbt : b ≤ t := R.min'_le t (Finset.mem_filter.mpr ⟨ht,hxt⟩)
    linarith [hab.2]

theorem consecutive_intervals_equal (S : Finset ℝ) {a b c d x : ℝ}
    (hab : ConsecutiveVertices S a b) (hcd : ConsecutiveVertices S c d)
    (hx : a < x ∧ x < b) (hy : c < x ∧ x < d) : a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with h | h | h
    · exact False.elim (hab.2.2.2 c hcd.1 ⟨h,hy.1.trans hx.2⟩)
    · exact h
    · exact False.elim (hcd.2.2.2 a hab.1 ⟨h,hx.1.trans hy.2⟩)
  have hbd : b = d := by
    rcases lt_trichotomy b d with h | h | h
    · exact False.elim (hcd.2.2.2 b hab.2.1 ⟨hy.1.trans hx.2,h⟩)
    · exact h
    · exact False.elim (hab.2.2.2 d hcd.2.1 ⟨hx.1.trans hy.2,h⟩)
  exact ⟨hac,hbd⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
