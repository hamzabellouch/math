import OAI.Probability.DilutedSpin.CoordinateFiber
import OAI.Probability.DilutedSpin.ScheduledGeometry

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance regularScheduleShiftPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

/-- An order-preserving re-assignment of every actual branching vertex
preserves the strict ancestral schedule. -/
lemma admissible_order_map (S : ReducedTopology) (q q' : S.Vertex → ℕ)
    {lo lo' hi hi' : ℕ} (hq : Admissible S q lo hi)
    (hl : ∀ v, lo' ≤ q' v) (hu : ∀ v, q' v < hi')
    (ho : ∀ u v, q u < q v → q' u < q' v) : Admissible S q' lo' hi' := by
  induction S generalizing lo lo' hi hi' with
  | leaf => trivial
  | node k hk C ih =>
    refine ⟨hl none,hu none,?_⟩
    intro i
    apply ih i (fun v => q (some ⟨i,v⟩)) (fun v => q' (some ⟨i,v⟩)) (hq.2.2 i)
    · intro v
      have hv := admissible_lower (C i) (fun v => q (some ⟨i,v⟩)) (hq.2.2 i) v
      exact ho none (some ⟨i,v⟩) hv
    · intro v; exact hu _
    · intro u v huv; exact ho _ _ huv

variable {L : ℕ} [NeZero L]

lemma regular_depth_gap {α : Type} {η : ℝ} (hlarge : 1<η*(L:ℝ))
    {q : α → Fin L} (hr : DepthAverage.Regular η q) (u v : α)
    (huv : (q u).val < (q v).val) : (q u).val+1 < (q v).val := by
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have hne : u ≠ v := by intro h; subst v; omega
  have hh := hr.2 u v hne
  have hd : DepthAverage.normalized (q u) ≤ DepthAverage.normalized (q v) :=
    div_le_div_of_nonneg_right (by exact_mod_cast huv.le) hL.le
  rw [abs_of_nonpos (sub_nonpos.mpr hd)] at hh
  have hcast : ((q u).val:ℝ)+1 < ((q v).val:ℝ) := by
    unfold DepthAverage.normalized at hh
    have hh' : η*(L:ℝ) < ((q v).val:ℝ)-((q u).val:ℝ) := by
      apply (lt_div_iff₀ hL).mp
      rw [sub_div]
      linarith [hh]
    linarith
  exact_mod_cast hcast

lemma shifted_val_bounds {α : Type} {η : ℝ} (hlarge : 1<η*(L:ℝ))
    {q : α → Fin L} (hr : DepthAverage.Regular η q) (s : α → Bool) (v : α) :
    (q v).val ≤ (DepthAverage.shiftPerm (s v) (q v)).val ∧
    (DepthAverage.shiftPerm (s v) (q v)).val ≤ (q v).val+1 := by
  have hrm := DepthAverage.regular_room hlarge hr v
  cases hs : s v with
  | false =>
    simp only [DepthAverage.shiftPerm,Bool.false_eq_true,ite_false,Equiv.refl_apply]
    omega
  | true =>
    simp only [DepthAverage.shiftPerm,ite_true,DepthAverage.rotate_val_of_room _ hrm]
    omega

/-- All intermediate positive one-step shifts of a regular admissible
assignment are genuine admissible shapes, with the original horizon. -/
theorem admissible_regular_shift (S : ReducedTopology) {η : ℝ}
    (hlarge : 1<η*(L:ℝ)) (q : S.Vertex → Fin L)
    {lo : ℕ} (hq : Admissible S (fun v => (q v).val) lo L) (hr : DepthAverage.Regular η q)
    (s : S.Vertex → Bool) :
    Admissible S (fun v => (DepthAverage.shiftPerm (s v) (q v)).val) lo L := by
  apply admissible_order_map S (fun v => (q v).val) _ hq
  · intro v
    exact (admissible_lower S _ hq v).trans (shifted_val_bounds hlarge hr s v).1
  · intro v; exact (DepthAverage.shiftPerm (s v) (q v)).isLt
  · intro u v huv
    have hg := regular_depth_gap hlarge hr u v huv
    have hb := shifted_val_bounds hlarge hr s u
    have hc := shifted_val_bounds hlarge hr s v
    omega

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
