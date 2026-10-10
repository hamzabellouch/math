import OAI.Combinatorics.Crossing.SublevelExtrema
import OAI.Combinatorics.Crossing.RoundDiskVisits

namespace OAI

noncomputable section
namespace Zarankiewicz

structure DiskPassage {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ) (τ : unitInterval) where
  enter : unitInterval
  leave : unitInterval
  enter_le_mark : enter ≤ τ
  mark_le_leave : τ ≤ leave
  enter_mem : γ enter ∈ closedRoundDisk z r
  leave_mem : γ leave ∈ closedRoundDisk z r
  all_visits : ∀ t, γ t ∈ closedRoundDisk z r → enter ≤ t ∧ t ≤ leave
  enter_boundary : 0 < enter → squaredLength (γ enter-z)=r^2
  leave_boundary : leave < 1 → squaredLength (γ leave-z)=r^2
  strict_enter : 0 < τ → enter < τ
  strict_leave : τ < 1 → τ < leave

theorem nonempty_diskPassage {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ)
    (τ : unitInterval) (hτ : squaredLength (γ τ-z) < r^2) :
    Nonempty (DiskPassage γ z r τ) := by
  obtain ⟨u,v,hu,hv,huτ,hτv,hfu,hfv,hall,hbu,hbv,hsu,hsv⟩ := sublevel_passage_extrema
    (fun t => squaredLength (γ.extend t-z)) (continuous_path_squared_distance γ z) (r^2) τ.val τ.property
    (by simpa using hτ)
  let u' : unitInterval := ⟨u,hu⟩
  let v' : unitInterval := ⟨v,hv⟩
  have heu : γ.extend u=γ u' := γ.extend_extends' u'
  have hev : γ.extend v=γ v' := γ.extend_extends' v'
  rw [heu] at hfu hbu
  rw [hev] at hfv hbv
  exact ⟨{
    enter := u'
    leave := v'
    enter_le_mark := huτ
    mark_le_leave := hτv
    enter_mem := hfu
    leave_mem := hfv
    all_visits := fun t ht => hall t.val t.property (by simpa [closedRoundDisk] using ht)
    enter_boundary := hbu
    leave_boundary := hbv
    strict_enter := hsu
    strict_leave := hsv }⟩

namespace DiskPassage
variable {a b z : Plane} {γ : Path a b} {r : ℝ} {τ : unitInterval}

theorem enter_lt_leave (P : DiskPassage γ z r τ) : P.enter < P.leave := by
  by_cases ht : τ=0
  · exact P.enter_le_mark.trans_lt (P.strict_leave (by rw [ht]; exact zero_lt_one))
  · exact (P.strict_enter (lt_of_le_of_ne (show 0 ≤ τ from τ.property.1) (Ne.symm ht))).trans_le P.mark_le_leave

theorem enter_at_source (P : DiskPassage γ z r τ) (ht : τ=0) : P.enter=0 := by
  apply le_antisymm
  · exact P.enter_le_mark.trans_eq ht
  · exact P.enter.property.1

theorem leave_at_target (P : DiskPassage γ z r τ) (ht : τ=1) : P.leave=1 := by
  apply le_antisymm
  · exact P.leave.property.2
  · exact ht.symm.trans_le P.mark_le_leave

theorem enter_pos_of_source_outside (P : DiskPassage γ z r τ)
    (h : a ∉ closedRoundDisk z r) : 0 < P.enter := by
  apply lt_of_le_of_ne (show 0 ≤ P.enter from P.enter.property.1)
  intro he
  have hh := P.enter_mem
  rw [← he] at hh
  exact h (by simpa using hh)

theorem leave_lt_one_of_target_outside (P : DiskPassage γ z r τ)
    (h : b ∉ closedRoundDisk z r) : P.leave < 1 := by
  apply lt_of_le_of_ne (show P.leave ≤ 1 from P.leave.property.2)
  intro he
  have hh := P.leave_mem
  rw [he] at hh
  exact h (by simpa using hh)

end DiskPassage
end Zarankiewicz

end

end OAI
