import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryResidueRegular
open Construction

def Regular (q : ℕ) : {l : ℕ} → History l → Prop
  | _, h => (h.root.frequency : ZMod q) ≠ 0 ∧
      (∀ n ∈ h.root.values, (n : ZMod q) ≠ 0) ∧
      match h with
      | .leaf _ => True
      | .node _ _ _ _ _ left right => Regular q left ∧ Regular q right
termination_by l _ => l

theorem intCast_ne_zero_of_natAbs_lt {q : ℕ} {s : ℤ}
    (hs : s ≠ 0) (hlt : s.natAbs < q) : (s : ZMod q) ≠ 0 := by
  intro hz
  have hd : q ∣ s.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd s q).mp hz)
  have hp : 0 < s.natAbs := Int.natAbs_pos.mpr hs
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hp hd)

theorem supported_regular {q l : ℕ} [Fact q.Prime] {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hq : q ∈ outside)
    (hV : ∀ j ≤ l, V j < q) : Regular q h := by
  have hfreq : (h.root.frequency : ZMod q) ≠ 0 := by
    apply intCast_ne_zero_of_natAbs_lt (History.supported_root_frequency_ne_zero hs)
    exact (History.supported_root_frequency_bound hs).trans_lt (hV l le_rfl)
  have hvalues : ∀n∈h.root.values,(n:ZMod q)≠0 := by
    intro n hn
    have hc := History.supported_root_coprime hs
    have hcross := (List.pairwise_append.mp hc).2.2
    exact ((ZMod.isUnit_iff_coprime n q).mpr (hcross n hn q hq)).ne_zero
  rw [Regular.eq_def]
  refine ⟨hfreq,hvalues,?_⟩
  cases h with
  | leaf a => trivial
  | @node l a p u hp hm left right =>
      exact ⟨supported_regular left (History.supported_left hs) hq
          (fun j hj => hV j (hj.trans (Nat.le_succ l))),
        supported_regular right (History.supported_right hs) hq
          (fun j hj => hV j (hj.trans (Nat.le_succ l)))⟩
termination_by l

theorem frequency_ne_zero {q l : ℕ} {h : History l} (hr : Regular q h) :
    (h.root.frequency : ZMod q) ≠ 0 := by rw [Regular.eq_def] at hr; exact hr.1

theorem value_ne_zero {q l : ℕ} {h : History l} (hr : Regular q h) {n : ℕ}
    (hn : n ∈ h.root.values) : (n : ZMod q) ≠ 0 := by
  rw [Regular.eq_def] at hr
  exact hr.2.1 n hn

theorem left_regular {q l : ℕ} {a : State} {p : ℕ} {u hp hm : List SmallSlot}
    {left right : History l} (hr : Regular q (History.node a p u hp hm left right)) :
    Regular q left := by rw [Regular] at hr; exact hr.2.2.1

theorem right_regular {q l : ℕ} {a : State} {p : ℕ} {u hp hm : List SmallSlot}
    {left right : History l} (hr : Regular q (History.node a p u hp hm left right)) :
    Regular q right := by rw [Regular] at hr; exact hr.2.2.2

end Ostmann.Arithmetic.HistoryResidueRegular

end

end OAI
