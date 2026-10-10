import OAI.NumberTheory.Ostmann.Construction.CanonicalEnumeration

namespace OAI

noncomputable section
namespace Ostmann.Construction

theorem allowedFrequency_bound (V : ℕ → ℕ) (l : ℕ) (v : AllowedFrequency V l) :
    v.val.natAbs≤V l := by
  have h := Finset.mem_Icc.mp v.property
  have ha : |v.val|≤(V l:ℤ) := abs_le.mpr h
  have ha' : ((v.val.natAbs:ℕ):ℤ)≤(V l:ℤ) := by
    simpa only [Int.natCast_natAbs] using ha
  exact_mod_cast ha'

theorem decodedPivot_eq_of_reversal (a : State) (v w : ℤ)
    (u hp hm : List SmallSlot) (p : ℕ) (hs : a.frequency≠0)
    (hu : 0<(u.map SmallSlot.value).prod)
    (heq : Arithmetic.reversalNumerator v w
      ((a.giantPlus*(hp.map SmallSlot.value).prod:ℕ):ℤ)
      ((a.giantMinus*(hm.map SmallSlot.value).prod:ℕ):ℤ) =
        a.frequency*((u.map SmallSlot.value).prod:ℤ)*(p:ℤ)) :
    decodedPivot a v w u hp hm=p := by
  have hu0 : ((u.map SmallSlot.value).prod:ℤ)≠0 := by exact_mod_cast hu.ne'
  have hden : a.frequency*((u.map SmallSlot.value).prod:ℤ)≠0 := mul_ne_zero hs hu0
  unfold decodedPivot
  rw [heq, Int.mul_ediv_cancel_left _ hden, Int.toNat_natCast]

theorem assignedSlots_extracted_roles (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (u : SourceAssignment sources (Template.extracted j T)) :
    ∀ q∈assignedSlots sources (Template.extracted j T) u, q.role=.compensation j := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  have hmem : (Template.extracted j T)[i]∈Template.extracted j T := List.getElem_mem i.isLt
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

theorem decoded_children_small_perm (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V (l+1))
    (hlen : a.small.length=(Template.current seed (l+1)).length) :
    let T := Template.current seed l
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    let n := (Template.remainder (l+1) T).length
    ((History.nodeLeft (decodeHistory sources seed V (l+1) a c)).root.small.Perm
      (u++a.small.take n)) ∧
    ((History.nodeRight (decodeHistory sources seed V (l+1) a c)).root.small.Perm
      (u++a.small.drop n)) := by
  dsimp only
  let T := Template.current seed l
  let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
  let n := (Template.remainder (l+1) T).length
  have hlen' : a.small.length=n+n := by
    simpa only [Template.current, List.length_append, T, n] using hlen
  have hu : u.length=(Template.extracted (l+1) T).length := assignedSlots_length _ _ _
  have hp : (a.small.take n).length=n := by rw [List.length_take,hlen']; omega
  have hm : (a.small.drop n).length=n := by rw [List.length_drop,hlen']; omega
  constructor
  · simpa only [decodeHistory, History.nodeLeft, decodeHistory_root, T, u, n] using
      Template.reinsert_perm (l+1) T u (a.small.take n) hu hp
  · simpa only [decodeHistory, History.nodeRight, decodeHistory_root, T, u, n] using
      Template.reinsert_perm (l+1) T u (a.small.drop n) hu hm

end Ostmann.Construction

end

end OAI
