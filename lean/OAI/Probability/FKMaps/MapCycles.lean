import Mathlib

namespace OAI

/-! Cut/join identities for tour permutations. Fixed points are retained as
one-element cycles, as required by the Euler-characteristic map definition. -/
noncomputable section
open Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

lemma formPerm_cut (a b : α) (L R : List α)
    (h : (a :: (L ++ b :: R)).Nodup) :
    (a :: (L ++ b :: R)).formPerm =
      swap a b * (a :: L).formPerm * (b :: R).formPerm := by
  induction L generalizing a with
  | nil => simp
  | cons c L ih =>
    have hab : a ≠ b := fun he => h.notMem (by simp [he])
    have hcb : c ≠ b := fun he => h.of_cons.notMem (by simp [he])
    have hcomm : swap a c * swap c b = swap a b * swap a c := by
      rw [mul_swap_eq_swap_mul]
      simp [swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]
    simp only [List.cons_append, List.formPerm_cons_cons]
    rw [ih c h.of_cons]
    simp only [← mul_assoc]
    rw [hcomm]

lemma swap_mul_formPerm_cut (a b : α) (L R : List α)
    (h : (a :: (L ++ b :: R)).Nodup) :
    swap a b * (a :: (L ++ b :: R)).formPerm =
      (a :: L).formPerm * (b :: R).formPerm := by
  rw [formPerm_cut a b L R h]
  simp [← mul_assoc]

lemma sameCycle_formPerm_of_mem {l : List α} (hn : l.Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) : l.formPerm.SameCycle x y := by
  rcases l with _ | ⟨a, _ | ⟨b, L⟩⟩
  · simp at hx
  · simp only [List.mem_singleton] at hx hy
    exact (hx.trans hy.symm).sameCycle _
  · apply (List.isCycle_formPerm hn (by simp)).sameCycle
    · exact (List.formPerm_apply_mem_ne_self_iff _ hn _ hx).mpr (by simp)
    · exact (List.formPerm_apply_mem_ne_self_iff _ hn _ hy).mpr (by simp)

lemma pow_eq_on_list (p : Perm α) (l : List α)
    (hp : ∀ x ∈ l, p x = l.formPerm x) {x : α} (hx : x ∈ l) (k : ℕ) :
    (p ^ k) x = (l.formPerm ^ k) x ∧ (p ^ k) x ∈ l := by
  induction k with
  | zero => exact ⟨rfl, hx⟩
  | succ k ih =>
    simp only [pow_succ', mul_apply]
    exact ⟨(hp _ ih.2).trans (congrArg l.formPerm ih.1),
      hp _ ih.2 ▸ l.formPerm_apply_mem_of_mem ih.2⟩

lemma sameCycle_of_list [Finite α] (p : Perm α) {l : List α} (hn : l.Nodup)
    (hp : ∀ x ∈ l, p x = l.formPerm x) {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    p.SameCycle x y := by
  obtain ⟨k,hk⟩ := (sameCycle_formPerm_of_mem hn hx hy).exists_nat_pow_eq
  exact ⟨k, by simpa using (pow_eq_on_list p l hp hx k).1.trans hk⟩

abbrev Orbits (p : Perm α) := Quotient (SameCycle.setoid p)

/-- A partition into nonempty cyclic lists counts all orbits, including fixed
points. The local action condition makes this independent of a chosen
representative of the quotient. -/
lemma card_orbits_eq_of_lists [Finite α] {β : Type*} [Finite β]
    (p : Perm α) (l : β → List α) (hn : ∀ i, (l i).Nodup)
    (hne : ∀ i, ∃ x, x ∈ l i)
    (hc : ∀ x, ∃! i, x ∈ l i)
    (hp : ∀ i x, x ∈ l i → p x = (l i).formPerm x) :
    Nat.card (Orbits p) = Nat.card β := by
  classical
  let idx : α → β := fun x => (hc x).choose
  have hm (x : α) : x ∈ l (idx x) := (hc x).choose_spec.1
  have hu {x : α} {i : β} (hi : x ∈ l i) : idx x = i :=
    ((hc x).choose_spec.2 i hi).symm
  have he {x y : α} : p.SameCycle x y ↔ idx x = idx y := by
    constructor
    · intro h
      obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
      have hh := (pow_eq_on_list p (l (idx x)) (hp (idx x)) (hm x) k).2
      rw [hk] at hh
      exact (hu hh).symm
    · intro h
      exact sameCycle_of_list p (hn (idx x)) (hp (idx x)) (hm x) (h ▸ hm y)
  let e : Orbits p ≃ β :=
    { toFun := Quotient.lift idx (fun _ _ h => he.mp h)
      invFun := fun i => Quotient.mk _ ((hne i).choose)
      left_inv := by
        intro q
        induction q using Quotient.inductionOn with
        | h x =>
          apply Quotient.sound
          apply he.mpr
          exact hu ((hne (idx x)).choose_spec)
      right_inv := by
        intro i
        exact hu ((hne i).choose_spec) }
  exact Nat.card_congr e

/-- Canonical cyclic list, retaining one-element fixed cycles. -/
def orbitList [Fintype α] (p : Perm α) (x : α) : List α :=
  if p x = x then [x] else p.toList x

lemma nodup_orbitList [Fintype α] (p : Perm α) (x : α) :
    (orbitList p x).Nodup := by
  unfold orbitList
  split_ifs <;> simp [nodup_toList]

lemma mem_orbitList [Fintype α] (p : Perm α) (x y : α) :
    y ∈ orbitList p x ↔ p.SameCycle x y := by
  classical
  unfold orbitList
  split_ifs with h
  · simp only [List.mem_singleton]
    exact ⟨fun he => (he.symm).sameCycle p,fun he => (he.eq_of_left h).symm⟩
  · simp [mem_toList_iff,h]

lemma orbitList_action [Fintype α] (p : Perm α) (x y : α)
    (hy : y ∈ orbitList p x) : p y = (orbitList p x).formPerm y := by
  classical
  have hxy := (mem_orbitList p x y).mp hy
  unfold orbitList
  split_ifs with h
  · have he := hxy.eq_of_left h
    subst y
    simpa using h
  · rw [formPerm_toList,hxy.cycleOf_apply]

/-- Splitting one part of a finite list partition into two consecutive,
nonempty pieces adds exactly one block, without discarding fixed points. -/
def splitFamily {β : Type*} [DecidableEq β] (l : β → List α) (i₀ : β)
    (L R : List α) : ({i : β // i ≠ i₀} ⊕ Bool) → List α
  | Sum.inl i => l i
  | Sum.inr false => L
  | Sum.inr true => R

omit [DecidableEq α] in
lemma splitFamily_partition {β : Type*} [DecidableEq β] (l : β → List α)
    (hn : ∀ i, (l i).Nodup) (hc : ∀ x, ∃! i, x ∈ l i)
    (i₀ : β) (L R : List α) (he : l i₀ = L ++ R) :
    ∀ x, ∃! i, x ∈ splitFamily l i₀ L R i := by
  intro x
  have hd : List.Disjoint L R := List.disjoint_iff_ne.mpr (List.nodup_append.mp (he ▸ hn i₀)).2.2
  have hoff {i : β} (hi : i ≠ i₀) (hx : x ∈ l i) : x ∉ L ∧ x ∉ R := by
    constructor <;> intro h
    all_goals
      have hh : x ∈ l i₀ := by rw [he]; simp [h]
      exact hi (((hc x).unique hx hh))
  have hinj : ∀ i j, x ∈ splitFamily l i₀ L R i →
      x ∈ splitFamily l i₀ L R j → i = j := by
    intro i j hi hj
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext ((hc x).unique hi hj))
      | inr b => cases b
                 · exact ((hoff i.property hi).1 hj).elim
                 · exact ((hoff i.property hi).2 hj).elim
    | inr b =>
      cases j with
      | inl j => cases b
                 · exact ((hoff j.property hj).1 hi).elim
                 · exact ((hoff j.property hj).2 hi).elim
      | inr c =>
        cases b <;> cases c
        · rfl
        · exact (List.disjoint_left.mp hd hi hj).elim
        · exact (List.disjoint_left.mp hd hj hi).elim
        · rfl
  obtain ⟨i,hi,_⟩ := hc x
  by_cases h : i = i₀
  · subst i
    rw [he,List.mem_append] at hi
    rcases hi with hi | hi
    · exact ⟨Sum.inr false,hi,fun j hj => hinj j _ hj hi⟩
    · exact ⟨Sum.inr true,hi,fun j hj => hinj j _ hj hi⟩
  · exact ⟨Sum.inl ⟨i,h⟩,hi,fun j hj => hinj j _ hj hi⟩

lemma card_orbits_cut [Finite α] {β : Type*} [Finite β]
    (p : Perm α) (l : β → List α) (hn : ∀ i, (l i).Nodup)
    (hne : ∀ i, ∃ x, x ∈ l i) (hc : ∀ x, ∃! i, x ∈ l i)
    (hp : ∀ i x, x ∈ l i → p x = (l i).formPerm x)
    (i₀ : β) (a b : α) (L R : List α)
    (he : l i₀ = (a :: L) ++ (b :: R)) :
    Nat.card (Orbits (swap a b * p)) = Nat.card (Orbits p) + 1 := by
  classical
  have hn₀ : ((a :: L) ++ (b :: R)).Nodup := he ▸ hn i₀
  have hn₁ := (List.nodup_append.mp hn₀).1
  have hn₂ := (List.nodup_append.mp hn₀).2.1
  have hd : List.Disjoint (a :: L) (b :: R) :=
    List.disjoint_iff_ne.mpr (List.nodup_append.mp hn₀).2.2
  have ha : a ∈ l i₀ := by simp [he]
  have hb : b ∈ l i₀ := by simp [he]
  let ll := splitFamily l i₀ (a :: L) (b :: R)
  have hnn (i) : (ll i).Nodup := by
    cases i with
    | inl i => exact hn i
    | inr c => cases c <;> assumption
  have hnee (i) : ∃ x, x ∈ ll i := by
    cases i with
    | inl i => exact hne i
    | inr c => cases c
               · exact ⟨a, List.mem_cons_self⟩
               · exact ⟨b, List.mem_cons_self⟩
  have hcc := splitFamily_partition l hn hc i₀ (a :: L) (b :: R) he
  have hpp (i) (x : α) (hx : x ∈ ll i) :
      (swap a b * p) x = (ll i).formPerm x := by
    cases i with
    | inl i =>
      have hpx : p x ∈ l i := by rw [hp i x hx]; exact List.formPerm_apply_mem_of_mem hx
      have hpa : p x ≠ a := fun h => i.property ((hc a).unique (h ▸ hpx) ha)
      have hpb : p x ≠ b := fun h => i.property ((hc b).unique (h ▸ hpx) hb)
      rw [mul_apply,swap_apply_of_ne_of_ne hpa hpb]
      exact hp i x hx
    | inr c =>
      have hcut := congrArg (fun u : Perm α => u x) (swap_mul_formPerm_cut a b L R hn₀)
      cases c
      · have hpx : p x = ((a :: L) ++ (b :: R)).formPerm x := by
          rw [← he]; exact hp i₀ x (by rw [he]; exact List.mem_append_left _ hx)
        have hxr : x ∉ b :: R := fun h => List.disjoint_left.mp hd hx h
        simpa only [ll,splitFamily,List.cons_append,mul_apply,hpx,List.formPerm_apply_of_notMem hxr] using hcut
      · have hpx : p x = ((a :: L) ++ (b :: R)).formPerm x := by
          rw [← he]; exact hp i₀ x (by rw [he]; exact List.mem_append_right _ hx)
        have hxl : (b :: R).formPerm x ∉ a :: L := fun h =>
          List.disjoint_left.mp hd h (List.formPerm_apply_mem_of_mem hx)
        simpa only [ll,splitFamily,List.cons_append,mul_apply,hpx,List.formPerm_apply_of_notMem hxl] using hcut
  rw [card_orbits_eq_of_lists (swap a b * p) ll hnn hnee hcc hpp,
    card_orbits_eq_of_lists p l hn hne hc hp]
  let : Fintype β := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_bool]
  have hh' : Fintype.card {i : β // i ≠ i₀} = Fintype.card β - 1 := by simp
  rw [hh']
  have hpos : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨i₀⟩
  omega

lemma orbitList_eq_cons [Fintype α] (p : Perm α) (a : α) :
    ∃ L, orbitList p a = a :: L := by
  classical
  by_cases ha : p a = a
  · exact ⟨[], by simp [orbitList,ha]⟩
  have hs : a ∈ p.support := mem_support.mpr ha
  have h := p.toList_getElem_zero a hs
  cases hl : p.toList a with
  | nil => exact ((toList_eq_nil_iff.mp hl) hs).elim
  | cons c L =>
    simp only [hl,List.getElem_cons_zero] at h
    subst c
    exact ⟨L,by simp [orbitList,ha,hl]⟩

/-- Swapping two distinct members of one orbit cuts that orbit into two.
In particular one-element vertex/face cycles are not lost in the count. -/
theorem card_orbits_swap_of_sameCycle [Fintype α] (p : Perm α) {a b : α}
    (hab : a ≠ b) (hs : p.SameCycle a b) :
    Nat.card (Orbits (swap a b * p)) = Nat.card (Orbits p) + 1 := by
  classical
  let q₀ : Orbits p := Quotient.mk _ a
  let r : Orbits p → α := fun q => if q = q₀ then a else q.out
  have hr (q : Orbits p) : Quotient.mk _ (r q) = q := by
    dsimp [r]
    split_ifs with h
    · exact h.symm
    · exact Quotient.out_eq q
  let l : Orbits p → List α := fun q => orbitList p (r q)
  have hmem (x : α) (q : Orbits p) : x ∈ l q ↔ Quotient.mk _ x = q := by
    change x ∈ orbitList p (r q) ↔ _
    rw [mem_orbitList]
    calc
      p.SameCycle (r q) x ↔ Quotient.mk _ x = (Quotient.mk _ (r q) : Orbits p) :=
        ⟨fun h => Quotient.sound h.symm,fun h => (Quotient.exact h).symm⟩
      _ ↔ _ := by rw [hr q]
  have hc (x : α) : ∃! q, x ∈ l q := by
    refine ⟨Quotient.mk _ x,(hmem x _).mpr rfl,?_⟩
    exact fun q h => ((hmem x q).mp h).symm
  have hne (q : Orbits p) : ∃ x, x ∈ l q := ⟨r q,(hmem _ _).mpr (hr q)⟩
  obtain ⟨K,hK⟩ := orbitList_eq_cons p a
  have hb : b ∈ K := by
    have hh := (mem_orbitList p a b).mpr hs
    rw [hK,List.mem_cons] at hh
    exact hh.resolve_left (Ne.symm hab)
  obtain ⟨L,R,hR⟩ := List.append_of_mem hb
  apply card_orbits_cut p l (fun q => nodup_orbitList p (r q)) hne hc
    (fun q x hx => orbitList_action p (r q) x hx) q₀ a b L R
  simp only [l,r,ite_true,hK,hR,List.cons_append]

lemma sameCycle_swap_of_not_sameCycle [Fintype α] (p : Perm α) {a b : α}
    (hs : ¬ p.SameCycle a b) : (swap a b * p).SameCycle a b := by
  classical
  obtain ⟨L,hL⟩ := orbitList_eq_cons p a
  obtain ⟨R,hR⟩ := orbitList_eq_cons p b
  have hnL : (a :: L).Nodup := hL ▸ nodup_orbitList p a
  have hnR : (b :: R).Nodup := hR ▸ nodup_orbitList p b
  have hd : List.Disjoint (a :: L) (b :: R) := by
    apply List.disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_orbitList p a x).mp (hL ▸ hx)
    have hy' := (mem_orbitList p b x).mp (hR ▸ hy)
    exact hs (hx'.trans hy'.symm)
  have hn : ((a :: L) ++ (b :: R)).Nodup := by
    exact List.nodup_append.mpr ⟨hnL,hnR,List.disjoint_iff_ne.mp hd⟩
  apply sameCycle_of_list (swap a b * p) hn ?_ (by simp) (by simp)
  intro x hx
  have he := congrArg (fun u : Perm α => u x) (formPerm_cut a b L R hn)
  simp only [mul_apply,List.cons_append] at he ⊢
  rw [he]
  congr 1
  rcases List.mem_append.mp hx with hx | hx
  · have hxr : x ∉ b :: R := fun hh => List.disjoint_left.mp hd hx hh
    rw [List.formPerm_apply_of_notMem hxr]
    simpa only [hL] using orbitList_action p a x (hL ▸ hx)
  · have hxl : (b :: R).formPerm x ∉ a :: L := fun hh =>
      List.disjoint_left.mp hd hh (List.formPerm_apply_mem_of_mem hx)
    rw [List.formPerm_apply_of_notMem hxl]
    simpa only [hR] using orbitList_action p b x (hR ▸ hx)

/-- Swapping members of distinct orbits joins precisely those two orbits. -/
theorem card_orbits_swap_of_not_sameCycle [Fintype α] (p : Perm α) {a b : α}
    (hs : ¬ p.SameCycle a b) :
    Nat.card (Orbits (swap a b * p)) + 1 = Nat.card (Orbits p) := by
  have hab : a ≠ b := fun h => hs (h.sameCycle p)
  have h := card_orbits_swap_of_sameCycle (swap a b * p) hab
    (sameCycle_swap_of_not_sameCycle p hs)
  simpa only [← mul_assoc,swap_mul_self,one_mul] using h.symm

/-- Each edge transposition changes Euler's orbit count by exactly one. -/
theorem card_orbits_swap_le [Fintype α] (p : Perm α) (a b : α) :
    Nat.card (Orbits (swap a b * p)) ≤ Nat.card (Orbits p) + 1 := by
  classical
  by_cases hab : a = b
  · subst b
    have he : swap a a * p = p := by ext x; simp
    rw [he]
    omega
  by_cases h : p.SameCycle a b
  · exact (card_orbits_swap_of_sameCycle p hab h).le
  · have hh := card_orbits_swap_of_not_sameCycle p h
    omega

end FKCRT.MapCycles
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
lemma sameCycle_mono {p q : Perm α}
    (h : ∀ x,q.SameCycle x (p x)) {x y : α} (hxy : p.SameCycle x y) : q.SameCycle x y := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simpa using SameCycle.refl q x
  | succ n ih =>
    rw [pow_succ',mul_apply]
    exact ih.trans (h _)

/-- Swapping the outputs at two distinct rotation cycles preserves every
old vertex incidence and merges the indicated two vertices. -/
lemma sameCycle_le_vertexJoin (p : Perm α) {a b : α} (h : ¬p.SameCycle a b)
    {x y : α} (hxy : p.SameCycle x y) : (swap a b*p).SameCycle x y := by
  let q := swap a b*p
  have hab : q.SameCycle a b := sameCycle_swap_of_not_sameCycle p h
  apply sameCycle_mono (p := p) (q := q) ?_ hxy
  intro d
  have hd : q.SameCycle d (q d) := sameCycle_apply_right.mpr (SameCycle.refl q d)
  by_cases ha : p d=a
  · have he : q d=b := by simp [q,mul_apply,ha]
    rw [ha]
    exact (he ▸ hd).trans hab.symm
  · by_cases hb : p d=b
    · have he : q d=a := by simp [q,mul_apply,hb]
      rw [hb]
      exact (he ▸ hd).trans hab
    · simpa [q,mul_apply,swap_apply_of_ne_of_ne ha hb] using hd

def JoinRel (p : Perm α) (a b x y : α) : Prop :=
  p.SameCycle x y ∨
    ((p.SameCycle x a ∨ p.SameCycle x b) ∧ (p.SameCycle y a ∨ p.SameCycle y b))

omit [DecidableEq α] [Fintype α] in
lemma JoinRel.refl (p : Perm α) (a b x : α) : JoinRel p a b x x :=
  Or.inl (SameCycle.refl p x)

omit [DecidableEq α] [Fintype α] in
lemma JoinRel.symm {p : Perm α} {a b x y : α} (h : JoinRel p a b x y) : JoinRel p a b y x := by
  rcases h with h|⟨hx,hy⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hy,hx⟩

omit [DecidableEq α] [Fintype α] in
lemma JoinRel.trans {p : Perm α} {a b x y z : α}
    (h : JoinRel p a b x y) (h' : JoinRel p a b y z) : JoinRel p a b x z := by
  rcases h with h|⟨hx,hy⟩
  · rcases h' with h'|⟨hy,hz⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr ⟨hy.imp (h.trans) (h.trans),hz⟩
  · rcases h' with h'|⟨_,hz⟩
    · exact Or.inr ⟨hx,hy.imp (h'.symm.trans) (h'.symm.trans)⟩
    · exact Or.inr ⟨hx,hz⟩

omit [Fintype α] in
lemma JoinRel.step (p : Perm α) (a b x : α) : JoinRel p a b x ((swap a b*p) x) := by
  have hx : p.SameCycle x (p x) := sameCycle_apply_right.mpr (SameCycle.refl p x)
  by_cases ha : p x=a
  · rw [mul_apply,ha,swap_apply_left]
    exact Or.inr ⟨Or.inl (ha ▸ hx),Or.inr (SameCycle.refl p b)⟩
  · by_cases hb : p x=b
    · rw [mul_apply,hb,swap_apply_right]
      exact Or.inr ⟨Or.inr (hb ▸ hx),Or.inl (SameCycle.refl p a)⟩
    · rw [mul_apply,swap_apply_of_ne_of_ne ha hb]
      exact Or.inl hx

/-- Exact vertex equivalence after one-vertex gluing. In particular no
additional vertices are identified, including fixed points and loop blocks. -/
theorem sameCycle_vertexJoin_iff (p : Perm α) {a b : α} (h : ¬p.SameCycle a b) (x y : α) :
    (swap a b*p).SameCycle x y ↔ JoinRel p a b x y := by
  constructor
  · intro hxy
    obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
    clear hxy
    induction n with
    | zero => simpa using JoinRel.refl p a b x
    | succ n ih =>
      rw [pow_succ',mul_apply]
      exact ih.trans (JoinRel.step p a b _)
  · rintro (hxy|⟨hx,hy⟩)
    · exact sameCycle_le_vertexJoin p h hxy
    · have hab := sameCycle_swap_of_not_sameCycle p h
      rcases hx with hx|hx <;> rcases hy with hy|hy
      · exact (sameCycle_le_vertexJoin p h hx).trans (sameCycle_le_vertexJoin p h hy).symm
      · exact (sameCycle_le_vertexJoin p h hx).trans (hab.trans (sameCycle_le_vertexJoin p h hy).symm)
      · exact (sameCycle_le_vertexJoin p h hx).trans (hab.symm.trans (sameCycle_le_vertexJoin p h hy).symm)
      · exact (sameCycle_le_vertexJoin p h hx).trans (sameCycle_le_vertexJoin p h hy).symm

end FKCRT.MapCycles
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
lemma sameCycle_partition {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {x y : α} (hxy : p.SameCycle x y) : x∈S ↔ y∈S := by
  obtain ⟨n,rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ',mul_apply,hp] using ih

omit [DecidableEq α] in
lemma not_sameCycle_partition {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b : α} (ha : a∈S) (hb : b∉S) : ¬p.SameCycle a b :=
  fun h => hb ((sameCycle_partition hp h).mp ha)

/-- The inclusion of either block's vertices remains injective under the
actual vertex-rotation cut/join. -/
theorem vertexJoin_inside_iff {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b x y : α} (ha : a∈S) (hb : b∉S)
    (hx : x∈S) (hy : y∈S) : (swap a b*p).SameCycle x y ↔ p.SameCycle x y := by
  rw [sameCycle_vertexJoin_iff p (not_sameCycle_partition hp ha hb)]
  constructor
  · rintro (h|⟨hxa|hxb,hya|hyb⟩)
    · exact h
    · exact hxa.trans hya.symm
    · exact False.elim (hb ((sameCycle_partition hp hyb).mp hy))
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
  · exact Or.inl

theorem vertexJoin_outside_iff {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b x y : α} (ha : a∈S) (hb : b∉S)
    (hx : x∉S) (hy : y∉S) : (swap a b*p).SameCycle x y ↔ p.SameCycle x y := by
  have hh := vertexJoin_inside_iff (S := Sᶜ) (p := p)
    (fun d => not_congr (hp d)) hb (by simpa using ha) hx hy
  simpa only [swap_comm b a] using hh

/-- A vertex in one block coincides with a vertex in the other block if
and only if both are their respective attachment poles. -/
theorem vertexJoin_cross_iff {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) {a b x y : α} (ha : a∈S) (hb : b∉S)
    (hx : x∈S) (hy : y∉S) : (swap a b*p).SameCycle x y ↔ p.SameCycle x a ∧ p.SameCycle y b := by
  rw [sameCycle_vertexJoin_iff p (not_sameCycle_partition hp ha hb)]
  constructor
  · rintro (h|⟨hxa|hxb,hya|hyb⟩)
    · exact False.elim (hy ((sameCycle_partition hp h).mp hx))
    · exact False.elim (hy ((sameCycle_partition hp hya).mpr ha))
    · exact ⟨hxa,hyb⟩
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
    · exact False.elim (hb ((sameCycle_partition hp hxb).mp hx))
  · rintro ⟨hxa,hyb⟩
    exact Or.inr ⟨Or.inl hxa,Or.inr hyb⟩

omit [Fintype α] in
lemma formPerm_other_mem_iff {l r : List α} (hd : l.Disjoint r) (x : α) :
    r.formPerm x∈l ↔ x∈l := by
  by_cases hx : x∈l
  · have hxr : x∉r := fun h => List.disjoint_left.mp hd hx h
    simp only [List.formPerm_apply_of_notMem hxr]
  · constructor
    · intro h
      have hxr : r.formPerm x∉r := fun hr => List.disjoint_left.mp hd h hr
      have he : r.formPerm x=x := List.formPerm_apply_of_notMem
        (fun hr => hxr (r.formPerm_apply_mem_of_mem hr))
      exact he ▸ h
    · exact False.elim ∘ hx

/-- The literal combined contour rotation is a one-vertex join of the
separate rotations. The flip permutation can be the actual first-colour
matching; only its proved locality is required. -/
theorem contour_vertex_join (a b : α) (L R : List α)
    (hn : (a::(L++b::R)).Nodup) (e : Perm α)
    (he : ∀ x,e x∈a::L ↔ x∈a::L) :
    let p := (a::L).formPerm*(b::R).formPerm*e
    ((a::(L++b::R)).formPerm*e=swap a b*p) ∧
    (∀ x y,x∈a::L → y∈a::L →
      (((a::(L++b::R)).formPerm*e).SameCycle x y ↔ p.SameCycle x y)) ∧
    (∀ x y,x∈a::L → y∉a::L →
      (((a::(L++b::R)).formPerm*e).SameCycle x y ↔ p.SameCycle x a ∧ p.SameCycle y b)) := by
  dsimp only
  have hd : (a::L).Disjoint (b::R) := by
    have hn' : ((a::L)++(b::R)).Nodup := by simpa only [List.cons_append] using hn
    exact List.disjoint_iff_ne.mpr (List.nodup_append.mp hn').2.2
  have hp : ∀ x,((a::L).formPerm*(b::R).formPerm*e) x∈a::L ↔ x∈a::L := by
    intro x
    simp only [mul_apply,List.formPerm_mem_iff_mem,formPerm_other_mem_iff hd,he]
  have hb : b∉a::L := fun h => List.disjoint_left.mp hd h (by simp)
  have hj : (a::(L++b::R)).formPerm*e=swap a b*((a::L).formPerm*(b::R).formPerm*e) := by
    rw [formPerm_cut a b L R hn]
    simp only [mul_assoc]
  refine ⟨hj,?_,?_⟩
  · intro x y hx hy
    rw [hj]
    exact vertexJoin_inside_iff (S := {x | x∈a::L}) hp (by simp) hb hx hy
  · intro x y hx hy
    rw [hj]
    exact vertexJoin_cross_iff (S := {x | x∈a::L}) hp (by simp) hb hx hy

end FKCRT.MapCycles
end

end OAI
