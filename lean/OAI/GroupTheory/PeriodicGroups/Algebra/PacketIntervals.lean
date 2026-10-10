import Mathlib
import OAI.GroupTheory.PeriodicGroups.Algebra.WordAlgebra

namespace OAI

section
universe u v w
namespace SourceBurnside.PacketIntervals
variable {Γ : Type*}

def total (len : Γ → ℕ) (s : List Γ) : ℕ := (s.map len).sum

@[simp] lemma total_nil (len : Γ → ℕ) : total len [] = 0 := rfl
@[simp] lemma total_cons (len : Γ → ℕ) (c : Γ) (s : List Γ) :
    total len (c::s) = len c + total len s := rfl
@[simp] lemma total_append (len : Γ → ℕ) (s t : List Γ) :
    total len (s ++ t) = total len s + total len t := by simp [total]

lemma total_perm (len : Γ → ℕ) {s t : List Γ} (h : s.Perm t) :
    total len s = total len t := (h.map len).sum_eq

def floorSplit (len : Γ → ℕ) : List Γ → ℕ → List Γ × List Γ
  | [], _ => ([],[])
  | c::s, N => if len c ≤ N then
      let p := floorSplit len s (N-len c)
      (c::p.1,p.2)
    else ([],c::s)

def ceilSplit (len : Γ → ℕ) : List Γ → ℕ → List Γ × List Γ
  | [], _ => ([],[])
  | c::s, N => if N=0 then ([],c::s) else if N ≤ len c then ([c],s) else
      let p := ceilSplit len s (N-len c)
      (c::p.1,p.2)

lemma floorSplit_join (len : Γ → ℕ) (s : List Γ) (N : ℕ) :
    (floorSplit len s N).1 ++ (floorSplit len s N).2 = s := by
  induction s generalizing N with
  | nil => rfl
  | cons c s ih =>
    simp only [floorSplit]
    split
    · simpa using congrArg (List.cons c) (ih (N-len c))
    · rfl

lemma ceilSplit_join (len : Γ → ℕ) (s : List Γ) (N : ℕ) :
    (ceilSplit len s N).1 ++ (ceilSplit len s N).2 = s := by
  induction s generalizing N with
  | nil => rfl
  | cons c s ih =>
    simp only [ceilSplit]
    split
    · rfl
    · split
      · rfl
      · simpa using congrArg (List.cons c) (ih (N-len c))

lemma floorSplit_bound (len : Γ → ℕ) (s : List Γ) (N : ℕ) :
    total len (floorSplit len s N).1 ≤ N := by
  induction s generalizing N with
  | nil => simp [floorSplit]
  | cons c s ih =>
    simp only [floorSplit]
    split
    · simp only [total_cons]
      have := ih (N-len c)
      omega
    · simp

lemma floorSplit_next (len : Γ → ℕ) (s : List Γ) (N : ℕ) (c : Γ) (t : List Γ)
    (h : (floorSplit len s N).2 = c::t) :
    N < total len (floorSplit len s N).1 + len c := by
  induction s generalizing N with
  | nil => simp [floorSplit] at h
  | cons a s ih =>
    simp only [floorSplit] at *
    by_cases ha : len a ≤ N
    · simp only [ite_eq_left ha, total_cons] at h ⊢
      have := ih (N-len a) h
      omega
    · simp only [ite_eq_right ha, total_nil, zero_add] at h ⊢
      cases h
      omega

lemma floorSplit_prefix (len : Γ → ℕ) (p s : List Γ) (N : ℕ)
    (hp : total len p ≤ N)
    (hs : ∀ c t, s = c::t → N < total len p + len c) :
    floorSplit len (p++s) N = (p,s) := by
  induction p generalizing N with
  | nil =>
    cases s with
    | nil => rfl
    | cons c t =>
      have hc := hs c t rfl
      simp [floorSplit, Nat.not_le.mpr (by simpa using hc)]
  | cons c p ih =>
    have hc : len c ≤ N := by simpa using le_trans (Nat.le_add_right (len c) (total len p)) hp
    simp only [List.cons_append, floorSplit, ite_eq_left hc]
    rw [ih (N-len c) (by simp only [total_cons] at hp; omega) (by
      intro a t ht
      have := hs a t ht
      simp only [total_cons] at this
      omega)]

lemma ceilSplit_zero (len : Γ → ℕ) (s : List Γ) : ceilSplit len s 0 = ([],s) := by
  cases s <;> simp [ceilSplit]

lemma ceilSplit_reaches (len : Γ → ℕ) (s : List Γ) (N : ℕ) (hN : N ≤ total len s) :
    N ≤ total len (ceilSplit len s N).1 := by
  induction s generalizing N with
  | nil => simpa [ceilSplit] using hN
  | cons c s ih =>
    simp only [ceilSplit]
    split
    · simp_all
    · split
      · simpa
      · simp only [total_cons]
        have := ih (N-len c) (by simp only [total_cons] at hN; omega)
        omega

lemma ceilSplit_before (len : Γ → ℕ) (s : List Γ) (N : ℕ) (hN : 0 < N)
    (hfit : N ≤ total len s) :
    total len (ceilSplit len s N).1.dropLast < N := by
  induction s generalizing N with
  | nil => simp at hfit; omega
  | cons c s ih =>
    simp only [ceilSplit, ite_eq_right (Nat.ne_of_gt hN)]
    split
    · simpa
    · have hsmall : len c < N := by omega
      have hfit' : N-len c ≤ total len s := by simp only [total_cons] at hfit; omega
      have hr := ceilSplit_reaches len s (N-len c) hfit'
      have he : (ceilSplit len s (N-len c)).1 ≠ [] := by
        intro he
        simp only [he, total_nil] at hr
        omega
      have hb := ih (N-len c) (by omega) hfit'
      rw [List.dropLast_cons_of_ne_nil he, total_cons]
      omega

lemma ceilSplit_prefix (len : Γ → ℕ) (p s : List Γ) (N : ℕ)
    (hp : N ≤ total len p)
    (hprev : (p=[] ∧ N=0) ∨ (p≠[] ∧ total len p.dropLast < N)) :
    ceilSplit len (p++s) N = (p,s) := by
  induction p generalizing N with
  | nil =>
    have : N=0 := by simpa using hp
    subst N
    exact ceilSplit_zero len s
  | cons c p ih =>
    have hN : 0 < N := by
      rcases hprev with h|h
      · simp at h
      · omega
    simp only [List.cons_append, ceilSplit, ite_eq_right (Nat.ne_of_gt hN)]
    cases p with
    | nil =>
      have hc : N ≤ len c := by simpa using hp
      simp [hc]
    | cons a t =>
      have hprev' : total len (a::t).dropLast + len c < N := by
        rcases hprev with h|h
        · simp at h
        · simpa [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), Nat.add_comm] using h.2
      have hc : ¬ N ≤ len c := by omega
      rw [ite_eq_right hc, ih (N-len c) (by change N ≤ len c + total len (a::t) at hp; omega)
        (Or.inr ⟨List.cons_ne_nil _ _, by omega⟩)]

lemma ceilSplit_empty_or_before (len : Γ → ℕ) (s : List Γ) (N : ℕ)
    (hfit : N ≤ total len s) :
    ((ceilSplit len s N).1 = [] ∧ N = 0) ∨
    ((ceilSplit len s N).1 ≠ [] ∧ total len (ceilSplit len s N).1.dropLast < N) := by
  by_cases hN : N=0
  · simp [hN, ceilSplit_zero]
  · right
    have hr := ceilSplit_reaches len s N hfit
    have hb := ceilSplit_before len s N (by omega) hfit
    refine ⟨?_, hb⟩
    intro he
    simp [he] at hr
    omega

lemma ceilSplit_overshoot (len : Γ → ℕ) (s : List Γ) (N b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) :
    total len (ceilSplit len s N).1 ≤ N+b := by
  induction s generalizing N with
  | nil => simp [ceilSplit]
  | cons c s ih =>
    have hc := hb c (by simp)
    have hs : ∀ a ∈ s, len a ≤ b := fun a ha => hb a (by simp [ha])
    simp only [ceilSplit]
    split
    · simp
    · split
      · simpa using le_trans hc (Nat.le_add_left b N)
      · simp only [total_cons]
        have := ih (N-len c) hs
        omega

lemma floorSplit_defect (len : Γ → ℕ) (s : List Γ) (N b : ℕ)
    (hfit : N ≤ total len s) (hb : ∀ c ∈ s, len c ≤ b) :
    N ≤ total len (floorSplit len s N).1 + b := by
  have hj := floorSplit_join len s N
  cases hr : (floorSplit len s N).2 with
  | nil =>
    rw [hr, List.append_nil] at hj
    rw [hj]
    omega
  | cons c t =>
    have hn := floorSplit_next len s N c t hr
    have hc : c ∈ s := by rw [← hj, hr]; simp
    have := hb c hc
    omega

structure Selection (Γ : Type*) where
  before : List Γ
  inside : List Γ
  after : List Γ
  deriving DecidableEq

def Selection.join (p : Selection Γ) : List Γ := p.before ++ p.inside ++ p.after

def select (len : Γ → ℕ) (s : List Γ) (a e : ℕ) : Selection Γ :=
  let p := ceilSplit len s a
  let q := floorSplit len p.2 (e-total len p.1)
  ⟨p.1,q.1,q.2⟩

lemma select_join (len : Γ → ℕ) (s : List Γ) (a e : ℕ) :
    (select len s a e).join = s := by
  simp only [select, Selection.join, List.append_assoc, floorSplit_join, ceilSplit_join]

lemma select_total (len : Γ → ℕ) (s : List Γ) (a e : ℕ) :
    total len (select len s a e).before + total len (select len s a e).inside +
      total len (select len s a e).after = total len s := by
  simpa [Selection.join, Nat.add_assoc] using congrArg (total len) (select_join len s a e)

lemma select_before_bound (len : Γ → ℕ) (s : List Γ) (a e b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) :
    total len (select len s a e).before ≤ a+b :=
  ceilSplit_overshoot len s a b hb

lemma select_inside_bound (len : Γ → ℕ) (s : List Γ) (a e b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) (ha : a+b ≤ e) (he : e ≤ total len s) :
    e-a ≤ total len (select len s a e).inside + 2*b := by
  have hc := ceilSplit_overshoot len s a b hb
  have hj := ceilSplit_join len s a
  have ht : total len s = total len (ceilSplit len s a).1 +
      total len (ceilSplit len s a).2 := by
    simpa only [total_append] using congrArg (total len) hj.symm
  have hfit : e-total len (ceilSplit len s a).1 ≤ total len (ceilSplit len s a).2 := by omega
  have hb' : ∀ c ∈ (ceilSplit len s a).2, len c ≤ b := by
    intro c hm
    apply hb
    rw [← hj]
    exact List.mem_append_right _ hm
  have hf := floorSplit_defect len (ceilSplit len s a).2
    (e-total len (ceilSplit len s a).1) b hfit hb'
  change e-a ≤ total len (floorSplit len (ceilSplit len s a).2
    (e-total len (ceilSplit len s a).1)).1 + 2*b
  omega

lemma select_permute (len : Γ → ℕ) (s : List Γ) (a e : ℕ)
    (hfit : a ≤ total len s) (t : List Γ)
    (ht : t.Perm (select len s a e).inside) :
    select len ((select len s a e).before ++ t ++ (select len s a e).after) a e =
      ⟨(select len s a e).before,t,(select len s a e).after⟩ := by
  let p := ceilSplit len s a
  let q := floorSplit len p.2 (e-total len p.1)
  have hp := ceilSplit_prefix len p.1 (t++q.2) a
    (ceilSplit_reaches len s a hfit) (ceilSplit_empty_or_before len s a hfit)
  have hq := floorSplit_prefix len t q.2 (e-total len p.1)
    (by rw [total_perm len ht]; exact floorSplit_bound len p.2 _)
    (by
      intro c r hr
      rw [total_perm len ht]
      exact floorSplit_next len p.2 _ c r hr)
  change select len (p.1 ++ t ++ q.2) a e = ⟨p.1,t,q.2⟩
  simp only [select, List.append_assoc, hp, hq]

lemma total_le_length_mul (len : Γ → ℕ) (s : List Γ) (b : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) : total len s ≤ s.length*b := by
  induction s with
  | nil => simp
  | cons c s ih =>
    have hc := hb c (by simp)
    have hs := ih (fun a ha => hb a (by simp [ha]))
    simp only [total_cons, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem select_long (len : Γ → ℕ) (s : List Γ) (a e b d : ℕ)
    (hb : ∀ c ∈ s, len c ≤ b) (he : e ≤ total len s)
    (hlong : b*(d^2+3) < e-a) :
    d^2 < (select len s a e).inside.length := by
  have ha : a+b ≤ e := by
    have hmul : b ≤ b*(d^2+3) := by nlinarith
    omega
  have hr := select_inside_bound len s a e b hb ha he
  have hm : ∀ c ∈ (select len s a e).inside, len c ≤ b := by
    intro c hc
    apply hb
    rw [← select_join len s a e, Selection.join]
    simp [hc]
  have ht := total_le_length_mul len (select len s a e).inside b hm
  by_contra hn
  have hle : (select len s a e).inside.length ≤ d^2 := by omega
  have hmul := Nat.mul_le_mul_right b hle
  nlinarith

end SourceBurnside.PacketIntervals

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T A : Type*}

def spell (label : Γ → List α) (s : List Γ) : List α := s.flatMap label

@[simp] lemma spell_append (label : Γ → List α) (s t : List Γ) :
    spell label (s++t) = spell label s ++ spell label t := by simp [spell]

lemma length_spell (label : Γ → List α) (s : List Γ) :
    (spell label s).length = PacketIntervals.total (fun c => (label c).length) s := by
  induction s with
  | nil => rfl
  | cons c s ih => simpa [spell] using congrArg (fun x => (label c).length + x) ih

lemma spell_perm (label : Γ → List α) {s t : List Γ} (h : s.Perm t) :
    (spell label s).Perm (spell label t) := h.flatMap (fun _ _ => List.Perm.refl _)

lemma nodup_of_spell_nodup (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (s : List Γ) (h : (spell label s).Nodup) : s.Nodup := by
  apply (List.nodup_flatMap.mp h).2.imp
  intro a b hab he
  subst b
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (label a) (hne a)
  exact List.disjoint_left.mp hab hx hx

lemma interval_sublist (p s q : List α) (a e : ℕ) (ha : a ≤ p.length)
    (he : p.length+s.length ≤ e) :
    s.Sublist (((p++s++q).drop a).take (e-a)) := by
  have ha' : a ≤ (p++s).length := by simp; omega
  rw [List.drop_append_of_le_length ha', List.drop_append_of_le_length ha]
  rw [List.take_append]
  have hk : ((p.drop a)++s).length ≤ e-a := by
    simp only [List.length_append, List.length_drop]
    omega
  rw [(List.take_eq_self_iff _).mpr hk]
  exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)

lemma select_spelling_sublist (label : Γ → List α) (s : List Γ) (a e : ℕ)
    (ha : a ≤ (spell label s).length)
    (hae : PacketIntervals.total (fun c => (label c).length)
      (PacketIntervals.select (fun c => (label c).length) s a e).before ≤ e) :
    (spell label (PacketIntervals.select (fun c => (label c).length) s a e).inside).Sublist
      (((spell label s).drop a).take (e-a)) := by
  let len := fun c => (label c).length
  let p := PacketIntervals.select len s a e
  have hj : spell label s = spell label p.before ++ spell label p.inside ++ spell label p.after := by
    rw [← PacketIntervals.select_join len s a e]
    simp only [PacketIntervals.Selection.join, spell_append]
    rfl
  rw [hj]
  have hlo : a ≤ (spell label p.before).length := by
    rw [length_spell]
    exact PacketIntervals.ceilSplit_reaches len s a (by simpa [length_spell] using ha)
  have hhi : (spell label p.before).length+(spell label p.inside).length ≤ e := by
    rw [length_spell, length_spell]
    have hf := PacketIntervals.floorSplit_bound len (PacketIntervals.ceilSplit len s a).2
      (e-PacketIntervals.total len (PacketIntervals.ceilSplit len s a).1)
    change PacketIntervals.total len p.inside ≤ e-PacketIntervals.total len p.before at hf
    change PacketIntervals.total len p.before ≤ e at hae
    dsimp [len] at hf hae
    omega
  exact interval_sublist _ _ _ a e hlo hhi

lemma erased_eq_of_perm_uniform (erase : α → T) (t : T) {s r : List α}
    (h : s.Perm r) (hu : ∀ x ∈ s, erase x = t) : s.map erase = r.map erase := by
  have hs : s.map erase = List.replicate s.length t := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, by simpa using hu⟩
  have hr : r.map erase = List.replicate r.length t := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, by simpa using (fun x hx => hu x (h.mem_iff.mpr hx))⟩
  rw [hs,hr,h.length_eq]

variable [Monoid A]

def eval (f : α → A) (s : List α) : A := (s.map f).prod

@[simp] lemma eval_append (f : α → A) (s t : List α) :
    eval f (s++t) = eval f s * eval f t := by simp [eval]

lemma eval_perm_uniform (f : α → A) (erase : α → T) (t : T)
    (hc : ∀ x y, erase x = t → erase y = t → Commute (f x) (f y))
    {s r : List α} (h : s.Perm r) (hu : ∀ x ∈ s, erase x = t) : eval f s = eval f r := by
  apply (h.map f).prod_eq'
  rw [List.pairwise_map]
  exact List.pairwise_of_forall_mem_list (fun x hx y hy => hc x y (hu x hx) (hu y hy))

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T : Type*}

def pickPacket (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (s : List Γ) : Cancellation.Packet Γ :=
  let a := (range ((spell label s).map erase)).1
  let e := (range ((spell label s).map erase)).2
  let p := PacketIntervals.select (fun c => (label c).length) s a e
  ⟨p.before,p.inside,p.after⟩

lemma pickPacket_join (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (s : List Γ) : (pickPacket label erase range s).join = s :=
  PacketIntervals.select_join _ _ _ _

lemma reordered_perm (p : Cancellation.Packet Γ) (s : List Γ) (hj : p.join = s)
    (σ : Equiv.Perm (Fin p.inside.length)) : (p.reorder σ).Perm s := by
  rw [← hj]
  have h : (List.ofFn (p.inside.get ∘ σ)).Perm p.inside := by
    simpa using σ.ofFn_comp_perm p.inside.get
  exact (h.append_left p.before).append_right p.after

lemma pickPacket_stable (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (s : List Γ) (ha : (range ((spell label s).map erase)).1 ≤ (spell label s).length)
    (t : T) (hu : ∀ x ∈ spell label (pickPacket label erase range s).inside, erase x = t)
    (σ : Equiv.Perm (Fin (pickPacket label erase range s).inside.length)) :
    (pickPacket label erase range ((pickPacket label erase range s).reorder σ)).key =
      (pickPacket label erase range s).key := by
  let p := pickPacket label erase range s
  let seq := List.ofFn (p.inside.get ∘ σ)
  have hseq : seq.Perm p.inside := by simpa [seq] using σ.ofFn_comp_perm p.inside.get
  have he : (spell label (p.reorder σ)).map erase = (spell label s).map erase := by
    rw [← pickPacket_join label erase range s]
    simp only [Cancellation.Packet.join, Cancellation.Packet.reorder, spell_append, List.map_append]
    rw [erased_eq_of_perm_uniform erase t (spell_perm label hseq).symm hu]
  have hs := PacketIntervals.select_permute (fun c => (label c).length) s
    (range ((spell label s).map erase)).1 (range ((spell label s).map erase)).2
    (by simpa only [length_spell] using ha) seq hseq
  change (pickPacket label erase range (p.reorder σ)).key = p.key
  unfold pickPacket
  rw [he]
  change (let q := PacketIntervals.select (fun c => (label c).length)
              (p.before++seq++p.after) (range ((spell label s).map erase)).1
              (range ((spell label s).map erase)).2;
          Cancellation.Packet.key ⟨q.before,q.inside,q.after⟩) = p.key
  change PacketIntervals.select (fun c => (label c).length) (p.before++seq++p.after)
    (range ((spell label s).map erase)).1 (range ((spell label s).map erase)).2 =
      ⟨p.before,seq,p.after⟩ at hs
  dsimp only
  rw [hs]
  simp only [Cancellation.Packet.key]
  exact congrArg (fun x : Multiset Γ => (p.before,p.after,x)) (Quotient.sound hseq)

variable {A : Type*} [Monoid A]

lemma pickPacket_same_value (label : Γ → List α) (erase : α → T) (range : List T → ℕ × ℕ)
    (f : α → A) (s : List Γ) (t : T)
    (hu : ∀ x ∈ spell label (pickPacket label erase range s).inside, erase x = t)
    (hc : ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (σ : Equiv.Perm (Fin (pickPacket label erase range s).inside.length)) :
    eval f (spell label ((pickPacket label erase range s).reorder σ)) = eval f (spell label s) := by
  let p := pickPacket label erase range s
  have hseq : (List.ofFn (p.inside.get ∘ σ)).Perm p.inside := by
    simpa using σ.ofFn_comp_perm p.inside.get
  have hev := eval_perm_uniform f erase t hc (spell_perm label hseq).symm hu
  conv_rhs => rw [← pickPacket_join label erase range s]
  change eval f (spell label (p.reorder σ)) = eval f (spell label p.join)
  simp only [Cancellation.Packet.join, Cancellation.Packet.reorder, spell_append, eval_append]
  rw [hev]

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {Γ α T K A : Type*} [Fintype Γ] [CommRing K] [CharP K 2]
  [Ring A] [Algebra K A]

def candidates (Γ : Type*) [Fintype Γ] (n : ℕ) : Finset (List Γ) :=
  Finset.univ.image (fun s : Σ r : Fin (n+1), Fin r.val → Γ => List.ofFn s.2)

lemma mem_candidates (n : ℕ) (s : List Γ) : s ∈ candidates Γ n ↔ s.length ≤ n := by
  simp only [candidates, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨r,f⟩,rfl⟩
    simp only [List.length_ofFn]
    omega
  · intro hs
    exact ⟨⟨⟨s.length,by omega⟩,s.get⟩,List.ofFn_get s⟩

def chunkSum {d : ℕ} (label : Γ → List α) (W : Γ → Matrix (Fin d) (Fin d) K)
    (f : α → A) (n : ℕ) (i j : Fin d) : A :=
  ∑ s ∈ (candidates Γ n).filter (fun s => (spell label s).length = n),
    Cancellation.chunkWeight W s i j • eval f (spell label s)

theorem chunkSum_eq_zero_of_ranges {d b n : ℕ}
    (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (hb : ∀ c, (label c).length ≤ b)
    (erase : α → T) (range : List T → ℕ × ℕ)
    (W : Γ → Matrix (Fin d) (Fin d) K) (f : α → A)
    (hrun : ∀ s : List Γ, (spell label s).length = n → eval f (spell label s) ≠ 0 →
      let a := (range ((spell label s).map erase)).1
      let e := (range ((spell label s).map erase)).2
      e ≤ (spell label s).length ∧ b*(d^2+3) < e-a ∧
      (((spell label s).drop a).take (e-a)).Nodup ∧
      ∃ t : T, (∀ x ∈ ((spell label s).drop a).take (e-a), erase x = t) ∧
        ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (i j : Fin d) : chunkSum label W f n i j = 0 := by
  let Q := (candidates Γ n).filter (fun s => (spell label s).length = n)
  let S := Q.filter (fun s => eval f (spell label s) ≠ 0)
  have hS {s : List Γ} (hs : s ∈ S) :
      s.length ≤ n ∧ (spell label s).length = n ∧ eval f (spell label s) ≠ 0 := by
    obtain ⟨hs,hne⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    exact ⟨(mem_candidates n s).mp hs,hl,hne⟩
  let pick := pickPacket label erase range
  have info (s : List Γ) (hs : s ∈ S) :
      (range ((spell label s).map erase)).1 ≤ (spell label s).length ∧
      (spell label (pick s).inside).Nodup ∧ d^2 < (pick s).inside.length ∧
      ∃ t : T, (∀ x ∈ spell label (pick s).inside, erase x=t) ∧
        ∀ x y, erase x=t → erase y=t → Commute (f x) (f y) := by
    obtain ⟨_,hn,hv⟩ := hS hs
    obtain ⟨he,hl,hd,t,hu,hc⟩ := hrun s hn hv
    let a := (range ((spell label s).map erase)).1
    let e := (range ((spell label s).map erase)).2
    have hmul : b ≤ b*(d^2+3) := by nlinarith
    have ha : a ≤ (spell label s).length := by dsimp [a,e] at *; omega
    have hae : PacketIntervals.total (fun c => (label c).length)
        (PacketIntervals.select (fun c => (label c).length) s a e).before ≤ e := by
      have ht := PacketIntervals.select_before_bound (fun c => (label c).length)
        s a e b (fun c _ => hb c)
      dsimp [a,e] at *
      omega
    have sub := select_spelling_sublist label s a e ha hae
    have lng := PacketIntervals.select_long (fun c => (label c).length) s a e b d
      (fun c _ => hb c) (by simpa only [length_spell] using he) hl
    refine ⟨ha,hd.sublist sub,lng,t,?_,hc⟩
    exact fun x hx => hu x (sub.subset hx)
  have same (s : List Γ) (hs : s ∈ S) (σ : Equiv.Perm (Fin (pick s).inside.length)) :
      eval f (spell label ((pick s).reorder σ)) = eval f (spell label s) := by
    obtain ⟨_,_,_,t,hu,hc⟩ := info s hs
    exact pickPacket_same_value label erase range f s t hu hc σ
  have hz := Cancellation.packet_cancellation S W (fun s => eval f (spell label s)) pick
    (fun s _ => pickPacket_join label erase range s)
    (fun s hs => nodup_of_spell_nodup label hne _ (info s hs).2.1)
    (fun s hs => (info s hs).2.2.1)
    (fun s hs σ => by
      obtain ⟨hlen,hn,hv⟩ := hS hs
      have hp := reordered_perm (pick s) s (pickPacket_join label erase range s) σ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
      · exact (mem_candidates n _).mpr (hp.length_eq.trans_le hlen)
      · exact (spell_perm label hp).length_eq.trans hn
      · rw [same s hs σ]
        exact hv)
    (fun s hs σ => by
      obtain ⟨ha,_,_,t,hu,_⟩ := info s hs
      exact pickPacket_stable label erase range s ha t hu σ)
    same i j
  change (∑ s ∈ Q, Cancellation.chunkWeight W s i j • eval f (spell label s)) = 0
  rw [← hz]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have hv : eval f (spell label s) = 0 := by
    by_contra hv
    exact hs (Finset.mem_filter.mpr ⟨‹s ∈ Q›,hv⟩)
  simp [hv]

end
end SourceBurnside.DirectCancellation

end

end OAI
