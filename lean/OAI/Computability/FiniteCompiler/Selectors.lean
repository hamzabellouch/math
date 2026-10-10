import OAI.Computability.FiniteCompiler.Rewriting
import OAI.Computability.FiniteCompiler.Effectivity

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
namespace Envelopes
variable {S : Type*}

def frame (d l r h : S) (N : ℕ) (w : List S) : List S :=
  d :: (List.replicate N l ++ w ++ List.replicate N r ++ [h])

@[simp] theorem length_frame (d l r h : S) (N : ℕ) (w : List S) :
    (frame d l r h N w).length = 2*N+2+w.length := by
  simp [frame]; omega

theorem infix_strip_cons {a d : S} {v w : List S} (hd : d≠a)
    (h : d::v <:+: a::w) : d::v <:+: w := by
  obtain ⟨x,y,he⟩ := h
  cases x with
  | nil => exact False.elim (hd (List.cons.inj he).1)
  | cons b x =>
    have hh : x++(d::v)++y=w := (List.cons.inj he).2
    exact ⟨x,y,hh⟩

theorem infix_strip_prefix {d : S} {v p w : List S} (hd : d∉p)
    (h : d::v <:+: p++w) : d::v <:+: w := by
  induction p with
  | nil => exact h
  | cons a p ih =>
    exact ih (fun hh => hd (List.mem_cons_of_mem _ hh))
      (infix_strip_cons (fun he => hd (by simp [he])) h)

theorem infix_strip_suffix {h : S} {v p w : List S} (hh : h∉p)
    (hi : v++[h] <:+: w++p) : v++[h] <:+: w := by
  have hr : h :: v.reverse <:+: p.reverse ++ w.reverse := by
    simpa using hi.reverse
  have hs := infix_strip_prefix (by simpa using hh) hr
  simpa using hs.reverse

theorem prefix_mem_initial {v p q : List S} (hv : v <+: p++q)
    (hlen : v.length ≤ p.length) : v ⊆ p := by
  have ht : (p++q).take v.length = v := by
    obtain ⟨t,he⟩ := hv
    rw [← he]
    simp
  have htake : (p++q).take v.length = p.take v.length := List.take_append_of_le_length hlen
  rw [htake] at ht
  intro a ha
  apply (List.take_sublist v.length p).subset
  rw [ht]
  exact ha

theorem infix_strip_outer {v w : List S} {a : S}
    (hi : v <:+: a::w) (hn : ¬ v <+: a::w) : v <:+: w := by
  obtain ⟨x,y,he⟩ := hi
  cases x with
  | nil => exact False.elim (hn ⟨y,he⟩)
  | cons b x => exact ⟨x,y,(List.cons.inj he).2⟩

/-- A short older selector cannot start in, or straddle, the new left guard. -/
theorem bounded_strip_left {d l h : S} {v w : List S} {N : ℕ}
    (hdl : d≠l) (hhd : h≠d) (hhl : h≠l) (hend : h∈d::v)
    (hlen : (d::v).length ≤ N) (hi : d::v <:+: d::(List.replicate N l++w)) :
    d::v <:+: w := by
  have hn : ¬ d::v <+: d::(List.replicate N l++w) := by
    intro hp
    have hm : h ∈ d :: List.replicate N l :=
      prefix_mem_initial (p := d::List.replicate N l) hp
        (by simp only [List.length_cons,List.length_replicate] at hlen ⊢; omega) hend
    simp only [List.mem_cons,List.mem_replicate] at hm
    rcases hm with ha | ⟨_,hl⟩
    · exact hhd ha
    · exact hhl hl
  have hs := infix_strip_outer hi hn
  exact infix_strip_prefix (by simp [hdl]) hs

/-- Every older selector side of length at most N lies wholly in the body of
    an N-envelope. Its body is checked irreducible when that envelope is chosen. -/
theorem bounded_infix_frame {d l r h : S} {v w : List S} {N : ℕ}
    (hdl : d≠l) (hhr : h≠r) (hhd : h≠d) (hhl : h≠l) (hdr : d≠r)
    (hlen : (d::(v++[h])).length ≤ N)
    (hi : d::(v++[h]) <:+: frame d l r h N w) : d::(v++[h]) <:+: w := by
  have hleft : d::(v++[h]) <:+: w++List.replicate N r++[h] :=
    bounded_strip_left hdl hhd hhl (by simp) hlen (by simpa [frame,List.append_assoc] using hi)
  have hrev : h::(v.reverse++[d]) <:+: h::(List.replicate N r++w.reverse) := by
    simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using hleft.reverse
  have hlen' : (h::(v.reverse++[d])).length ≤ N := by simpa using hlen
  have hh := bounded_strip_left hhr hhd.symm hdr (by simp) hlen' hrev
  simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using hh.reverse

/-- The purely alphabetic version used for static/selector overlaps. -/
theorem alphabet_infix_frame {d l r h a b : S} {v w : List S} {N : ℕ}
    (had : a≠d) (hal : a≠l) (hbr : b≠r) (hbh : b≠h)
    (hi : a::(v++[b]) <:+: frame d l r h N w) : a::(v++[b]) <:+: w := by
  have hleft : a::(v++[b]) <:+: w++List.replicate N r++[h] :=
    infix_strip_prefix (p := d::List.replicate N l) (by simp [had,hal])
      (by simpa [frame,List.append_assoc] using hi)
  have ht : (a::v)++[b] <:+: w++(List.replicate N r++[h]) := by
    simpa only [List.cons_append,List.append_assoc] using hleft
  exact infix_strip_suffix (by simp [hbr,hbh]) ht

/-- The long header has exactly one occurrence in its own envelope. -/
theorem header_unique {d l r h : S} {N : ℕ} {w x y : List S}
    (hdl : d≠l) (hlr : l≠r) (hlh : l≠h) (hw : w.length < N)
    (he : frame d l r h N w = x++(d::List.replicate N l)++y) : x=[] := by
  cases x with
  | nil => rfl
  | cons a x =>
    have hi : d::List.replicate N l <:+: List.replicate N l++w++List.replicate N r++[h] :=
      ⟨x,y,(List.cons.inj he).2.symm⟩
    have hs : d::List.replicate N l <:+: w++List.replicate N r++[h] :=
      infix_strip_prefix (p := List.replicate N l) (by simp [hdl]) (by simpa only [List.append_assoc] using hi)
    have hn : 0<N := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
    have hs' : (d::List.replicate k l)++[l] <:+: w++(List.replicate (k+1) r++[h]) := by
      simpa only [List.replicate_succ',List.cons_append,List.append_assoc] using hs
    have hb := infix_strip_suffix (by simp [hlr,hlh]) hs'
    have hh := hb.length_le
    simp only [List.length_append,List.length_cons,List.length_replicate] at hh
    omega

/-- Prefix-comparable same-stage envelopes have equal bodies. -/
theorem prefix_frame {d l r h : S} {N : ℕ} {u v : List S}
    (hhr : h≠r) (_ : u.length<N) (hv : v.length<N)
    (hp : frame d l r h N u <+: frame d l r h N v) : u=v := by
  have ht : u++List.replicate N r++[h] <+: v++List.replicate N r++[h] := by
    apply (List.prefix_self_append_iff (l₃ := d::List.replicate N l)).mp
    simpa only [frame,List.cons_append,List.append_assoc] using hp
  have hle : u.length ≤ v.length := by
    have hh := ht.length_le
    simp only [List.length_append,List.length_replicate,List.length_singleton] at hh
    omega
  have heq : u.length=v.length := by
    by_contra heq
    have hlt : u.length<v.length := by omega
    have h₁ : u.length+N < (u++List.replicate N r++[h]).length := by simp
    have hh := ht.getElem h₁
    have he₁ : (u++List.replicate N r++[h])[u.length+N] = h := by
      rw [List.getElem_append_right (by simp)]
      simp
    have h₂ : u.length+N < (v++List.replicate N r++[h]).length := by simp; omega
    have he₂ : (v++List.replicate N r++[h])[u.length+N]'h₂ = r := by
      rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_append_right (by omega)]
      simp
    exact hhr (he₁.symm.trans (hh.trans he₂))
  have he := ht.eq_of_length (by simp [heq])
  exact List.append_cancel_right (List.append_cancel_right he)

/-- Same-stage left sides cannot properly contain one another. -/
theorem infix_frame {d l r h : S} {N : ℕ} {u v x y : List S}
    (hdl : d≠l) (hlr : l≠r) (hlh : l≠h) (hhr : h≠r)
    (hu : u.length<N) (hv : v.length<N)
    (he : frame d l r h N u = x++frame d l r h N v++y) :
    x=[] ∧ u=v ∧ y=[] := by
  have hx : x=[] := header_unique hdl hlr hlh hu
    (y := v++List.replicate N r++[h]++y) (by simpa [frame,List.append_assoc] using he)
  subst x
  have hp : frame d l r h N v <+: frame d l r h N u := ⟨y,by simpa using he.symm⟩
  have hvu := prefix_frame hhr hv hu hp
  subst v
  have hy := congrArg List.length he
  simp only [List.nil_append,List.length_append] at hy
  exact ⟨rfl,rfl,List.length_eq_zero_iff.mp (by omega)⟩

theorem frame_last {d l r h : S} {N : ℕ} {w : List S} :
    (frame d l r h N w).getLast? = some h := by
  change ((d::(List.replicate N l++w++List.replicate N r))++[h]).getLast? = some h
  rw [List.getLast?_append]
  rfl

/-- A suffix ending in h cannot be a short prefix of a fresh header. -/
theorem no_short_overlap {d l r h : S} {N : ℕ} {w m : List S}
    (hhd : h≠d) (hhl : h≠l) (hm : m.getLast? = some h)
    (hpre : m <+: frame d l r h N w) (hlen : m.length ≤ N+1) : False := by
  have hh : h∈m := List.mem_of_getLast? hm
  have hi : h∈d::List.replicate N l :=
    prefix_mem_initial (p := d::List.replicate N l)
      (by simpa [frame,List.append_assoc] using hpre) (by simpa using hlen) hh
  simp [hhd,hhl] at hi

/-- Aligned headers and guards exclude every proper same-stage boundary peak. -/
theorem overlap_frame {d l r h : S} {N : ℕ} {u v p m q : List S}
    (hdl : d≠l) (hlr : l≠r) (hlh : l≠h) (hhr : h≠r) (hhd : h≠d)
    (hu : u.length<N) (hv : v.length<N) (hm : m≠[])
    (he₁ : frame d l r h N u = p++m)
    (he₂ : frame d l r h N v = m++q) : p=[] ∧ u=v ∧ q=[] := by
  have hlast : m.getLast? = some h := by
    have hh := frame_last (d := d) (l := l) (r := r) (h := h) (N := N) (w := u)
    rw [he₁,List.getLast?_append,List.getLast?_eq_some_getLast hm] at hh
    simpa only [List.getLast?_eq_some_getLast hm, Option.some_or] using hh
  have hpre : m <+: frame d l r h N v := ⟨q,he₂.symm⟩
  have hlen : N+1 < m.length := by
    by_contra hh
    exact no_short_overlap hhd hlh.symm hlast hpre (by omega)
  have hh : d::List.replicate N l <+: m := by
    apply List.prefix_of_prefix_length_le
      (l₃ := frame d l r h N v) _ hpre (by simp; omega)
    exact ⟨v++List.replicate N r++[h],by simp [frame,List.append_assoc]⟩
  obtain ⟨t,ht⟩ := hh
  have hp : p=[] := header_unique hdl hlr hlh hu
    (by simpa [← ht,List.append_assoc] using he₁)
  subst p
  have hem : frame d l r h N u=m := by simpa using he₁
  have huv := prefix_frame hhr hu hv (hem.symm ▸ hpre)
  subst v
  have hq := congrArg List.length (he₂.trans (congrArg (·++q) hem.symm))
  simp only [List.length_append] at hq
  exact ⟨rfl,rfl,List.length_eq_zero_iff.mp (by omega)⟩

@[simp] theorem reverse_frame (d l r h : S) (N : ℕ) (w : List S) :
    (frame d l r h N w).reverse = frame h r l d N w.reverse := by
  simp [frame,List.append_assoc]

/-- Different-stage boundary overlaps are excluded by spacing alone; this
    does not depend on which earlier stage passed its irreducibility test. -/
theorem short_long_overlap {d l r h : S} {N M : ℕ} {u v p m q : List S}
    (hhd : h≠d) (hhl : h≠l) (hsmall : (frame d l r h N u).length≤M+1)
    (hm : m≠[]) (he : frame d l r h N u=p++m)
    (hf : frame d l r h M v=m++q) : False := by
  have hlast : m.getLast?=some h := by
    have hh := frame_last (d := d) (l := l) (r := r) (h := h) (N := N) (w := u)
    rw [he,List.getLast?_append,List.getLast?_eq_some_getLast hm] at hh
    simpa only [List.getLast?_eq_some_getLast hm,Option.some_or] using hh
  apply no_short_overlap hhd hhl hlast ⟨q,hf.symm⟩
  have hh := congrArg List.length he
  simp only [List.length_append] at hh
  omega

theorem long_short_overlap {d l r h : S} {N M : ℕ} {u v p m q : List S}
    (hdh : d≠h) (hdr : d≠r) (hsmall : (frame d l r h N v).length≤M+1)
    (hm : m≠[]) (he : frame d l r h M u=p++m)
    (hf : frame d l r h N v=m++q) : False := by
  apply short_long_overlap hdh hdr (u := v.reverse) (v := u.reverse)
    (p := q.reverse) (m := m.reverse) (q := p.reverse)
  · simpa using hsmall
  · simpa using hm
  · simpa using congrArg List.reverse hf
  · simpa using congrArg List.reverse he

/-- General form of code containment: only avoidance of the four envelope
    markers is used, so it applies to either of the two disjoint code types. -/
theorem avoiding_infix_frame {d l r h : S} {N : ℕ} {u w : List S}
    (hn : u≠[]) (hd : d∉u) (hl : l∉u) (hr : r∉u) (hh : h∉u)
    (hi : u <:+: frame d l r h N w) : u <:+: w := by
  have hleft : u <:+: w++List.replicate N r++[h] := by
    cases u with
    | nil => contradiction
    | cons a u =>
      apply infix_strip_prefix (p := d::List.replicate N l) ?_
        (by simpa [frame,List.append_assoc] using hi)
      simp only [List.mem_cons,List.mem_replicate]
      rintro (ha | ⟨_,ha⟩)
      · exact hd (by simp [ha])
      · exact hl (by simp [ha])
  rcases List.eq_nil_or_concat' u with he | ⟨v,b,rfl⟩
  · exact False.elim (hn he)
  · apply infix_strip_suffix (p := List.replicate N r++[h]) ?_
      (by simpa only [List.append_assoc] using hleft)
    simp only [List.mem_append,List.mem_replicate,List.mem_singleton]
    rintro (⟨_,hb⟩ | hb)
    · exact hr (by simp [hb])
    · exact hh (by simp [hb])

/-- A code suffix cannot meet the first envelope marker. -/
theorem avoiding_frame_overlap_left {d l r h : S} {N : ℕ} {u w p m q : List S}
    (hd : d∉u) (hm : m≠[]) (he : u=p++m) (hf : frame d l r h N w=m++q) : False := by
  cases m with
  | nil => contradiction
  | cons a m =>
    have ha : d=a := (List.cons.inj hf).1
    apply hd
    simp [he,ha]

/-- An envelope suffix cannot meet a code prefix because it ends in h. -/
theorem avoiding_frame_overlap_right {d l r h : S} {N : ℕ} {u w p m q : List S}
    (hh : h∉u) (hm : m≠[]) (he : frame d l r h N w=p++m) (hf : u=m++q) : False := by
  exact avoiding_frame_overlap_left (u := u.reverse) (m := m.reverse)
    (p := q.reverse) (q := p.reverse) (d := h) (l := r) (r := l) (h := d)
    (N := N) (w := w.reverse) (by simpa using hh) (by simpa using hm)
    (by simpa using congrArg List.reverse hf)
    (by simpa using congrArg List.reverse he)

end Envelopes

open Relation
variable {S : Type*} {rs : List (List S × List S)}

theorem join_context {u v : List S} (h : Join (Steps rs) u v) (x y : List S) :
    Join (Steps rs) (x++u++y) (x++v++y) := by
  obtain ⟨z,huz,hvz⟩ := h
  exact ⟨x++z++y,steps_context huz x y,steps_context hvz x y⟩

/-- The two critical configurations, checked only inside the current length ball. -/
def Critical (rs : List (List S × List S)) (n : ℕ) : Prop :=
  (∀ u u' v v', (u,u')∈rs → (v,v')∈rs → ∀ a b, u=a++v++b → u.length≤n →
    Join (Steps rs) u' (a++v'++b)) ∧
  (∀ u u' v v', (u,u')∈rs → (v,v')∈rs → ∀ p m q, m≠[] →
    u=p++m → v=m++q → (p++m++q).length≤n →
    Join (Steps rs) (u'++q) (p++v'))

theorem critical_ordered {n : ℕ} (crit : Critical rs n)
    {u u' v v' x y a b : List S} (hu : (u,u')∈rs) (hv : (v,v')∈rs)
    (he : x++u++y=a++v++b) (hlen : (x++u++y).length≤n) (hxa : x.length≤a.length) :
    Join (Steps rs) (x++u'++y) (a++v'++b) := by
  have hp₁ : x <+: x++u++y := ⟨u++y,by simp only [List.append_assoc]⟩
  have hp₂ : a <+: x++u++y := ⟨v++b,by simpa only [List.append_assoc] using he.symm⟩
  obtain ⟨p,hp⟩ := List.prefix_of_prefix_length_le hp₁ hp₂ hxa
  subst a
  have hs : u++y=p++(v++b) :=
    List.append_cancel_left (by simpa only [List.append_assoc] using he)
  rcases List.append_eq_append_iff.mp hs with ⟨t,rfl,hy⟩ | ⟨s,huv,hvb⟩
  · subst y
    refine ⟨x++u'++t++v'++b,?_,?_⟩
    · exact .single (by simpa only [List.append_assoc] using Step.apply hv (x++u'++t) b)
    · exact .single (by simpa only [List.append_assoc] using Step.apply hu x (t++v'++b))
  · rcases List.append_eq_append_iff.mp hvb.symm with ⟨c,hvc,hy⟩ | ⟨c,hsc,hb⟩
    · by_cases hsn : s=[]
      · subst s
        simp only [List.append_nil] at huv
        subst u
        simp only [List.nil_append] at hvc
        subst v
        subst y
        refine ⟨x++u'++v'++b,?_,?_⟩
        · exact .single (by simpa only [List.append_assoc] using Step.apply hv (x++u') b)
        · exact .single (by simpa only [List.append_assoc] using Step.apply hu x (v'++b))
      · have hj := crit.2 u u' v v' hu hv p s c hsn huv hvc
          (by simp only [huv,hy,List.length_append] at hlen; simp only [List.length_append]; omega)
        have hc := join_context hj x b
        simpa only [hy,List.append_assoc] using hc
    · have hj := crit.1 u u' v v' hu hv p c
        (by simp only [huv,hsc,List.append_assoc])
        (by simp only [List.length_append] at hlen; omega)
      have hc := join_context hj x y
      simpa only [hb,List.append_assoc] using hc

theorem step_decompose {a b : List S} (h : Step rs a b) :
    ∃ u v x y, (u,v)∈rs ∧ a=x++u++y ∧ b=x++v++y := by
  cases h with
  | apply h x y => exact ⟨_,_,x,y,h,rfl,rfl⟩

/-- Critical-pair reduction, including disjoint, boundary and containment peaks. -/
theorem critical_localJoin {n : ℕ} (crit : Critical rs n) {w a b : List S}
    (hw : w.length≤n) (ha : Step rs w a) (hb : Step rs w b) : Join (Steps rs) a b := by
  obtain ⟨u,u',x,y,hu,rfl,rfl⟩ := step_decompose ha
  obtain ⟨v,v',a,b,hv,he,rfl⟩ := step_decompose hb
  rcases le_total x.length a.length with h | h
  · exact critical_ordered crit hu hv he hw h
  · obtain ⟨z,haz,hbz⟩ := critical_ordered crit hv hu he.symm (by simpa only [he] using hw) h
    exact ⟨z,hbz,haz⟩

end

section
open Relation Envelopes
namespace Selectors
variable {S : Type*}

structure Markers (S : Type*) where
  zero : S
  d : S
  l : S
  r : S
  h : S
  distinct : List.Pairwise (· ≠ ·) [zero,d,l,r,h]

namespace Markers
variable (a : Markers S)
theorem z_d : a.zero≠a.d := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem z_l : a.zero≠a.l := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem z_r : a.zero≠a.r := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem z_h : a.zero≠a.h := by have := a.distinct; simpa using (List.pairwise_cons.mp this).1 _ (by simp)
theorem d_l : a.d≠a.l := by have := (List.pairwise_cons.mp a.distinct).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem d_r : a.d≠a.r := by have := (List.pairwise_cons.mp a.distinct).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem d_h : a.d≠a.h := by have := (List.pairwise_cons.mp a.distinct).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem l_r : a.l≠a.r := by have := (List.pairwise_cons.mp (List.pairwise_cons.mp a.distinct).2).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem l_h : a.l≠a.h := by have := (List.pairwise_cons.mp (List.pairwise_cons.mp a.distinct).2).2; exact (List.pairwise_cons.mp this).1 _ (by simp)
theorem r_h : a.r≠a.h := by have := (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp a.distinct).2).2).2; simpa using this

abbrev wrap (N : ℕ) (w : List S) : List S := frame a.d a.l a.r a.h N w

theorem wrap_avoids {N : ℕ} {w : List S} (hw : a.zero∉w) : a.zero∉a.wrap N w := by
  simp [wrap,frame,hw,a.z_d,a.z_l,a.z_r,a.z_h]
end Markers

variable [DecidableEq S] (a : Markers S)

/-- Literal selector rules, with the first member sent to the empty word. -/
def rules (N : ℕ) (ws : List (List S)) : List (List S × List S) :=
  ws.map fun w => (a.wrap N w,if ws.head?=some w then [] else [a.zero])

theorem mem_rules {N : ℕ} {ws : List (List S)} {u v : List S} :
    (u,v)∈rules a N ws ↔ ∃ w∈ws, u=a.wrap N w ∧ v=if ws.head?=some w then [] else [a.zero] := by
  simp only [rules,List.mem_map,Prod.mk.injEq]
  aesop

/-- The only possible old left-side shapes at a selector stage. -/
def Old (N : ℕ) (u : List S) : Prop :=
  a.zero∈u ∨
  (u≠[] ∧ a.d∉u ∧ a.l∉u ∧ a.r∉u ∧ a.h∉u) ∨
  ∃ M w, u=a.wrap M w ∧ u.length<N

omit [DecidableEq S] in
theorem no_occurrence {rs : List (List S × List S)} {w u v : List S}
    (hw : Irreducible (Step rs) w) (hp : (u,v)∈rs) (hi : u <:+: w) : False := by
  obtain ⟨x,y,he⟩ := hi
  exact hw _ (he ▸ Step.apply hp x y)

omit [DecidableEq S] in
theorem old_in_new {rs : List (List S × List S)} {N : ℕ} {u v w : List S}
    (hu : Old a N u) (huz : a.zero∉u) (hp : (u,v)∈rs)
    (hw : Irreducible (Step rs) w) (hi : u <:+: a.wrap N w) : False := by
  rcases hu with hz | ⟨hn,hd,hl,hr,hh⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · exact no_occurrence hw hp (avoiding_infix_frame hn hd hl hr hh hi)
  · apply no_occurrence hw hp
    apply bounded_infix_frame a.d_l a.r_h.symm a.d_h.symm a.l_h.symm a.d_r
      (by simpa [Markers.wrap,frame,List.append_assoc] using Nat.le_of_lt hlen)
      (by simpa [Markers.wrap,frame,List.append_assoc] using hi)

omit [DecidableEq S] in
theorem new_in_old {N : ℕ} {u w : List S} (hu : Old a N u) (huz : a.zero∉u)
    (hi : a.wrap N w <:+: u) : False := by
  rcases hu with hz | ⟨_,hd,_,_,_⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · apply hd
    exact hi.subset (by simp [Markers.wrap,frame])
  · have hh := hi.length_le
    simp only [Markers.wrap,length_frame] at hh hlen
    omega

omit [DecidableEq S] in
theorem old_new_overlap {N : ℕ} {u w p m q : List S} (hu : Old a N u) (huz : a.zero∉u)
    (hm : m≠[]) (he : u=p++m) (hf : a.wrap N w=m++q) : False := by
  rcases hu with hz | ⟨_,hd,_,_,_⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · exact avoiding_frame_overlap_left hd hm he hf
  · exact short_long_overlap a.d_h.symm a.l_h.symm (by change (a.wrap M t).length≤N+1; omega) hm he hf

omit [DecidableEq S] in
theorem new_old_overlap {N : ℕ} {u w p m q : List S} (hu : Old a N u) (huz : a.zero∉u)
    (hm : m≠[]) (he : a.wrap N w=p++m) (hf : u=m++q) : False := by
  rcases hu with hz | ⟨_,_,_,_,hh⟩ | ⟨M,t,rfl,hlen⟩
  · exact huz hz
  · exact avoiding_frame_overlap_right hh hm he hf
  · exact long_short_overlap a.d_h a.d_r (by change (a.wrap M t).length≤N+1; omega) hm he hf

omit [DecidableEq S] in
theorem join_mono {rs rt : List (List S × List S)} (ht : ∀ p∈rs,p∈rt)
    {u v : List S} (h : Join (Steps rs) u v) : Join (Steps rt) u v := by
  obtain ⟨w,hu,hv⟩ := h
  exact ⟨w,steps_mono ht hu,steps_mono ht hv⟩

omit [DecidableEq S] in
theorem zero_join {rs : List (List S × List S)}
    (hz : Absorbs rs a.zero) (hp : ∀ p∈rs,a.zero∈p.1 → a.zero∈p.2)
    {w u v : List S} (hw : a.zero∈w) (hu : Step rs w u) (hv : Step rs w v) :
    Join (Steps rs) u v :=
  ⟨[a.zero],absorbs_mem hz (step_preserves_letter hp hw hu),
    absorbs_mem hz (step_preserves_letter hp hw hv)⟩

/-- The actual finite selector extension preserves the entire bounded critical
    condition, not just the disjoint cases. All irreducibility tests are on bodies. -/
theorem critical_extension {rs : List (List S × List S)} {N B : ℕ} {ws : List (List S)}
    (hz : Absorbs rs a.zero) (hp : ∀ p∈rs,a.zero∈p.1 → a.zero∈p.2)
    (hold : ∀ p∈rs,Old a N p.1)
    (hws : ∀ w∈ws, w.length<N ∧ a.zero∉w ∧ Irreducible (Step rs) w)
    (hc : Critical rs B) : Critical (rs++rules a N ws) B := by
  let rt := rs++rules a N ws
  have hinc : ∀ p∈rs,p∈rt := fun _ h => List.mem_append_left _ h
  have hz' : Absorbs rt a.zero := fun b => ⟨hinc _ (hz b).1,hinc _ (hz b).2⟩
  have hp' : ∀ p∈rt,a.zero∈p.1 → a.zero∈p.2 := by
    intro ⟨u,v⟩ ht hu
    rcases List.mem_append.mp ht with ht | ht
    · exact hp _ ht hu
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp ht
      exact False.elim (a.wrap_avoids (hws w hw).2.1 hu)
  constructor
  · intro u u' v v' hu hv x y he hlen
    by_cases huz : a.zero∈u
    · apply zero_join a hz' hp' huz
      · simpa using Step.apply hu [] []
      · simpa only [he] using Step.apply hv x y
    have hvz : a.zero∉v := fun hh => huz (by simp [he,hh])
    rcases List.mem_append.mp hu with hu | hu <;> rcases List.mem_append.mp hv with hv | hv
    · exact join_mono hinc (hc.1 _ _ _ _ hu hv x y he hlen)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hv
      exact False.elim (new_in_old a (hold _ hu) huz ⟨x,y,he.symm⟩)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      exact False.elim (old_in_new a (hold _ hv) hvz hv (hws w hw).2.2 ⟨x,y,he.symm⟩)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      obtain ⟨t,ht,rfl,rfl⟩ := (mem_rules a).mp hv
      obtain ⟨rfl,rfl,rfl⟩ := infix_frame a.d_l a.l_r a.l_h a.r_h.symm
        (hws w hw).1 (hws t ht).1 he
      exact ⟨_,.refl,by simpa using (ReflTransGen.refl : Steps (rs++rules a N ws) (if ws.head?=some w then [] else [a.zero]) _)⟩
  · intro u u' v v' hu hv p m q hm he hf hlen
    by_cases hwz : a.zero∈p++m++q
    · apply zero_join a hz' hp' hwz
      · simpa only [rt,he,List.append_assoc,List.nil_append] using Step.apply hu [] q
      · simpa only [rt,hf,List.append_assoc,List.append_nil] using Step.apply hv p []
    have huz : a.zero∉u := fun hh => hwz (by simpa only [he,List.mem_append] using Or.inl hh)
    have hvz : a.zero∉v := by
      intro hh
      apply hwz
      simp only [hf,List.mem_append] at hh
      simp only [List.mem_append]
      aesop
    rcases List.mem_append.mp hu with hu | hu <;> rcases List.mem_append.mp hv with hv | hv
    · exact join_mono hinc (hc.2 _ _ _ _ hu hv p m q hm he hf hlen)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hv
      exact False.elim (old_new_overlap a (hold _ hu) huz hm he hf)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      exact False.elim (new_old_overlap a (hold _ hv) hvz hm he hf)
    · obtain ⟨w,hw,rfl,rfl⟩ := (mem_rules a).mp hu
      obtain ⟨t,ht,rfl,rfl⟩ := (mem_rules a).mp hv
      obtain ⟨rfl,rfl,rfl⟩ := overlap_frame a.d_l a.l_r a.l_h a.r_h.symm a.d_h.symm
        (hws w hw).1 (hws t ht).1 hm he hf
      exact ⟨if ws.head?=some w then [] else [a.zero],
        by simpa using (ReflTransGen.refl : Steps (rs++rules a N ws) (if ws.head?=some w then [] else [a.zero]) _),
        by simpa using (ReflTransGen.refl : Steps (rs++rules a N ws) (if ws.head?=some w then [] else [a.zero]) _)⟩

end Selectors
end

section
open Relation
namespace Selectors
variable {S : Type*} [DecidableEq S] (a : Markers S)

/-- A potential tuple and its envelope size, independent of all class tests. -/
structure Stage (S : Type*) where
  size : ℕ
  bodies : List (List S)

variable {a}

def allowed (rs : List (List S × List S)) (s : Stage S) : Bool :=
  s.bodies.all (fun w => (next rs w).isNone)

def choose (rs : List (List S × List S)) (s : Stage S) (n : ℕ) : List (List S × List S) :=
  if s.size ≤ n ∧ allowed rs s then rs++rules a s.size s.bodies else rs

def process (base : List (List S × List S)) (stages : ℕ → Stage S) (n : ℕ) : ℕ → List (List S × List S)
  | 0 => base
  | j+1 => choose (a:=a) (process base stages n j) (stages j) n

def BoundedEq (rs rt : List (List S × List S)) (k : ℕ) : Prop :=
  ∀ p, p.1.length ≤ k → (p ∈ rs ↔ p ∈ rt)

theorem allowed_iff {rs : List (List S × List S)} {s : Stage S} :
    allowed rs s = true ↔ ∀ w ∈ s.bodies, Irreducible (Step rs) w := by
  simp only [allowed,List.all_eq_true,Option.isNone_iff_eq_none]
  apply forall₂_congr
  intro w hw
  constructor
  · exact next_none
  · intro h
    cases hn : next rs w with
    | none => rfl
    | some v => exact False.elim (h v (next_sound hn))

omit [DecidableEq S] in
theorem irreducible_bounded {rs rt : List (List S × List S)} {k : ℕ}
    (hh : BoundedEq rs rt k) {w : List S} (hw : w.length ≤ k) :
    Irreducible (Step rs) w ↔ Irreducible (Step rt) w := by
  constructor <;> intro h v hv
  · exact h v ((step_stable hh hw).mpr hv)
  · exact h v ((step_stable hh hw).mp hv)

theorem choose_contains (rs : List (List S × List S)) (s : Stage S) (n : ℕ) :
    ∀ p ∈ rs,p ∈ choose (a:=a) rs s n := by
  intro p hp
  unfold choose
  split
  · exact List.mem_append_left _ hp
  · exact hp

theorem mem_choose {rs : List (List S × List S)} {s : Stage S} {n : ℕ} {p} :
    p ∈ choose (a:=a) rs s n → p ∈ rs ∨ p ∈ rules a s.size s.bodies := by
  unfold choose
  split
  · exact List.mem_append.mp
  · exact Or.inl

theorem choose_bounded {rs rt : List (List S × List S)} {k n : ℕ} {s : Stage S}
    (hkn : k ≤ n) (hh : BoundedEq rs rt k)
    (hbody : ∀ w ∈ s.bodies,w.length<s.size) :
    BoundedEq (choose (a:=a) rs s k) (choose (a:=a) rt s n) k := by
  by_cases hsk : s.size ≤ k
  · have hs : allowed rs s = true ↔ allowed rt s = true := by
      rw [allowed_iff,allowed_iff]
      exact forall₂_congr (fun w hw => irreducible_bounded hh ((Nat.le_of_lt (hbody w hw)).trans hsk))
    intro p hp
    simp only [choose,hsk,hsk.trans hkn,true_and,hs]
    split
    · simp only [List.mem_append,hh p hp]
    · exact hh p hp
  · have hnew : ∀ p ∈ rules a s.size s.bodies, ¬p.1.length ≤ k := by
      intro ⟨u,v⟩ hp hl
      obtain ⟨w,_,rfl,_⟩ := (mem_rules a).mp hp
      simp only [Markers.wrap,Envelopes.length_frame] at hl
      omega
    intro p hp
    have hn : p∉rules a s.size s.bodies := fun hm => hnew _ hm hp
    simp only [choose,hsk,false_and,↓reduceIte]
    split
    · simp only [List.mem_append,hn,or_false,hh p hp]
    · exact hh p hp

theorem process_bounded {base small : List (List S × List S)} {stages : ℕ → Stage S}
    {k n : ℕ} (hkn : k ≤ n) (hh : BoundedEq small base k)
    (hb : ∀ j w, w ∈ (stages j).bodies → w.length<(stages j).size) (j : ℕ) :
    BoundedEq (process (a:=a) small stages k j) (process (a:=a) base stages n j) k := by
  induction j with
  | zero => exact hh
  | succ j ih => exact choose_bounded hkn ih (hb j)

theorem process_members {base : List (List S × List S)} {stages : ℕ → Stage S} {n j : ℕ} {p} :
    p ∈ process (a:=a) base stages n j → p ∈ base ∨ ∃ i<j,p ∈ rules a (stages i).size (stages i).bodies := by
  induction j with
  | zero => exact Or.inl
  | succ j ih =>
    intro hp
    rcases mem_choose hp with hp | hp
    · rcases ih hp with hp | ⟨i,hi,hp⟩
      · exact Or.inl hp
      · exact Or.inr ⟨i,by omega,hp⟩
    · exact Or.inr ⟨j,by omega,hp⟩

theorem process_contains (base : List (List S × List S)) (stages : ℕ → Stage S) (n j : ℕ) :
    ∀ p ∈ base,p ∈ process (a:=a) base stages n j := by
  induction j with
  | zero => exact fun _ h => h
  | succ j ih => exact fun p h => choose_contains _ _ _ p (ih p h)

theorem process_zero {base : List (List S × List S)} {stages : ℕ → Stage S} {n j : ℕ}
    (hb : ∀ p ∈ base,a.zero ∈ p.1 → a.zero ∈ p.2)
    (hz : ∀ i w, w ∈ (stages i).bodies → a.zero∉w) :
    ∀ p ∈ process (a:=a) base stages n j,a.zero ∈ p.1 → a.zero ∈ p.2 := by
  intro ⟨u,v⟩ hp hu
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hb _ hp hu
  · obtain ⟨w,hw,rfl,_⟩ := (mem_rules a).mp hp
    exact False.elim (a.wrap_avoids (hz i w hw) hu)

/-- Full consecutive selector processing preserves critical joins.  The spacing
    is required for *all potential* earlier sides, selected or not. -/
theorem process_critical {base : List (List S × List S)} {stages : ℕ → Stage S} {n : ℕ}
    (hz : Absorbs base a.zero) (hp : ∀ p ∈ base,a.zero ∈ p.1 → a.zero ∈ p.2)
    (hold : ∀ p ∈ base,a.zero ∈ p.1 ∨ (p.1≠[] ∧ a.d∉p.1 ∧ a.l∉p.1 ∧ a.r∉p.1 ∧ a.h∉p.1))
    (hbody : ∀ i w, w ∈ (stages i).bodies → w.length<(stages i).size ∧ a.zero∉w)
    (hspace : ∀ i j, i<j → ∀ w ∈ (stages i).bodies,(a.wrap (stages i).size w).length<(stages j).size)
    (hc : Critical base n) (j : ℕ) : Critical (process (a:=a) base stages n j) n := by
  induction j with
  | zero => exact hc
  | succ j ih =>
    simp only [process,choose]
    split
    next hs =>
      apply critical_extension a
      · intro b
        exact ⟨process_contains _ _ _ _ _ (hz b).1,process_contains _ _ _ _ _ (hz b).2⟩
      · exact process_zero hp (fun i w hw => (hbody i w hw).2)
      · intro ⟨u,v⟩ hu
        rcases process_members hu with hu | ⟨i,hi,hu⟩
        · rcases hold _ hu with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · obtain ⟨w,hw,rfl,_⟩ := (mem_rules a).mp hu
          exact Or.inr (Or.inr ⟨_,_,rfl,hspace i j hi w hw⟩)
      · intro w hw
        exact ⟨(hbody j w hw).1,(hbody j w hw).2,allowed_iff.mp hs.2 w hw⟩
      · exact ih
    next hs => exact ih

omit [DecidableEq S] in
theorem boundedEq_refl (rs : List (List S × List S)) (k : ℕ) : BoundedEq rs rs k :=
  fun _ _ => Iff.rfl

omit [DecidableEq S] in
theorem boundedEq_trans {rs rt ru : List (List S × List S)} {k : ℕ}
    (h : BoundedEq rs rt k) (g : BoundedEq rt ru k) : BoundedEq rs ru k :=
  fun p hp => (h p hp).trans (g p hp)

theorem choose_inert {rs : List (List S × List S)} {s : Stage S} {n k : ℕ}
    (hs : k  ≤  s.size) : BoundedEq rs (choose (a:=a) rs s n) k := by
  intro p hp
  constructor
  · exact choose_contains _ _ _ _
  · intro hm
    rcases mem_choose hm with hm | hm
    · exact hm
    · rcases p with ⟨u,v⟩
      obtain ⟨w,_,rfl,_⟩ := (mem_rules a).mp hm
      simp only [Markers.wrap,Envelopes.length_frame] at hp
      omega

theorem process_future {base : List (List S × List S)} {stages : ℕ → Stage S}
    {k n lo hi : ℕ} (hle : lo ≤ hi)
    (hs : ∀ j, lo ≤ j → k ≤ (stages j).size) :
    BoundedEq (process (a:=a) base stages n lo) (process (a:=a) base stages n hi) k := by
  induction hi,hle using Nat.le_induction with
  | base => exact boundedEq_refl _ _
  | succ j hj ih => exact boundedEq_trans ih (choose_inert (hs j hj))

/-- Stability for the literal completed tables, whose number of examined tuples
    varies with the normalization bound. -/
theorem tables_bounded {bases : ℕ → List (List S × List S)} {stages : ℕ → Stage S}
    (hb : ∀ k n, k ≤ n → BoundedEq (bases k) (bases n) k)
    (hlen : ∀ j w, w ∈ (stages j).bodies → w.length<(stages j).size)
    (hsize : ∀ j, j<(stages j).size) {k n : ℕ} (hkn : k ≤ n) :
    BoundedEq (process (a:=a) (bases k) stages k k)
      (process (a:=a) (bases n) stages n n) k :=
  boundedEq_trans (process_bounded hkn (hb k n hkn) hlen k)
    (process_future hkn (fun j hj => hj.trans (Nat.le_of_lt (hsize j))))

theorem rules_decrease {r : S → S → Prop} (s : Stage S) :
    ∀ p ∈ rules a s.size s.bodies, List.Shortlex r p.2 p.1 := by
  intro ⟨u,v⟩ hp
  obtain ⟨w,_,rfl,rfl⟩ := (mem_rules a).mp hp
  apply List.Shortlex.of_length_lt
  simp only [Markers.wrap,Envelopes.length_frame]
  split <;> simp
  omega

theorem process_decrease {r : S → S → Prop} {base : List (List S × List S)}
    (hd : ∀ p ∈ base,List.Shortlex r p.2 p.1) (stages : ℕ → Stage S) (n j : ℕ) :
    ∀ p ∈ process (a:=a) base stages n j,List.Shortlex r p.2 p.1 := by
  intro p hp
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hd p hp
  · exact rules_decrease _ p hp

end Selectors
end

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} [DecidableEq Q] [DecidableRel (List.Shortlex r)]

def pickStep (q : Q) (best : List A) (p : List A × Q) : List A :=
  if p.2=q ∧ List.Shortlex r p.1 best then p.1 else best

def pick (pairs : List (List A × Q)) (w : List A) (q : Q) : List A :=
  pairs.foldl (pickStep (r:=r) q) w

variable (wf : WellFounded r) (q : List A → Q)

theorem pick_class {ps : List (List A × Q)} {w v : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) (hv : q v=q w) : q (pick (r:=r) ps v (q w))=q w := by
  induction ps generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    simp only [pick,List.foldl_cons]
    apply ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
    simp only [pickStep]
    split
    next h => exact (hps p (List.mem_cons_self)).symm.trans h.1
    next h => exact hv

theorem pick_least_fixed {ps : List (List A × Q)} {w : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) :
    pick (r:=r) ps (least wf q w) (q w)=least wf q w := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hh : ¬ (p.2=q w ∧ List.Shortlex r p.1 (least wf q w)) := by
      rintro ⟨hq,hr⟩
      exact least_global_min wf q ((hps p List.mem_cons_self).symm.trans hq) hr
    simp only [pick,List.foldl_cons,pickStep,ite_eq_right hh]
    exact ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))

variable [Std.Trichotomous r]

/-- The finite answer list computes the same least shortlex representative as
    the manuscript, even though it tests every word in the common length ball. -/
theorem pick_eq_least {ps : List (List A × Q)} {w : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) (hm : (least wf q w,q w) ∈ ps) :
    pick (r:=r) ps w (q w)=least wf q w := by
  obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hm
  have hb : ∀ p ∈ before,p.2=q p.1 := fun p hp => hps p (List.mem_append_left _ hp)
  have ha : ∀ p ∈ after,p.2=q p.1 := fun p hp =>
    hps p (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have hclass := pick_class (r:=r) q hb (w:=w) rfl
  have hsel : pickStep (r:=r) (q w) (pick (r:=r) before w (q w)) (least wf q w,q w) = least wf q w := by
    unfold pickStep
    simp only [true_and]
    split
    · rfl
    next h =>
      apply Std.Trichotomous.trichotomous (r:=List.Shortlex r)
      · exact least_global_min wf q hclass
      · exact h
  simp only [pick,List.foldl_append,List.foldl_cons]
  change after.foldl (pickStep (r:=r) (q w))
    (pickStep (r:=r) (q w) (pick (r:=r) before w (q w)) (least wf q w,q w)) = _
  rw [hsel]
  exact pick_least_fixed wf q ha

end Canonical

namespace Search

section
variable {A : Type*} [DecidableEq A]

def lexBool (r : A → A → Bool) : List A → List A → Bool
  | [],[] => false
  | [],_::_ => true
  | _::_,[] => false
  | a::u,b::v => if a=b then lexBool r u v else r a b

theorem lexBool_eq [LinearOrder A] (u v : List A) :
    lexBool (fun a b : A => decide (a<b)) u v = decide (List.Lex (·<·) u v) := by
  induction u generalizing v with
  | nil => cases v <;> simp [lexBool]
  | cons a u ih =>
    cases v with
    | nil => simp [lexBool]
    | cons b v =>
      by_cases hab : a=b
      · subst b
        simp [lexBool,ih,List.lex_cons_iff]
      · simp only [lexBool,ite_eq_right hab]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · exact List.Lex.rel
        · intro h
          cases h with
          | rel h => exact h
          | cons h => exact False.elim (hab rfl)

def lexFoldStep (r : A → A → Bool) (st : Bool ⊕ List A) (a : A) : Bool ⊕ List A :=
  match st with
  | .inl b => .inl b
  | .inr [] => .inl false
  | .inr (b::v) => if a=b then .inr v else .inl (r a b)

def lexFinish : Bool ⊕ List A → Bool := Sum.elim id (fun v => !v.isEmpty)

theorem lexFold (r : A → A → Bool) (u : List A) (st : Bool ⊕ List A) :
    lexFinish (u.foldl (lexFoldStep r) st)=st.elim id (lexBool r u) := by
  induction u generalizing st with
  | nil => cases st with
    | inl b => rfl
    | inr v => cases v <;> rfl
  | cons a u ih =>
    rw [List.foldl_cons,ih]
    cases st with
    | inl b => rfl
    | inr v =>
      cases v with
      | nil => cases u <;> rfl
      | cons b v =>
        simp only [lexFoldStep,lexBool,Sum.elim_inr]
        split <;> rfl

variable [Primcodable A]

theorem primrec_lexBool (r : A → A → Bool) (hr : Primrec₂ r) : Primrec₂ (lexBool r) := by
  have hinr : Primrec₂ (fun (p : (Bool ⊕ List A) × A) (v : List A) =>
      match v with
      | [] => (Sum.inl false : Bool ⊕ List A)
      | b::v => if p.2=b then .inr v else .inl (r p.2 b)) := by
    exact (Primrec.list_casesOn Primrec.snd (Primrec.const (.inl false))
      (Primrec.ite
        (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
        (Primrec.sumInr.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.sumInl.comp (hr.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)))).to₂).to₂.of_eq (by intro p v; cases v <;> rfl)
  have hstep : Primrec₂ (lexFoldStep r) :=
    (Primrec.sumCasesOn Primrec.fst
      (Primrec.sumInl.comp Primrec.snd).to₂ hinr).to₂.of_eq (by
        intro st a
        cases st with
        | inl b => rfl
        | inr v => cases v <;> rfl)
  have hf : Primrec (lexFinish (A:=A)) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.snd.to₂)
      ((Primrec.not.comp (Effect.primrec_listIsEmpty.comp Primrec.snd)).to₂)).of_eq (fun p => by cases p <;> rfl)
  exact ((hf.comp (Primrec.list_foldl Primrec.fst
    (Primrec.sumInr.comp Primrec.snd) (hstep.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq (fun p => lexFold r p.1 (.inr p.2))).to₂

 theorem primrec_shortlex [LinearOrder A] (hr : PrimrecRel (fun a b : A => a<b)) :
    PrimrecRel (List.Shortlex (fun a b : A => a<b)) := by
  have hlex : PrimrecRel (List.Lex (fun a b : A => a<b)) := by
    apply PrimrecRel.of_eq
      (Primrec.eq.comp₂ (primrec_lexBool (fun a b : A => decide (a<b)) hr.decide)
        (Primrec.const true).to₂)
    intro u v
    rw [lexBool_eq,decide_eq_true_eq]
  exact ((Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)).or
    ((Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)).and hlex)).of_eq
      (fun p => List.shortlex_def.symm)

end

variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

def output (C : BlockCode A S) (z : S) (ps : List (List A × Option Q))
    (p : List A × Option Q) : List S :=
  if p.2=none then [z] else C.encode (Canonical.pick (r:=r) ps p.1 p.2)

def table (C : BlockCode A S) (z : S) (ps : List (List A × Option Q)) : List (List S × List S) :=
  ps.flatMap fun p =>
    if p.1≠[] ∧ output (r:=r) C z ps p≠C.encode p.1 then [(C.encode p.1,output (r:=r) C z ps p)] else []

noncomputable def compute [Fintype A] (C : BlockCode A S) (z : S)
    (q : List A → Part (Option Q)) (n : ℕ) : Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (q w).map (w,·)) (Static.words A n)).map (table (r:=r) C z)

theorem traverse_map {X Y : Type*} (f : X → Part Y) (g : X → Y) (l : List X)
    (h : ∀ x∈l, g x ∈ f x) : l.map g ∈ Effect.traverse f l := by
  induction l with
  | nil => exact Part.mem_some _
  | cons x xs ih =>
    exact Part.mem_bind_iff.mpr ⟨g x,h x List.mem_cons_self,
      (Part.mem_map_iff _).mpr ⟨xs.map g,ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),rfl⟩⟩

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r) (q : List A → Option Q)

omit [DecidableEq A] [DecidableEq S] in
 theorem output_full (C : BlockCode A S) (z : S) {n : ℕ} {w : List A} (hw : w.length≤n) :
    output (r:=r) C z ((Static.words A n).map fun v => (v,q v)) (w,q w) = Static.output C wf q z w := by
  have hps : ∀ p∈(Static.words A n).map (fun v => (v,q v)),p.2=q p.1 := by
    intro p hp
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    rfl
  have hm : (Canonical.least wf q w,q w)∈(Static.words A n).map (fun v => (v,q v)) :=
    List.mem_map.mpr ⟨Canonical.least wf q w,(Static.mem_words _ _).mpr
      ((Canonical.least_length wf q w).trans hw),by simp [Canonical.least_class]⟩
  simp only [output,Static.output,Canonical.pick_eq_least wf q hps hm]

omit [DecidableEq A] in
 theorem table_full (C : BlockCode A S) (z : S) (n : ℕ) :
    table (r:=r) C z ((Static.words A n).map fun v => (v,q v))=Static.table C wf q z n := by
  unfold table Static.table
  rw [List.flatMap_map]
  have hh : ∀ w∈Static.words A n,
      (if w≠[] ∧ output (r:=r) C z ((Static.words A n).map fun v => (v,q v)) (w,q w)≠C.encode w
        then [(C.encode w,output (r:=r) C z ((Static.words A n).map fun v => (v,q v)) (w,q w))] else []) =
      (if w≠[] ∧ Static.output C wf q z w≠C.encode w
        then [(C.encode w,Static.output C wf q z w)] else []) := by
    intro w hw
    rw [output_full wf q C z ((Static.mem_words _ _).mp hw)]
  rw [List.flatMap_congr hh]
  have he (l : List (List A)) :
      l.flatMap (fun w => if w≠[] ∧ Static.output C wf q z w≠C.encode w
        then [(C.encode w,Static.output C wf q z w)] else []) =
      (l.filter fun w => w≠[] ∧ Static.output C wf q z w≠C.encode w).map
        (fun w => (C.encode w,Static.output C wf q z w)) := by
    induction l with
    | nil => rfl
    | cons w l ih =>
      by_cases hh : w≠[] ∧ Static.output C wf q z w≠C.encode w
      · simp only [List.flatMap_cons,List.filter_cons,decide_eq_true_eq,ite_eq_left hh,List.map_cons,List.singleton_append,ih]
      · simp only [List.flatMap_cons,List.filter_cons,decide_eq_true_eq,ite_eq_right hh,List.nil_append,ih]
  exact he _

omit [DecidableEq A] in
 theorem compute_full (C : BlockCode A S) (z : S) {f : List A → Part (Option Q)} {n : ℕ}
    (h : ∀ w,w.length≤n → q w ∈ f w) :
    Static.table C wf q z n ∈ compute (r:=r) C z f n := by
  apply (Part.mem_map_iff _).mpr
  refine ⟨(Static.words A n).map (fun w => (w,q w)),?_,table_full wf q C z n⟩
  apply traverse_map
  intro w hw
  exact (Part.mem_map_iff _).mpr ⟨q w,h w ((Static.mem_words _ _).mp hw),rfl⟩

variable [Primcodable A] [Primcodable S] [Primcodable Q]
omit [Std.Trichotomous r]

omit [DecidableEq A] [DecidableEq S] in
 theorem primrec_encode (C : BlockCode A S) : Primrec C.encode :=
  Primrec.list_flatMap Primrec.id ((Primrec.dom_finite C.block).comp Primrec.snd).to₂

omit [DecidableEq A] in
 theorem primrec_words : Primrec (Static.words A) := by
  exact (Primrec.nat_rec₁ [[]]
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap (Primrec.const (Static.letters A))
        (Primrec.list_map (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
    fun n => by induction n <;> simp_all [Static.words]

omit [DecidableEq A] [Fintype A] in
 theorem primrec_pickStep (hr : PrimrecRel (List.Shortlex r))
    {X : Type*} [Primcodable X] {v : X → Option Q} {b : X → List A} {p : X → List A × Option Q}
    (hv : Primrec v) (hb : Primrec b) (hp : Primrec p) :
    Primrec (fun x => Canonical.pickStep (r:=r) (v x) (b x) (p x)) :=
  Primrec.ite ((Primrec.eq.comp (Primrec.snd.comp hp) hv).and
    (hr.comp (Primrec.fst.comp hp) hb)) (Primrec.fst.comp hp) hb

omit [DecidableEq A] [Fintype A] in
 theorem primrec_pick (hr : PrimrecRel (List.Shortlex r))
    {X : Type*} [Primcodable X]
    {ps : X → List (List A × Option Q)} {v : X → List A} {q : X → Option Q}
    (hp : Primrec ps) (hv : Primrec v) (hq : Primrec q) :
    Primrec (fun x => Canonical.pick (r:=r) (ps x) (v x) (q x)) :=
  Primrec.list_foldl hp hv (primrec_pickStep (Q:=Q) hr
    (hq.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

omit [DecidableEq A] [DecidableEq S] in
 theorem primrec_output (C : BlockCode A S) (z : S) (hr : PrimrecRel (List.Shortlex r)) :
    Primrec₂ (output (Q:=Q) (r:=r) C z) := by
  exact (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const none))
    (Primrec.const [z])
    ((primrec_encode C).comp (primrec_pick (Q:=Q) hr Primrec.fst
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).to₂

omit [DecidableEq A] in
 theorem primrec_table (C : BlockCode A S) (z : S) (hr : PrimrecRel (List.Shortlex r)) :
    Primrec (table (Q:=Q) (r:=r) C z) := by
  apply Primrec.list_flatMap Primrec.id
  change Primrec (fun p : List (List A × Option Q) × (List A × Option Q) =>
    if p.2.1≠[] ∧ output (r:=r) C z p.1 p.2≠C.encode p.2.1
      then [(C.encode p.2.1,output (r:=r) C z p.1 p.2)] else [])
  have hout : Primrec (fun p : List (List A × Option Q) × (List A × Option Q) =>
      output (r:=r) C z p.1 p.2) := primrec_output (Q:=Q) C z hr
  have hcode : Primrec (fun p : List (List A × Option Q) × (List A × Option Q) =>
      C.encode p.2.1) := (primrec_encode C).comp (Primrec.fst.comp Primrec.snd)
  exact Primrec.ite
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])).not.and
      (Primrec.eq.comp hout hcode).not)
    (Primrec.list_cons.comp (hcode.pair hout) (Primrec.const [])) (Primrec.const [])

omit [DecidableEq A] in
 theorem partrec_compute (C : BlockCode A S) (z : S) (hr : PrimrecRel (List.Shortlex r))
    {f : List A → Part (Option Q)} (hf : Partrec f) : Partrec (compute (r:=r) C z f) := by
  have hh : Partrec (fun w => (f w).map (w,·)) :=
    hf.map (Computable.fst.pair Computable.snd).to₂
  exact (((Effect.partrec_traverse hh).comp primrec_words.to_comp).map
    ((primrec_table (Q:=Q) C z hr).to_comp.comp Computable.snd).to₂)

end Search
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Selectors

section
variable {S : Type*} [DecidableEq S] [Primcodable S]

def maxLength (ws : List (List S)) : ℕ := (ws.map List.length).foldr max 0

omit [DecidableEq S] [Primcodable S] in
theorem length_le_maxLength {ws : List (List S)} {w : List S} (hw : w∈ws) : w.length ≤ maxLength ws := by
  induction ws with
  | nil => simp at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact le_max_left _ _
    · exact (ih hw).trans (le_max_right _ _)

def tuples (z : S) (i : ℕ) : List (List S) :=
  let ws := (Encodable.decode (α:=List (List S)) i).getD [[]]
  if ws≠[] ∧ ws.Nodup ∧ (∀ w∈ws,z∉w) then ws else [[]]

theorem tuples_valid (z : S) (i : ℕ) :
    tuples z i≠[] ∧ (tuples z i).Nodup ∧ ∀ w∈tuples z i,z∉w := by
  unfold tuples
  dsimp only
  split
  · assumption
  · simp

 theorem tuples_complete (z : S) {ws : List (List S)}
    (hne : ws≠[]) (hd : ws.Nodup) (hz : ∀ w∈ws,z∉w) : tuples z (Encodable.encode ws)=ws := by
  simp only [tuples,Encodable.encodek,Option.getD_some]
  exact ite_eq_left ⟨hne,hd,hz⟩

/-- Each new size is past the entire preceding potential envelope, not merely
    past those actually selected. The index and current body bounds are included. -/
def sizes (z : S) : ℕ → ℕ
  | 0 => maxLength (tuples z 0)+1
  | i+1 => max (max (i+2) (maxLength (tuples z (i+1))+1))
      (2 * sizes z i+3+maxLength (tuples z i))

def stages (z : S) (i : ℕ) : Stage S := ⟨sizes z i,tuples z i⟩

theorem index_lt_size (z : S) (i : ℕ) : i < sizes z i := by
  cases i with
  | zero => simp [sizes]
  | succ i =>
    have h : i+2 ≤ sizes z (i+1) := (le_max_left _ _).trans (le_max_left _ _)
    omega

 theorem body_lt_size (z : S) (i : ℕ) {w : List S} (hw : w∈tuples z i) : w.length < sizes z i := by
  have hh := length_le_maxLength hw
  cases i with
  | zero => simp only [sizes]; omega
  | succ i =>
    have h : maxLength (tuples z (i+1))+1 ≤ sizes z (i+1) := (le_max_right _ _).trans (le_max_left _ _)
    omega

 theorem sizes_step (z : S) (i : ℕ) : 2*sizes z i+2+maxLength (tuples z i) < sizes z (i+1) := by
  have : 2*sizes z i+3+maxLength (tuples z i) ≤ sizes z (i+1) := le_max_right _ _
  omega

 theorem sizes_strictMono (z : S) : StrictMono (sizes z) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have := sizes_step z i
  omega

 theorem stage_spacing (a : Markers S) {i j : ℕ} (hij : i < j) {w : List S}
    (hw : w∈(stages a.zero i).bodies) :
    (a.wrap (stages a.zero i).size w).length < (stages a.zero j).size := by
  have hw' := length_le_maxLength hw
  have hs := sizes_step a.zero i
  have hj := (sizes_strictMono a.zero).monotone (Nat.succ_le_of_lt hij)
  change sizes a.zero (i+1) ≤ sizes a.zero j at hj
  simp only [Markers.wrap,Envelopes.length_frame,stages]
  change w.length ≤ maxLength (tuples a.zero i) at hw'
  omega

 theorem primrec_mem {X : Type*} [Primcodable X] : PrimrecRel (fun (x : X) (l : List X) => x∈l) :=
  (PrimrecRel.of_eq Primrec.eq.exists_mem_list (by intro l x; simp)).swap

 theorem primrec_dedup {X : Type*} [Primcodable X] [DecidableEq X] : Primrec (@List.dedup X _) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite
      (primrec_mem.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂).of_eq
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [id_eq] at ih ⊢
    simp only [List.foldr_cons,ih,List.dedup_cons']

 theorem primrec_nodup {X : Type*} [Primcodable X] [DecidableEq X] : PrimrecPred (@List.Nodup X) :=
  (Primrec.eq.comp primrec_dedup Primrec.id).of_eq (fun _ => List.dedup_eq_self)

omit [DecidableEq S] in
 theorem primrec_maxLength : Primrec (@maxLength S) :=
  (Primrec.list_foldr (Primrec.list_map Primrec.id (Primrec.list_length.comp Primrec.snd).to₂)
    (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

 theorem primrec_tuples (z : S) : Primrec (tuples z) := by
  have hc : Primrec (fun i => (Encodable.decode (α:=List (List S)) i).getD [[]]) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [[]])
  have hz : PrimrecPred (fun ws : List (List S) => ∀ w∈ws,z∉w) :=
    ((primrec_mem.comp (Primrec.const z) Primrec.id).not).forall_mem_list
  exact Primrec.ite ((Primrec.eq.comp hc (Primrec.const [])).not.and
    ((primrec_nodup.comp hc).and (hz.comp hc))) hc (Primrec.const [[]])

 theorem primrec_sizes (z : S) : Primrec (sizes z) := by
  have hm := primrec_maxLength.comp (primrec_tuples z)
  have hs : Primrec₂ (fun i v => max (max (i+2) (maxLength (tuples z (i+1))+1))
      (2*v+3+maxLength (tuples z i))) := by
    exact (Primrec.nat_max.comp
      (Primrec.nat_max.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
        (Primrec.succ.comp (hm.comp (Primrec.succ.comp Primrec.fst))))
      (Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 3))
        (hm.comp Primrec.fst))).to₂
  exact (Primrec.nat_rec₁ (maxLength (tuples z 0)+1) hs).of_eq (by
    intro i
    induction i <;> simp_all [sizes])

end

variable {S : Type*} [DecidableEq S] [Primcodable S]

def stageEquiv : Stage S ≃ ℕ × List (List S) where
  toFun s := (s.size,s.bodies)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable (Stage S) := Primcodable.ofEquiv _ stageEquiv

omit [DecidableEq S] in
theorem primrec_stage_size : Primrec (@Stage.size S) := Primrec.fst.comp Primrec.of_equiv

omit [DecidableEq S] in
theorem primrec_stage_bodies : Primrec (@Stage.bodies S) := Primrec.snd.comp Primrec.of_equiv

theorem primrec_stages (z : S) : Primrec (stages z) :=
  Primrec.of_equiv_symm.comp ((primrec_sizes z).pair (primrec_tuples z))

omit [DecidableEq S] in
theorem primrec_replicate (b : S) : Primrec (fun n => List.replicate n b) :=
  (Primrec.nat_rec₁ [] (Primrec.list_cons.comp (Primrec.const b) Primrec.snd).to₂).of_eq
    (by intro n; induction n <;> simp_all [List.replicate_succ])

omit [DecidableEq S] in
theorem primrec_wrap (a : Markers S) : Primrec₂ a.wrap := by
  exact (Primrec.list_cons.comp (Primrec.const a.d)
    (Primrec.list_append.comp (Primrec.list_append.comp
      (Primrec.list_append.comp ((primrec_replicate a.l).comp Primrec.fst) Primrec.snd)
      ((primrec_replicate a.r).comp Primrec.fst)) (Primrec.const [a.h]))).to₂

theorem primrec_rules (a : Markers S) : Primrec₂ (rules a) := by
  exact (Primrec.list_map Primrec.snd
    ((primrec_wrap a).comp (Primrec.fst.comp Primrec.fst) Primrec.snd |>.pair
      (Primrec.ite (Primrec.eq.comp
        (Primrec.list_head?.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp Primrec.snd)) (Primrec.const []) (Primrec.const [a.zero]))).to₂).to₂

theorem primrec_allowed : PrimrecRel (fun (rs : List (List S × List S)) s => allowed rs s = true) := by
  have hh : PrimrecRel (fun (w : List S) (rs : List (List S × List S)) => next rs w = none) :=
    (Primrec.eq.comp (primrec_next.comp Primrec.snd Primrec.fst) (Primrec.const none)).primrecRel
  exact (hh.forall_mem_list.comp (primrec_stage_bodies.comp Primrec.snd) Primrec.fst).of_eq
    (by intro p; simp [allowed,List.all_eq_true,Option.isNone_iff_eq_none])

theorem primrec_choose (a : Markers S) {X : Type*} [Primcodable X]
    {rs : X → List (List S × List S)} {s : X → Stage S} {n : X → ℕ}
    (hr : Primrec rs) (hs : Primrec s) (hn : Primrec n) :
    Primrec (fun x => choose (a:=a) (rs x) (s x) (n x)) :=
  Primrec.ite
    ((Primrec.nat_le.comp (primrec_stage_size.comp hs) hn).and (primrec_allowed.comp hr hs))
    (Primrec.list_append.comp hr ((primrec_rules a).comp
      (primrec_stage_size.comp hs) (primrec_stage_bodies.comp hs))) hr

theorem primrec_process (a : Markers S) (ss : ℕ → Stage S) (hss : Primrec ss) :
    Primrec₂ (fun p : List (List S × List S) × ℕ => process (a:=a) p.1 ss p.2) := by
  apply Primrec₂.of_eq (Primrec.nat_rec Primrec.fst
    (primrec_choose a (Primrec.snd.comp Primrec.snd)
      (hss.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst)).to₂)
  intro p j
  induction j with
  | zero => rfl
  | succ j ih => simp only [process,ih]

theorem primrec_full_process (a : Markers S) {base : ℕ → List (List S × List S)}
    (hb : Primrec base) : Primrec (fun n => process (a:=a) (base n) (stages a.zero) n n) :=
  (primrec_process a _ (primrec_stages _)).comp (hb.pair Primrec.id) Primrec.id

end FiniteAlgebraicEnvelopes.Bootstrap.Selectors

end OAI
