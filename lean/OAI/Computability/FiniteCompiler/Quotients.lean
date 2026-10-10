import OAI.Computability.FiniteCompiler.Selectors
import OAI.Computability.FiniteCompiler.Effectivity
import OAI.GroupTheory.BooneHigman.Basic
import OAI.GroupTheory.BooneHigman.WordProblem

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
open Relation
namespace BlockCode
variable {A B S : Type*} (C : BlockCode A S)

def Alphabet : Set S := {s | ∃ a, s ∈ C.block a}

theorem mem_alphabet {w : List A} {s : S} (h : s ∈ C.encode w) : s ∈ C.Alphabet := by
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp h
  exact ⟨a,ha⟩

theorem encode_ne_nil {w : List A} (h : w ≠ []) : C.encode w ≠ [] := by
  intro he
  exact h (C.encode_injective (he.trans C.encode_nil.symm))

theorem disjoint_infix (D : BlockCode B S) (hd : Disjoint C.Alphabet D.Alphabet)
    {w : List A} {v : List B} (hv : v ≠ []) (hi : D.encode v <:+: C.encode w) : False := by
  obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ (D.encode_ne_nil hv)
  exact Set.disjoint_left.mp hd (C.mem_alphabet (hi.subset hs)) (D.mem_alphabet hs)

theorem disjoint_overlap (D : BlockCode B S) (hd : Disjoint C.Alphabet D.Alphabet)
    {u : List A} {v : List B} {p m q : List S} (hm : m ≠ [])
    (hu : C.encode u=p++m) (hv : D.encode v=m++q) : False := by
  obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hm
  exact Set.disjoint_left.mp hd (C.mem_alphabet (hu ▸ List.mem_append_right p hs))
    (D.mem_alphabet (hv ▸ List.mem_append_left q hs))
end BlockCode

namespace Static
variable {S A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_support {n : ℕ} {p : List S × List S} (hp : p ∈ table C wf q z n) :
    p.1 ≠ [] ∧ ∀ s ∈ p.1,s ∈ C.Alphabet := by
  rcases p with ⟨u,v⟩
  obtain ⟨w,_,hn,_,rfl,rfl⟩ := (mem_table C wf q z).mp hp
  exact ⟨C.encode_ne_nil hn,fun _ hs => C.mem_alphabet hs⟩

omit [DecidableEq A] [DecidableEq Q] in
theorem table_decrease {s : S → S → Prop} (hwidth : 1<C.width+1)
    (hc : ∀ a b, r a b → List.Lex s (C.block a) (C.block b)) (n : ℕ) :
    ∀ p ∈ table C wf q z n,List.Shortlex s p.2 p.1 := by
  intro ⟨u,v⟩ hp
  obtain ⟨w,_,hn,he,rfl,rfl⟩ := (mem_table C wf q z).mp hp
  unfold output
  split
  · apply List.Shortlex.of_length_lt
    simp only [List.length_singleton,C.encode_length]
    have hw : 1 ≤ w.length := by have := List.length_pos_iff.mpr hn; omega
    nlinarith
  · obtain h | h := Canonical.least_lt_or_eq wf q w
    · exact C.encode_shortlex hc h
    · exact False.elim (he (by simp_all [output]))

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_bounded {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C wf q z (k/(C.width+1))) (table C wf q z (n/(C.width+1))) k := by
  intro ⟨u,v⟩ hu
  simp only [mem_table]
  constructor
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    exact ⟨w,hw.trans (Nat.div_le_div_right hkn),hn,he,rfl,rfl⟩
  · rintro ⟨w,hw,hn,he,rfl,rfl⟩
    refine ⟨w,?_,hn,he,rfl,rfl⟩
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr
    simpa only [C.encode_length,Nat.mul_comm] using hu

omit [DecidableEq A] [DecidableEq Q] in
theorem critical_containment_bound {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C wf q z (n/(C.width+1)), p ∈ rs)
    (hc : Contextual q (n/(C.width+1))) (hi : ZeroIdeal q (n/(C.width+1)))
    {u u' v v' x y : List S}
    (hu : (u,u') ∈ table C wf q z (n/(C.width+1)))
    (hv : (v,v') ∈ table C wf q z (n/(C.width+1)))
    (he : u=x++v++y) (hlen : u.length ≤ n) : Join (Steps rs) u' (x++v'++y) := by
  apply critical_containment C wf q z hzero hz ht hc hi hu hv he
  obtain ⟨w,hw,_,_,rfl,_⟩ := (mem_table C wf q z).mp hu
  simpa only [C.encode_length] using Nat.mul_le_mul_left (C.width+1) hw

omit [DecidableEq A] [DecidableEq Q] in
theorem critical_overlap_bound {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C wf q z (n/(C.width+1)), p ∈ rs)
    (hc : Contextual q (n/(C.width+1))) (hi : ZeroIdeal q (n/(C.width+1)))
    {u u' v v' p m t : List S}
    (hu : (u,u') ∈ table C wf q z (n/(C.width+1)))
    (hv : (v,v') ∈ table C wf q z (n/(C.width+1)))
    (hm : m ≠ []) (he : u=p++m) (hf : v=m++t) (hlen : (p++m++t).length ≤ n) :
    Join (Steps rs) (u'++t) (p++v') := by
  apply critical_overlap C wf q z hzero hz ht hc hi hu hv hm he hf
  obtain ⟨a,_,_,_,rfl,_⟩ := (mem_table C wf q z).mp hu
  obtain ⟨b,_,_,_,rfl,_⟩ := (mem_table C wf q z).mp hv
  obtain ⟨c,d,e,rfl,rfl,rfl,rfl,rfl⟩ := C.overlap_decode hm he hf
  have hh : (C.width+1)*(c++d++e).length ≤ n := by
    simpa only [← C.encode_append,C.encode_length] using hlen
  have hdiv : (c++d++e).length ≤ n/(C.width+1) :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa [Nat.mul_comm] using hh)
  simpa only [← C.encode_append,C.encode_length] using Nat.mul_le_mul_left (C.width+1) hdiv
end Static

namespace Base
variable {S A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (f : List A → Option Q) (g : List B → Option R) (z : S)

noncomputable def absorption : List (List S × List S) :=
  (Static.letters S).flatMap fun a => [([z,a],[z]),([a,z],[z])]

omit [DecidableEq S] in
@[simp] theorem mem_absorption {u v : List S} : (u,v) ∈ absorption z ↔
    ∃ a, (u=[z,a] ∨ u=[a,z]) ∧ v=[z] := by
  simp only [absorption,Static.letters,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,
    List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  aesop

noncomputable def table (n : ℕ) : List (List S × List S) :=
  absorption z ++ Static.table C wf f z (n/(C.width+1)) ++ Static.table D wg g z (n/(D.width+1))

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem mem_table {n : ℕ} {p : List S × List S} : p ∈ table C D wf wg f g z n ↔
    p ∈ absorption z ∨ p ∈ Static.table C wf f z (n/(C.width+1)) ∨
      p ∈ Static.table D wg g z (n/(D.width+1)) := by
  simp only [table,List.mem_append,or_assoc]

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem absorbs (n : ℕ) : Absorbs (table C D wf wg f g z n) z := by
  intro a
  constructor <;> apply (mem_table C D wf wg f g z).mpr <;> apply Or.inl <;>
    apply (mem_absorption z).mpr
  · exact ⟨a,Or.inl rfl,rfl⟩
  · exact ⟨a,Or.inr rfl,rfl⟩

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem preserves_zero (hC : z ∉ C.Alphabet) (hD : z ∉ D.Alphabet) (n : ℕ) :
    ∀ p ∈ table C D wf wg f g z n, z ∈ p.1 → z ∈ p.2 := by
  intro ⟨u,v⟩ hp hu
  rcases (mem_table C D wf wg f g z).mp hp with hp | hp | hp
  · obtain ⟨a,_,rfl⟩ := (mem_absorption z).mp hp
    simp
  · exact False.elim (hC ((Static.table_support C wf f z hp).2 z hu))
  · exact False.elim (hD ((Static.table_support D wg g z hp).2 z hu))

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R] in
/-- All static and absorption critical pairs for the literal two-code base table. -/
theorem critical (hC : z ∉ C.Alphabet) (hD : z ∉ D.Alphabet)
    (hdis : Disjoint C.Alphabet D.Alphabet) {n : ℕ}
    (hf : f [] ≠ none) (hg : g [] ≠ none)
    (hfc : Static.Contextual f (n/(C.width+1))) (hfi : Static.ZeroIdeal f (n/(C.width+1)))
    (hgc : Static.Contextual g (n/(D.width+1))) (hgi : Static.ZeroIdeal g (n/(D.width+1))) :
    Critical (table C D wf wg f g z n) n := by
  let rs := table C D wf wg f g z n
  have hz : Absorbs rs z := absorbs C D wf wg f g z n
  have hp := preserves_zero C D wf wg f g z hC hD n
  have hCt : ∀ p ∈ Static.table C wf f z (n/(C.width+1)),p ∈ rs :=
    fun _ h => (mem_table C D wf wg f g z).mpr (.inr (.inl h))
  have hDt : ∀ p ∈ Static.table D wg g z (n/(D.width+1)),p ∈ rs :=
    fun _ h => (mem_table C D wf wg f g z).mpr (.inr (.inr h))
  have hzero {w u v : List S} (hw : z ∈ w) (hu : Step rs w u) (hv : Step rs w v) :
      Join (Steps rs) u v :=
    ⟨[z],absorbs_mem hz (step_preserves_letter hp hw hu),
      absorbs_mem hz (step_preserves_letter hp hw hv)⟩
  have hnabs {u v : List S} (h : z ∉ u) : (u,v) ∉ absorption z := by
    rintro hh
    obtain ⟨a,ha,_⟩ := (mem_absorption z).mp hh
    rcases ha with rfl | rfl <;> simp at h
  constructor
  · intro u u' v v' hu hv x y he hlen
    by_cases huz : z ∈ u
    · apply hzero huz
      · simpa using Step.apply hu [] []
      · simpa only [he] using Step.apply hv x y
    have hvz : z ∉ v := fun hh => huz (by simp [he,hh])
    have hu' := (mem_table C D wf wg f g z).mp hu
    have hv' := (mem_table C D wf wg f g z).mp hv
    simp only [hnabs huz,hnabs hvz,false_or] at hu' hv'
    rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact Static.critical_containment_bound C wf f z hf hz hCt hfc hfi hu' hv' he hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hu'
      obtain ⟨b,_,hb,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hv'
      exact False.elim (C.disjoint_infix D hdis hb ⟨x,y,he.symm⟩)
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hu'
      obtain ⟨b,_,hb,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hv'
      exact False.elim (D.disjoint_infix C hdis.symm hb ⟨x,y,he.symm⟩)
    · exact Static.critical_containment_bound D wg g z hg hz hDt hgc hgi hu' hv' he hlen
  · intro u u' v v' hu hv p m t hm he hh hlen
    by_cases hwz : z ∈ p++m++t
    · apply hzero hwz
      · simpa only [he,List.nil_append,List.append_assoc] using Step.apply hu [] t
      · simpa only [hh,List.append_nil,List.append_assoc] using Step.apply hv p []
    have huz : z ∉ u := fun h => hwz (by simp [←he,h])
    have hvz : z ∉ v := fun h => hwz (by simpa only [List.append_assoc,←hh,List.mem_append] using Or.inr h)
    have hu' := (mem_table C D wf wg f g z).mp hu
    have hv' := (mem_table C D wf wg f g z).mp hv
    simp only [hnabs huz,hnabs hvz,false_or] at hu' hv'
    rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
    · exact Static.critical_overlap_bound C wf f z hf hz hCt hfc hfi hu' hv' hm he hh hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hu'
      obtain ⟨b,_,_,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hv'
      exact False.elim (C.disjoint_overlap D hdis hm he hh)
    · obtain ⟨a,_,_,_,rfl,_⟩ := (Static.mem_table D wg g z).mp hu'
      obtain ⟨b,_,_,_,rfl,_⟩ := (Static.mem_table C wf f z).mp hv'
      exact False.elim (D.disjoint_overlap C hdis.symm hm he hh)
    · exact Static.critical_overlap_bound D wg g z hg hz hDt hgc hgi hu' hv' hm he hh hlen

end Base

open Relation
variable {S : Type*} [DecidableEq S] {r : S → S → Prop}

omit [DecidableEq S] in
theorem steps_bounded {rs rt : List (List S × List S)} {k : ℕ}
    (hh : Selectors.BoundedEq rs rt k)
    (hd : ∀ p ∈ rs,List.Shortlex r p.2 p.1) {u v : List S} (hu : u.length ≤ k)
    (h : Steps rs u v) : Steps rt u v := by
  induction h with
  | refl => exact .refl
  | tail h hs ih => exact ih.tail ((step_stable hh ((steps_length hd h).trans hu)).mp hs)

/-- The actual partial table-first procedure used at the fixed point. -/
def tableNormal (T : ℕ → Part (List (List S × List S))) (w : List S) : Part (List S) :=
  (T w.length).bind (fun rs => evaluate rs w)

/-- A successful table has all the finite mathematical certificates needed by
    the bounded Newman argument. No totality of the program is part of this. -/
def GoodTable (T : ℕ → Part (List (List S × List S))) (n : ℕ) : Prop :=
  ∃ rs ∈ T n, (∀ p ∈ rs,List.Shortlex r p.2 p.1) ∧ Critical rs n

theorem tableNormal_at {T : ℕ → Part (List (List S × List S))} {n : ℕ}
    (wf : WellFounded r) (ht : ∀ k ≤ n,GoodTable (r:=r) T k)
    (hs : ∀ k ≤ n,∀ rk ∈ T k,∀ rn ∈ T n,Selectors.BoundedEq rk rn k)
    {rn : List (List S × List S)} (hrn : rn ∈ T n) {w : List S} (hw : w.length ≤ n) :
    tableNormal T w=evaluate rn w := by
  obtain ⟨rk,hrk,hdk,hck⟩ := ht w.length hw
  obtain ⟨rt,hrt,hdt,hct⟩ := ht n le_rfl
  have he := Part.mem_unique hrt hrn
  subst rt
  obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf hdk) w)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf hdt) w)
  obtain ⟨hwu,huI⟩ := evaluate_sound hu
  obtain ⟨hwv,hvI⟩ := evaluate_sound hv
  have hstab := hs w.length hw rk hrk rn hrn
  have hwu' := steps_bounded hstab hdk le_rfl hwu
  have huI' := (Selectors.irreducible_bounded hstab (steps_length hdk hwu)).mp huI
  have huv := evaluate_unique_on wf hdt n (fun _ _ _ h => critical_localJoin hct h)
    hw hwu' hwv huI' hvI
  subst v
  rw [tableNormal,Part.eq_some_iff.mpr hrk,Part.bind_some]
  exact (Part.eq_some_iff.mpr hu).trans (Part.eq_some_iff.mpr hv).symm

/-- This is the whole contextual-induction step, including the table at the
    shortened contextual endpoint and irreducibility in the larger table. -/
theorem tableNormal_budget {T : ℕ → Part (List (List S × List S))} {n : ℕ}
    (wf : WellFounded r) (ht : ∀ k ≤ n,GoodTable (r:=r) T k)
    (hs : ∀ k m, k ≤ m → m ≤ n → ∀ rk ∈ T k,∀ rm ∈ T m,Selectors.BoundedEq rk rm k) :
    Compiler.PartialBudget (tableNormal T) n := by
  have htotal (w : List S) (hw : w.length ≤ n) : (tableNormal T w).Dom := by
    obtain ⟨rs,hrs,hd,hc⟩ := ht w.length hw
    rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some]
    exact evaluate_total (steps_wellFounded wf hd) w
  have hlen (w : List S) (hw : w.length ≤ n) (out : List S) (ho : out ∈ tableNormal T w) :
      out.length ≤ w.length := by
    obtain ⟨rs,hrs,hd,hc⟩ := ht w.length hw
    rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at ho
    exact steps_length hd (evaluate_sound ho).1
  refine ⟨htotal,hlen,?_⟩
  intro x w y hlenxy out hout
  obtain ⟨rs,hrs,hd,hc⟩ := ht n le_rfl
  have hw : w.length ≤ n := by simp only [List.length_append] at hlenxy; omega
  have hlenout := hlen w hw out hout
  have hshort : (x++out++y).length ≤ n := by simp only [List.length_append] at hlenxy ⊢; omega
  have heq (v : List S) (hv : v.length ≤ n) : tableNormal T v = evaluate rs v :=
    tableNormal_at wf ht (fun k hk => hs k n hk le_rfl) hrs hv
  have ehw := heq w hw
  rw [ehw] at hout
  rw [heq _ hshort,heq _ hlenxy]
  exact evaluate_context_on wf hd n (fun _ _ _ h => critical_localJoin hc h) hout x y hlenxy

/-- The source's simultaneous length induction, for the table builder actually
    fed to the recursion theorem.  `build` only receives strictly smaller budgets.
    Thus this lemma never assumes the desired total/contextual program outright. -/
theorem bootstrap_length_induction (wf : WellFounded r)
    (T : ℕ → Part (List (List S × List S))) (f : List S → Part (List S))
    (fixed : f=tableNormal T)
    (stable : ∀ k n, k ≤ n → ∀ rk ∈ T k,∀ rn ∈ T n,Selectors.BoundedEq rk rn k)
    (build : ∀ n, (∀ m<n,Compiler.PartialBudget f m) → GoodTable (r:=r) T n) :
    ∀ n, GoodTable (r:=r) T n ∧ Compiler.PartialBudget f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := build n (fun m hm => (ih m hm).2)
    refine ⟨hn,?_⟩
    rw [fixed]
    apply tableNormal_budget wf
    · intro k hk
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact (ih k hk).1
      · exact hn
    · intro k m hkm _
      exact stable k m hkm

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*}

theorem traverse_comp (f : A → Part B) (g : X → A) (l : List X) :
    traverse (fun x => f (g x)) l=traverse f (l.map g) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [traverse,List.map_cons,ih]

theorem traverse_domain {f : A → Part B} {l : List A} (h : (traverse f l).Dom) :
    ∀ a∈l,(f a).Dom := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨out,ho⟩ := Part.dom_iff_mem.mp h
    obtain ⟨b,hb,ht⟩ := Part.mem_bind_iff.mp ho
    obtain ⟨bs,hbs,_⟩ := (Part.mem_map_iff _).mp ht
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb.1
    · exact ih hbs.1 x hx

theorem partrec_traverse_parameter [Primcodable X] [Primcodable A] [Primcodable B]
    {f : X → A → Part B} (hf : Partrec₂ f) : Partrec₂ (fun x => traverse (f x)) := by
  have hp : Primrec (fun p : X × List A => p.2.map (p.1,·)) :=
    Primrec.list_map Primrec.snd ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂
  exact ((partrec_traverse hf).comp hp.to_comp).of_eq (by
    intro p
    exact (traverse_comp (Function.uncurry f) (p.1,·) p.2).symm)
end Effect

namespace Bootstrap
namespace Search
variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

noncomputable def value (f : List A → Part (Option Q)) (w : List A) : Option Q := by
  classical
  exact if h : (f w).Dom then (f w).get h else none

omit [DecidableEq A] [DecidableEq S] [DecidableEq Q] [DecidableRel (List.Shortlex r)] in
theorem value_mem {f : List A → Part (Option Q)} {w : List A} (h : (f w).Dom) : value f w ∈ f w := by
  simp only [value,dite_eq_left h]
  exact Part.get_mem h

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r)

omit [DecidableEq A] [Std.Trichotomous r] in
theorem compute_domain (C : BlockCode A S) (z : S) {f : List A → Part (Option Q)} {n : ℕ}
    (hc : (compute (r:=r) C z f n).Dom) : ∀ w,w.length ≤ n → (f w).Dom := by
  obtain ⟨rs,hrs⟩ := Part.dom_iff_mem.mp hc
  obtain ⟨ps,hps,_⟩ := (Part.mem_map_iff _).mp hrs
  have ht := Effect.traverse_domain hps.1
  intro w hw
  have hww := ht w ((Static.mem_words _ _).mpr hw)
  obtain ⟨p,hp⟩ := Part.dom_iff_mem.mp hww
  obtain ⟨v,hv,_⟩ := (Part.mem_map_iff _).mp hp
  exact hv.1

omit [DecidableEq A] in
theorem compute_eq (C : BlockCode A S) (z : S) {f : List A → Part (Option Q)} {n : ℕ}
    {rs : List (List S × List S)} (hc : rs ∈ compute (r:=r) C z f n) :
    rs=Static.table C wf (value f) z n := by
  exact Part.mem_unique hc (compute_full wf (value f) C z
    (fun w hw => value_mem (compute_domain C z hc.1 w hw)))

omit [DecidableEq A] [Std.Trichotomous r] in
theorem partrec_compute_parameter {X : Type*} [Primcodable X]
    [Primcodable A] [Primcodable S] [Primcodable Q]
    (C : BlockCode A S) (z : S) (hr : PrimrecRel (List.Shortlex r))
    {f : X → List A → Part (Option Q)} (hf : Partrec₂ f) :
    Partrec₂ (fun x => compute (r:=r) C z (f x)) := by
  have hp : Partrec₂ (fun x w => (f x w).map (w,·)) :=
    (hf.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂
  exact (((Effect.partrec_traverse_parameter hp).comp Computable.fst
    (primrec_words.to_comp.comp Computable.snd)).map
      ((primrec_table (Q:=Q) C z hr).to_comp.comp Computable.snd).to₂).to₂
end Search

namespace Build
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)

noncomputable def bases (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (Search.compute (r:=r) C a.zero f (n/(C.width+1))).bind fun rc =>
    (Search.compute (r:=s) D a.zero g (n/(D.width+1))).map fun rd => Base.absorption a.zero ++ rc ++ rd

noncomputable def tables (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (n : ℕ) :
    Part (List (List S × List S)) :=
  (bases (r:=r) (s:=s) a C D f g n).map fun b =>
    Selectors.process (a:=a) b (Selectors.stages a.zero) n n

variable [Std.Trichotomous r] [Std.Trichotomous s] (wf : WellFounded r) (wg : WellFounded s)

omit [Primcodable S] [DecidableEq A] [DecidableEq B] in
theorem bases_eq {f : List A → Part (Option Q)} {g : List B → Part (Option R)}
    {n : ℕ} {rs : List (List S × List S)} (h : rs ∈ bases (r:=r) (s:=s) a C D f g n) :
    rs=Base.table C D wf wg (Search.value f) (Search.value g) a.zero n := by
  obtain ⟨rc,hrc,ht⟩ := Part.mem_bind_iff.mp h
  obtain ⟨rd,hrd,rfl⟩ := (Part.mem_map_iff _).mp ht
  rw [Search.compute_eq wf C a.zero hrc,Search.compute_eq wg D a.zero hrd]
  rfl

omit [DecidableEq A] [DecidableEq B] in
theorem tables_eq {f : List A → Part (Option Q)} {g : List B → Part (Option R)}
    {n : ℕ} {rs : List (List S × List S)} (h : rs ∈ tables (r:=r) (s:=s) a C D f g n) :
    rs=Selectors.process (a:=a) (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n)
      (Selectors.stages a.zero) n n := by
  obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp h
  rw [bases_eq a C D wf wg hb]

variable [Primcodable A] [Primcodable B] [Primcodable Q] [Primcodable R]
variable {X : Type*} [Primcodable X]
variable {F : X → List A → Part (Option Q)} {G : X → List B → Part (Option R)}

omit [DecidableEq A] [DecidableEq B] [Std.Trichotomous r] [Std.Trichotomous s] in
 theorem partrec_bases_parameter (hr : PrimrecRel (List.Shortlex r))
    (hs : PrimrecRel (List.Shortlex s)) (hF : Partrec₂ F) (hG : Partrec₂ G) :
    Partrec₂ (fun x => bases (r:=r) (s:=s) a C D (F x) (G x)) := by
  have hc : Partrec (fun p : X × ℕ => Search.compute (r:=r) C a.zero (F p.1) (p.2/(C.width+1))) :=
    (Search.partrec_compute_parameter C a.zero hr hF).comp Computable.fst
      (Primrec.nat_div.to_comp.comp Computable.snd (Computable.const _))
  have hd : Partrec (fun p : (X × ℕ) × List (List S × List S) =>
      Search.compute (r:=s) D a.zero (G p.1.1) (p.1.2/(D.width+1))) :=
    (Search.partrec_compute_parameter D a.zero hs hG).comp (Computable.fst.comp Computable.fst)
      (Primrec.nat_div.to_comp.comp (Computable.snd.comp Computable.fst) (Computable.const _))
  exact (hc.bind (hd.map (Primrec.list_append.to_comp.comp
    (Primrec.list_append.to_comp.comp (Computable.const (Base.absorption a.zero))
      (Computable.snd.comp Computable.fst)) Computable.snd).to₂).to₂).to₂

omit [DecidableEq A] [DecidableEq B] [Std.Trichotomous r] [Std.Trichotomous s] in
 theorem partrec_tables_parameter (hr : PrimrecRel (List.Shortlex r))
    (hs : PrimrecRel (List.Shortlex s)) (hF : Partrec₂ F) (hG : Partrec₂ G) :
    Partrec₂ (fun x => tables (r:=r) (s:=s) a C D (F x) (G x)) := by
  have hb := partrec_bases_parameter a C D hr hs hF hG
  exact (hb.map ((Selectors.primrec_process a _ (Selectors.primrec_stages a.zero)).to_comp.comp
    (Computable.snd.pair (Computable.snd.comp Computable.fst))
    (Computable.snd.comp Computable.fst)).to₂).to₂

end Build

 theorem partrec_tableNormal_parameter {X S : Type*} [DecidableEq S]
    [Primcodable X] [Primcodable S] {T : X → ℕ → Part (List (List S × List S))}
    (ht : Partrec₂ T) : Partrec₂ (fun x => tableNormal (T x)) := by
  exact ((ht.comp Computable.fst (Primrec.list_length.to_comp.comp Computable.snd)).bind
    (partrec_evaluate.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂).to₂

end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section
namespace Base
variable {S A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (f : List A → Option Q) (g : List B → Option R) (z : S)

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem bounded {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C D wf wg f g z k) (table C D wf wg f g z n) k := by
  intro p hp
  rw [mem_table,mem_table]
  exact or_congr Iff.rfl (or_congr (Static.table_bounded C wf f z hkn p hp)
    (Static.table_bounded D wg g z hkn p hp))

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R] in
theorem decrease {t : S → S → Prop} (hcw : 1<C.width+1) (hdw : 1<D.width+1)
    (hc : ∀ a b,r a b → List.Lex t (C.block a) (C.block b))
    (hd : ∀ a b,s a b → List.Lex t (D.block a) (D.block b)) (n : ℕ) :
    ∀ p ∈ table C D wf wg f g z n,List.Shortlex t p.2 p.1 := by
  intro ⟨u,v⟩ hp
  rcases (mem_table C D wf wg f g z).mp hp with hp | hp | hp
  · obtain ⟨a,hu,rfl⟩ := (mem_absorption z).mp hp
    rcases hu with rfl | rfl <;> exact List.Shortlex.of_length_lt (by simp)
  · exact Static.table_decrease C wf f z hcw hc _ _ hp
  · exact Static.table_decrease D wg g z hdw hd _ _ hp

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem shapes (a : Selectors.Markers S)
    (hC : ∀ b∈[a.d,a.l,a.r,a.h],b∉C.Alphabet)
    (hD : ∀ b∈[a.d,a.l,a.r,a.h],b∉D.Alphabet) (n : ℕ) :
    ∀ p ∈ table C D wf wg f g a.zero n,
      a.zero∈p.1 ∨ (p.1≠[] ∧ a.d∉p.1 ∧ a.l∉p.1 ∧ a.r∉p.1 ∧ a.h∉p.1) := by
  intro ⟨u,v⟩ hp
  rcases (mem_table C D wf wg f g a.zero).mp hp with hp | hp | hp
  · obtain ⟨b,hu,_⟩ := (mem_absorption a.zero).mp hp
    rcases hu with rfl | rfl <;> exact Or.inl (by simp)
  · obtain ⟨hn,hs⟩ := Static.table_support C wf f a.zero hp
    exact Or.inr ⟨hn,fun h => hC _ (by simp) (hs _ h),fun h => hC _ (by simp) (hs _ h),
      fun h => hC _ (by simp) (hs _ h),fun h => hC _ (by simp) (hs _ h)⟩
  · obtain ⟨hn,hs⟩ := Static.table_support D wg g a.zero hp
    exact Or.inr ⟨hn,fun h => hD _ (by simp) (hs _ h),fun h => hD _ (by simp) (hs _ h),
      fun h => hD _ (by simp) (hs _ h),fun h => hD _ (by simp) (hs _ h)⟩
end Base

namespace Build
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R))

omit [Primcodable S] [DecidableEq A] [DecidableEq B] in
theorem bases_full {n : ℕ}
    (hf : ∀ w,w.length ≤ n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length ≤ n/(D.width+1) → (g w).Dom) :
    Base.table C D wf wg (Search.value f) (Search.value g) a.zero n ∈ bases (r:=r) (s:=s) a C D f g n := by
  refine Part.mem_bind_iff.mpr ⟨_,Search.compute_full wf (Search.value f) C a.zero
    (fun w hw => Search.value_mem (hf w hw)),?_⟩
  exact (Part.mem_map_iff _).mpr ⟨_,Search.compute_full wg (Search.value g) D a.zero
    (fun w hw => Search.value_mem (hg w hw)),rfl⟩

omit [DecidableEq A] [DecidableEq B] in
theorem tables_full {n : ℕ}
    (hf : ∀ w,w.length ≤ n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length ≤ n/(D.width+1) → (g w).Dom) :
    Selectors.process (a:=a) (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n)
      (Selectors.stages a.zero) n n ∈ tables (r:=r) (s:=s) a C D f g n :=
  (Part.mem_map_iff _).mpr ⟨_,bases_full a C D wf wg f g hf hg,rfl⟩

include wf wg in
omit [DecidableEq A] [DecidableEq B] in
theorem stable {k n : ℕ} (hkn : k ≤ n) {rk rn : List (List S × List S)}
    (hk : rk ∈ tables (r:=r) (s:=s) a C D f g k)
    (hn : rn ∈ tables (r:=r) (s:=s) a C D f g n) : Selectors.BoundedEq rk rn k := by
  rw [tables_eq a C D wf wg hk,tables_eq a C D wf wg hn]
  exact Selectors.tables_bounded
    (fun _ _ hh => Base.bounded C D wf wg (Search.value f) (Search.value g) a.zero hh)
    (fun j w hw => Selectors.body_lt_size a.zero j hw)
    (Selectors.index_lt_size a.zero) hkn

include wf wg in
omit [DecidableEq A] [DecidableEq B] in
theorem good {t : S → S → Prop} (hcw : 1<C.width+1) (hdw : 1<D.width+1)
    (hc : ∀ a b,r a b → List.Lex t (C.block a) (C.block b))
    (hd : ∀ a b,s a b → List.Lex t (D.block a) (D.block b))
    (hC : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉C.Alphabet)
    (hD : ∀ b∈[a.zero,a.d,a.l,a.r,a.h],b∉D.Alphabet)
    (hCD : Disjoint C.Alphabet D.Alphabet) {n : ℕ}
    (hf : ∀ w,w.length ≤ n/(C.width+1) → (f w).Dom)
    (hg : ∀ w,w.length ≤ n/(D.width+1) → (g w).Dom)
    (hf0 : Search.value f []≠none) (hg0 : Search.value g []≠none)
    (hfc : Static.Contextual (Search.value f) (n/(C.width+1)))
    (hfi : Static.ZeroIdeal (Search.value f) (n/(C.width+1)))
    (hgc : Static.Contextual (Search.value g) (n/(D.width+1)))
    (hgi : Static.ZeroIdeal (Search.value g) (n/(D.width+1))) :
    GoodTable (r:=t) (tables (r:=r) (s:=s) a C D f g) n := by
  refine ⟨_,tables_full a C D wf wg f g hf hg,?_,?_⟩
  · exact Selectors.process_decrease
      (Base.decrease C D wf wg (Search.value f) (Search.value g) a.zero hcw hdw hc hd n) _ _ _
  · apply Selectors.process_critical
    · exact Base.absorbs C D wf wg (Search.value f) (Search.value g) a.zero n
    · exact Base.preserves_zero C D wf wg (Search.value f) (Search.value g) a.zero
        (hC _ (by simp)) (hD _ (by simp)) n
    · exact Base.shapes C D wf wg (Search.value f) (Search.value g) a
        (fun b hb => hC b (List.mem_cons_of_mem _ hb))
        (fun b hb => hD b (List.mem_cons_of_mem _ hb)) n
    · intro j w hw
      exact ⟨Selectors.body_lt_size a.zero j hw,(Selectors.tuples_valid a.zero j).2.2 w hw⟩
    · exact fun _ _ hh _ hw => Selectors.stage_spacing a hh hw
    · exact Base.critical C D wf wg (Search.value f) (Search.value g) a.zero
        (hC _ (by simp)) (hD _ (by simp)) hCD hf0 hg0 hfc hfi hgc hgi

end Build

namespace Quotient
open Relation
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))

/-- Literal equations of the stabilized infinite table. Restricting a stage to
its own budget removes only premature copies of the fixed absorption rules. -/
def Rel (u v : FreeMonoid S) : Prop :=
  ∃ n rs, rs ∈ T n ∧ (u.toList,v.toList) ∈ rs ∧ u.toList.length ≤ n

abbrev Mon := PresentedMonoid (Rel T)
def present (w : List S) : Mon T := PresentedMonoid.mk (Rel T) (FreeMonoid.ofList w)
noncomputable def normal (w : List S) : List S := Compiler.partValue (tableNormal T w)

omit [DecidableEq S] in
@[simp] theorem present_nil : present T []=1 := rfl
omit [DecidableEq S] in
@[simp] theorem present_append (u v : List S) : present T (u++v)=present T u * present T v := rfl

omit [DecidableEq S] in
 theorem present_step {n : ℕ} {rs : List (List S × List S)} (hrs : rs ∈ T n)
    {u v : List S} (hu : u.length ≤ n) (h : Step rs u v) : present T u=present T v := by
  cases h with
  | @apply a b hab x y =>
    have ha : a.length ≤ n := by simp only [List.length_append] at hu; omega
    have hh : present T a=present T b :=
      PresentedMonoid.mk_eq_mk_of_rel ⟨n,rs,hrs,hab,ha⟩
    simp only [present_append,hh]

omit [DecidableEq S] in
 theorem present_steps {r : S → S → Prop} {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs ∈ T n) (hd : ∀ p∈rs,List.Shortlex r p.2 p.1)
    {u v : List S} (hu : u.length ≤ n) (h : Steps rs u v) : present T u=present T v := by
  induction h with
  | refl => rfl
  | tail h hs ih => exact ih.trans (present_step T hrs ((steps_length hd h).trans hu) hs)

variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

 theorem budget (n : ℕ) : Compiler.PartialBudget (tableNormal T) n :=
  tableNormal_budget wf (fun _ _ => good _) (fun k m h _ => stable k m h)

 theorem normal_mem (w : List S) : normal T w ∈ tableNormal T w :=
  Compiler.partValue_mem ((budget T wf good stable w.length).total w le_rfl)

 theorem present_normal (w : List S) : present T w=present T (normal T w) := by
  obtain ⟨rs,hrs,hd,_⟩ := good w.length
  have h := normal_mem T wf good stable w
  rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at h
  exact present_steps T hrs hd le_rfl (evaluate_sound h).1

 theorem normal_context (x w y : List S) :
    normal T (x++normal T w++y)=normal T (x++w++y) := by
  exact congrArg Compiler.partValue ((budget T wf good stable (x++w++y).length).context
    x w y le_rfl _ (normal_mem T wf good stable w))

 theorem normal_append (u v : List S) :
    normal T (u++v)=normal T (normal T u++normal T v) := by
  have hu := normal_context T wf good stable [] u v
  have hv := normal_context T wf good stable (normal T u) v []
  simp only [List.nil_append,List.append_nil] at hu hv
  exact hu.symm.trans hv.symm

 theorem normal_rel {u v : FreeMonoid S} (h : Rel T u v) : normal T u.toList=normal T v.toList := by
  obtain ⟨n,rs,hrs,huv,hu⟩ := h
  obtain ⟨rt,hrt,hd,hc⟩ := good n
  have he := Part.mem_unique hrt hrs
  subst rt
  have hstep : Step rs u.toList v.toList := by
    simpa only [List.nil_append,List.append_nil] using Step.apply huv [] []
  have hv : v.toList.length ≤ n := (steps_length hd (.single hstep)).trans hu
  have hat (w : List S) (hw : w.length ≤ n) : tableNormal T w=evaluate rs w :=
    tableNormal_at wf (fun _ _ => good _) (fun k hk => stable k n hk) hrs hw
  have hnu := normal_mem T wf good stable u.toList
  have hnv := normal_mem T wf good stable v.toList
  rw [hat _ hu] at hnu
  rw [hat _ hv] at hnv
  exact evaluate_unique_on wf hd n (fun _ _ _ h => critical_localJoin hc h) hu
    (evaluate_sound hnu).1 ((ReflTransGen.single hstep).trans (evaluate_sound hnv).1)
    (evaluate_sound hnu).2 (evaluate_sound hnv).2

noncomputable def normalCon : Con (FreeMonoid S) where
  r u v := normal T u.toList=normal T v.toList
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h g => h.trans g⟩
  mul' := by
    intro u v x y huv hxy
    change normal T (u.toList++x.toList)=normal T (v.toList++y.toList)
    exact (normal_append T wf good stable _ _).trans
      ((congrArg₂ (fun a b => normal T (a++b)) huv hxy).trans
        (normal_append T wf good stable _ _).symm)

 theorem present_eq_iff (u v : List S) : present T u=present T v ↔ normal T u=normal T v := by
  constructor
  · intro h
    exact (Con.conGen_le.mpr (fun _ _ h => normal_rel T wf good stable h) :
      conGen (Rel T) ≤ normalCon T wf good stable) (PresentedMonoid.mk_eq_mk_iff.mp h)
  · intro h
    exact (present_normal T wf good stable u).trans (h ▸ (present_normal T wf good stable v).symm)

variable [Primcodable S]
 theorem computable_normal (hT : Partrec T) : Computable (normal T) := by
  have hp : Partrec (tableNormal T) :=
    ((hT.comp Primrec.list_length.to_comp).bind
      (partrec_evaluate.comp Computable.snd (Computable.fst)).to₂)
  apply hp.of_eq
  intro w
  exact Part.eq_some_iff.mpr (normal_mem T wf good stable w)

 theorem computable_wordProblem (hT : Partrec T) :
    ComputablePred (fun p : List S × List S => present T p.1=present T p.2) := by
  have hn := computable_normal T wf good stable hT
  have hh : ComputablePred (fun p : List S × List S => normal T p.1=normal T p.2) :=
    ⟨inferInstance, Primrec.eq.computablePred.decide.comp
      ((hn.comp Computable.fst).pair (hn.comp Computable.snd))⟩
  exact hh.of_eq (fun p => (present_eq_iff T wf good stable p.1 p.2).symm)

end Quotient

open Relation

namespace Selectors
variable {S : Type*} [DecidableEq S] {a : Markers S}

theorem process_mono (base : List (List S × List S)) (stages : ℕ → Stage S)
    (n : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    ∀ p∈process (a:=a) base stages n j,p∈process (a:=a) base stages n k := by
  induction hjk with
  | refl => exact fun _ h => h
  | @step k h ih =>
    exact fun p hp => choose_contains _ _ _ p (ih p hp)

theorem selected_mem {base : List (List S × List S)} {stages : ℕ → Stage S}
    {n j : ℕ} (hjn : j<n) (hs : (stages j).size≤n)
    (ha : allowed (process (a:=a) base stages n j) (stages j)=true) :
    ∀ p∈rules a (stages j).size (stages j).bodies,p∈process (a:=a) base stages n n := by
  intro p hp
  apply process_mono base stages n (Nat.succ_le_of_lt hjn) p
  change p∈choose (a:=a) (process base stages n j) (stages j) n
  rw [choose,ite_eq_left ⟨hs,ha⟩]
  exact List.mem_append_right _ hp
end Selectors

namespace Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

theorem normal_irreducible (w : List S) {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈T n) (hwlen : w.length≤n) : Irreducible (Step rs) (normal T w) := by
  have hw := normal_mem T wf good stable w
  rw [tableNormal_at wf (fun k _ => good k)
    (fun k hk => stable k _ hk) hrs hwlen] at hw
  exact (evaluate_sound hw).2

 theorem normal_idempotent (w : List S) : normal T (normal T w)=normal T w := by
  simpa only [List.nil_append,List.append_nil] using normal_context T wf good stable [] w []

 theorem normal_eq_self {w : List S} {rs : List (List S × List S)} (hrs : rs∈T w.length)
    (hi : Irreducible (Step rs) w) : normal T w=w := by
  have hw := normal_mem T wf good stable w
  rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at hw
  exact (irreducible_reaches (Step rs) hi (evaluate_sound hw).1).symm

omit [DecidableEq S] wf good stable in
 theorem present_surjective : Function.Surjective (present T) := by
  intro x
  obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
  exact ⟨w.toList,rfl⟩

noncomputable def representative (x : Mon T) : List S :=
  normal T (Classical.choose (present_surjective T x))

 theorem present_representative (x : Mon T) : present T (representative T x)=x := by
  rw [representative,←present_normal T wf good stable]
  exact Classical.choose_spec (present_surjective T x)

 theorem representative_injective : Function.Injective (representative T) := by
  intro x y he
  rw [←present_representative T wf good stable x,←present_representative T wf good stable y,he]

 theorem representative_irreducible (x : Mon T) {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈T n) (hx : (representative T x).length≤n) :
    Irreducible (Step rs) (representative T x) := by
  have h := normal_irreducible T wf good stable (representative T x) hrs hx
  simpa only [representative,normal_idempotent T wf good stable] using h

omit [DecidableEq S] wf good stable in
 theorem irreducible_of_short {rs : List (List S × List S)} {w : List S}
    (h : ∀ p∈rs,w.length<p.1.length) : Irreducible (Step rs) w := by
  intro v hv
  cases hv with
  | @apply u v huv x y =>
    have hh := h (u,v) huv
    simp only [List.length_append] at hh
    omega

 theorem present_nil_ne_zero (z : S)
    (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length) :
    (1 : Mon T)≠present T [z] := by
  obtain ⟨r0,hr0,_⟩ := good 0
  obtain ⟨r1,hr1,_⟩ := good 1
  have h0 : normal T []=[] := normal_eq_self T wf good stable hr0
    (irreducible_of_short (fun p hp => by simpa using Nat.lt_trans Nat.zero_lt_one (hshort 0 r0 hr0 p hp)))
  have h1 : normal T [z]=[z] := normal_eq_self T wf good stable hr1
    (irreducible_of_short (fun p hp => hshort 1 r1 hr1 p hp))
  intro he
  have hh := (present_eq_iff T wf good stable [] [z]).mp he
  rw [h0,h1] at hh
  simp at hh

omit [DecidableEq S] wf good stable in
 theorem present_absorbs (z : S) {rs : List (List S × List S)}
    (hrs : rs∈T 2) (hz : Absorbs rs z) :
    ∀ w,present T [z]*present T w=present T [z] ∧
      present T w*present T [z]=present T [z] := by
  have hza (a : S) : present T [z]*present T [a]=present T [z] :=
    PresentedMonoid.mk_eq_mk_of_rel ⟨2,rs,hrs,(hz a).1,by simp⟩
  have haz (a : S) : present T [a]*present T [z]=present T [z] :=
    PresentedMonoid.mk_eq_mk_of_rel ⟨2,rs,hrs,(hz a).2,by simp⟩
  intro w
  induction w with
  | nil => simp
  | cons a w ih =>
    have hh : present T (a::w)=present T [a]*present T w := rfl
    rw [hh]
    exact ⟨by rw [←mul_assoc,hza,ih.1],by rw [mul_assoc,ih.2,haz]⟩

@[instance_reducible]
noncomputable def monoidWithZero (z : S) {rs : List (List S × List S)}
    (hrs : rs∈T 2) (hz : Absorbs rs z) : MonoidWithZero (Mon T) where
  __ := (inferInstance : Monoid (Mon T))
  zero := present T [z]
  zero_mul x := by
    obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
    exact (present_absorbs T z hrs hz w.toList).1
  mul_zero x := by
    obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
    exact (present_absorbs T z hrs hz w.toList).2

 theorem representative_avoids_zero (z : S) (x : Mon T)
    (hx : x≠present T [z])
    (hz : ∀ n rs,rs∈T n → Absorbs rs z) : z∉representative T x := by
  intro hzx
  let w := representative T x
  obtain ⟨rs,hrs,hd,_⟩ := good w.length
  have he := present_steps T hrs hd le_rfl (absorbs_mem (hz _ _ hrs) hzx)
  exact hx ((present_representative T wf good stable x).symm.trans he)

end Quotient
namespace Selectors
variable {S : Type*} [DecidableEq S] [Primcodable S]

/-- Every nonzero irreducible ordered tuple receives its literal selector.
    The finite processing stage is chosen beyond the complete selector word. -/
theorem tuple_selected (a : Markers S) (T : ℕ → Part (List (List S × List S)))
    (bases : ℕ → List (List S × List S))
    (hT : ∀ n,process (a:=a) (bases n) (stages a.zero) n n ∈ T n)
    {ws : List (List S)} (hne : ws≠[]) (hd : ws.Nodup) (hz : ∀ w∈ws,a.zero∉w)
    (hi : ∀ w∈ws,∀ n rs,rs∈T n → w.length≤n → Irreducible (Step rs) w) :
    ∃ N,∀ w∈ws,Quotient.present T (a.wrap N w)=
      Quotient.present T (if ws.head?=some w then [] else [a.zero]) := by
  let j := Encodable.encode ws
  let N := sizes a.zero j
  let n := 3*N+2
  have he : (stages a.zero j).bodies=ws := tuples_complete a.zero hne hd hz
  have hsize : (stages a.zero j).size=N := rfl
  have hjN : j<N := index_lt_size a.zero j
  have hNn : N≤n := by omega
  have hjn : j<n := lt_of_lt_of_le hjN hNn
  have hlen (w : List S) (hw : w∈ws) : w.length<N := by
    apply body_lt_size a.zero j
    change w∈(stages a.zero j).bodies
    rw [he]
    exact hw
  have hall : allowed (process (a:=a) (bases n) (stages a.zero) n j) (stages a.zero j)=true := by
    apply allowed_iff.mpr
    intro w hw
    have hw' : w∈ws := he ▸ hw
    have nh := hi w hw' n _ (hT n) (le_trans (Nat.le_of_lt (hlen w hw')) hNn)
    intro v hv
    apply nh v
    exact step_mono (process_mono (bases n) (stages a.zero) n (Nat.le_of_lt hjn)) hv
  refine ⟨N,?_⟩
  intro w hw
  have hp : (a.wrap N w,if ws.head?=some w then [] else [a.zero])∈rules a
      (stages a.zero j).size (stages a.zero j).bodies := by
    rw [he,hsize]
    exact (mem_rules a).mpr ⟨w,hw,rfl,rfl⟩
  have hmem := selected_mem hjn (hsize ▸ hNn) hall _ hp
  apply PresentedMonoid.mk_eq_mk_of_rel
  refine ⟨n,_,hT n,hmem,?_⟩
  change (a.wrap N w).length≤n
  simp only [Markers.wrap,Envelopes.length_frame]
  have := hlen w hw
  omega

end Selectors
namespace Quotient
variable {S : Type*} [DecidableEq S] [Primcodable S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

/-- Source selectors for the stabilized quotient, with the distinguished element
    first in the tuple. Not an extra algebraic assumption on that quotient. -/
theorem selectors (a : Selectors.Markers S) (bases : ℕ → List (List S × List S))
    (hT : ∀ n,Selectors.process (a:=a) (bases n) (Selectors.stages a.zero) n n∈T n)
    (hz : ∀ n rs,rs∈T n → Absorbs rs a.zero)
    (X : Finset (Mon T)) (hX : present T [a.zero]∉X) (x : Mon T) (hx : x∈X) :
    ∃ L R : Mon T,L*x*R=1 ∧ ∀ y∈X,y≠x → L*y*R=present T [a.zero] := by
  classical
  let xs := x::(X.erase x).toList
  have xsne : xs≠[] := List.cons_ne_nil _ _
  have xsd : xs.Nodup := List.nodup_cons.mpr ⟨by simp,Finset.nodup_toList _⟩
  have xsmem (y : Mon T) : y∈xs ↔ y∈X := by
    simp only [xs,List.mem_cons,Finset.mem_toList,Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_,hh⟩)
      · exact hx
      · exact hh
    · intro hh
      by_cases he : y=x
      · exact Or.inl he
      · exact Or.inr ⟨he,hh⟩
  let rep := representative T
  have hrep : Function.Injective rep := representative_injective T wf good stable
  let ws := xs.map rep
  have hwsne : ws≠[] := by simp [ws,xs]
  have hwsd : ws.Nodup := xsd.map hrep
  have hwsz : ∀ w∈ws,a.zero∉w := by
    intro w hw
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
    exact representative_avoids_zero T wf good stable a.zero y
      (fun he => hX (he ▸ (xsmem y).mp hy)) hz
  have hwsi : ∀ w∈ws,∀ n rs,rs∈T n → w.length≤n → Irreducible (Step rs) w := by
    intro w hw n rs hrs hlen
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
    exact representative_irreducible T wf good stable y hrs hlen
  obtain ⟨N,hN⟩ := Selectors.tuple_selected a T bases hT hwsne hwsd hwsz hwsi
  let L := present T (a.d::List.replicate N a.l)
  let R := present T (List.replicate N a.r++[a.h])
  have heq (y : Mon T) : present T (a.wrap N (rep y))=L*y*R := by
    change present T (a.d::(List.replicate N a.l++rep y++List.replicate N a.r++[a.h]))=_
    have he : a.d::(List.replicate N a.l++rep y++List.replicate N a.r++[a.h])=
      (a.d::List.replicate N a.l)++rep y++(List.replicate N a.r++[a.h]) := by simp [List.append_assoc]
    rw [he,present_append,present_append,present_representative T wf good stable]
  refine ⟨L,R,?_,?_⟩
  · have hw : rep x∈ws := List.mem_map.mpr ⟨x,(xsmem x).mpr hx,rfl⟩
    have hs := hN _ hw
    rw [heq] at hs
    simpa only [ws,xs,List.map_cons,List.head?_cons,ite_true,present_nil] using hs
  · intro y hy hyx
    have hw : rep y∈ws := List.mem_map.mpr ⟨y,(xsmem y).mpr hy,rfl⟩
    have hs := hN _ hw
    rw [heq] at hs
    have hne : ws.head?≠some (rep y) := by
      simp only [ws,xs,List.map_cons,List.head?_cons]
      exact fun h => hyx (hrep (Option.some.inj h)).symm
    simpa only [ite_eq_right hne] using hs

end Quotient
end

namespace Static
variable {S A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_short (hc : 1<C.width+1) {n : ℕ} {p : List S × List S}
    (hp : p∈table C wf q z n) : 1<p.1.length := by
  obtain ⟨w,_,hn,_,he,_⟩ := (mem_table C wf q z).mp hp
  rw [he,C.encode_length]
  have hl : 1≤w.length := List.length_pos_iff.mpr hn
  exact hc.trans_le (by simpa using Nat.mul_le_mul_left (C.width+1) hl)
end Static

namespace Build
variable {S A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R))

include wf wg in
omit [DecidableEq A] [DecidableEq B] in
theorem tables_absorb {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈tables (r:=r) (s:=s) a C D f g n) : Absorbs rs a.zero := by
  rw [tables_eq a C D wf wg hrs]
  have hh := Selectors.process_contains (a:=a)
    (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n)
    (Selectors.stages a.zero) n n
  intro b
  exact ⟨hh _ (Base.absorbs C D wf wg (Search.value f) (Search.value g) a.zero n b).1,
    hh _ (Base.absorbs C D wf wg (Search.value f) (Search.value g) a.zero n b).2⟩

include wf wg in
omit [DecidableEq A] [DecidableEq B] in
theorem tables_short (hc : 1<C.width+1) (hd : 1<D.width+1) {n : ℕ}
    {rs : List (List S × List S)} (hrs : rs∈tables (r:=r) (s:=s) a C D f g n) :
    ∀ p∈rs,1<p.1.length := by
  rw [tables_eq a C D wf wg hrs]
  intro p hp
  rcases Selectors.process_members hp with hp | ⟨j,hj,hp⟩
  · rcases (Base.mem_table C D wf wg (Search.value f) (Search.value g) a.zero).mp hp with hp | hp | hp
    · obtain ⟨b,(he | he),_⟩ := (Base.mem_absorption a.zero).mp hp <;> rw [he] <;> simp
    · exact Static.table_short C wf (Search.value f) a.zero hc hp
    · exact Static.table_short D wg (Search.value g) a.zero hd hp
  · obtain ⟨w,_,he,_⟩ := (Selectors.mem_rules a).mp hp
    rw [he]
    simp only [Selectors.Markers.wrap,Envelopes.length_frame]
    omega

include wf wg in
omit [DecidableEq A] [DecidableEq B] in
/-- Once bounded induction has proved total tables, their process descriptions
    are genuine members. No totality of static programs is added here. -/
theorem tables_process {t : S → S → Prop}
    (good : ∀ n,GoodTable (r:=t) (tables (r:=r) (s:=s) a C D f g) n) (n : ℕ) :
    Selectors.process (a:=a) (Base.table C D wf wg (Search.value f) (Search.value g) a.zero n)
      (Selectors.stages a.zero) n n∈tables (r:=r) (s:=s) a C D f g n := by
  obtain ⟨rs,hrs,_⟩ := good n
  rw [←tables_eq a C D wf wg hrs]
  exact hrs

end Build
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_surjective : Function.Surjective (present A M) := by
  intro x
  obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
  exact ⟨w.toList,rfl⟩

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_zero_mul (w : List (Letter S Γ Q)) :
    present A M [.zero] * present A M w=present A M [.zero] := by
  induction w with
  | nil => exact mul_one _
  | cons c w ih =>
    have hh : present A M [.zero,c]=present A M [.zero] :=
      PresentedMonoid.mk_eq_mk_of_rel (.zero (.pair _ _ (by simp [Path.typeOf])))
    have hp : present A M (c::w)=present A M [c]*present A M w := rfl
    rw [hp,←mul_assoc]
    change present A M [.zero,c]*present A M w=_
    rw [hh,ih]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_mul_zero (w : List (Letter S Γ Q)) :
    present A M w * present A M [.zero]=present A M [.zero] := by
  induction w with
  | nil => exact one_mul _
  | cons c w ih =>
    have hh : present A M [c,.zero]=present A M [.zero] :=
      PresentedMonoid.mk_eq_mk_of_rel (.zero (.pair _ _ (by simp [Path.typeOf])))
    have hp : present A M (c::w)=present A M [c]*present A M w := rfl
    rw [hp,mul_assoc,ih]
    exact hh

@[instance_reducible]
noncomputable def monoidWithZero : MonoidWithZero (Presentation A M) where
  __ := (inferInstance : Monoid (Presentation A M))
  zero := present A M [.zero]
  zero_mul x := by
    obtain ⟨w,rfl⟩ := present_surjective A M x
    exact present_zero_mul A M w
  mul_zero x := by
    obtain ⟨w,rfl⟩ := present_surjective A M x
    exact present_mul_zero A M w

variable [Primcodable S]
variable (hle : PrimrecRel (fun a b : Control.Sector S Γ Q => a≤b))
variable {f : List S → Part (List S)} (hf : Partrec f)
variable (budget : ∀ n,PartialBudget f n)
include hle hf budget

 theorem computable_normal : Computable (normal A M (fun w => partValue (f w))) := by
  apply (partrec_partialNormal A M hle hf).of_eq
  intro w
  exact partialNormal_eq_some A M (budget (grade w)) w le_rfl

 theorem computable_wordProblem
    (hdecode : ∀ g a,A.output g=some a → g=A.input a) (hr : Realizes A M f) :
    ComputablePred (fun p : List (Letter S Γ Q) × List (Letter S Γ Q) =>
      present A M p.1=present A M p.2) := by
  have hn := computable_normal A M hle hf budget
  have he : ComputablePred (fun p : List (Letter S Γ Q) × List (Letter S Γ Q) =>
      normal A M (fun w => partValue (f w)) p.1=normal A M (fun w => partValue (f w)) p.2) :=
    ⟨inferInstance,Primrec.eq.computablePred.decide.comp
      ((hn.comp Computable.fst).pair (hn.comp Computable.snd))⟩
  exact he.of_eq (fun p => (present_eq_iff_normal A M hdecode (fun n => (budget n).totalize)
    (fun n => hr.computesAt A M (budget n)) p.1 p.2).symm)

end Compiler.Word

namespace Bootstrap.Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

theorem representative_mul (x y : Mon T) : representative T (x*y)=
    normal T (representative T x++representative T y) := by
  have he : present T (representative T (x*y))=
      present T (representative T x++representative T y) := by
    rw [present_append,present_representative T wf good stable,
      present_representative T wf good stable,present_representative T wf good stable]
  have hn := (present_eq_iff T wf good stable _ _).mp he
  simpa only [representative,normal_idempotent T wf good stable] using hn

variable {Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q] [LinearOrder (Compiler.Control.Sector S Γ Q)]
variable (A : Compiler.Simulator.Alphabet S Γ) (M : Compiler.Simulator.Machine Q Γ)
variable (hdecode : ∀ g a,A.output g=some a → g=A.input a)
variable (hr : Compiler.Word.Realizes A M (tableNormal T))

noncomputable def rawMap (hdecode : ∀ g a,A.output g=some a → g=A.input a)
    (hr : Compiler.Word.Realizes A M (tableNormal T)) : Mon T →ₙ* Compiler.Word.Presentation A M where
  toFun x := Compiler.Word.present A M (Compiler.Word.raw A.blank (representative T x))
  map_mul' x y := by
    have hb := fun n => (budget T wf good stable n).totalize
    have hc := fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n)
    apply (Compiler.Word.present_eq_iff_normal A M hdecode hb hc _ _).mpr
    change Compiler.Word.normal A M (fun w => Compiler.partValue (tableNormal T w))
      (Compiler.Word.raw A.blank (representative T (x*y))) =
      Compiler.Word.normal A M (fun w => Compiler.partValue (tableNormal T w))
      (Compiler.Word.raw A.blank (representative T x) ++
        Compiler.Word.raw A.blank (representative T y))
    rw [Compiler.Word.normal_raw,Compiler.Word.normal_raw_product,
      representative_mul T wf good stable]
    rfl

include hdecode hr in
theorem rawMap_injective : Function.Injective (rawMap T wf good stable A M hdecode hr) := by
  intro x y hxy
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n)) _ _).mp hxy
  simp only [Compiler.Word.normal_raw] at hn
  have he := congrArg Compiler.Word.rawLetters hn
  simp only [Compiler.Word.rawLetters_raw] at he
  exact representative_injective T wf good stable he

include hdecode hr in
theorem rawMap_ne_one (x : Mon T) : rawMap T wf good stable A M hdecode hr x≠1 := by
  intro hx
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n))
    (Compiler.Word.raw A.blank (representative T x)) []).mp hx
  simp only [Compiler.Word.normal_raw,Compiler.Word.normal_nil] at hn
  simp [Compiler.Word.raw,Compiler.Word.encode,Compiler.Surface.raw,Compiler.Scan.literal,
    Compiler.Path.encode,Compiler.Path.headed] at hn

include hdecode hr in
theorem rawMap_ne_zero (x : Mon T) :
    rawMap T wf good stable A M hdecode hr x≠Compiler.Word.present A M [.zero] := by
  intro hx
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n))
    (Compiler.Word.raw A.blank (representative T x)) [.zero]).mp hx
  simp only [Compiler.Word.normal_raw,Compiler.Word.normal_omega] at hn
  simp [Compiler.Word.raw,Compiler.Word.encode,Compiler.Surface.raw,Compiler.Scan.literal,
    Compiler.Path.encode,Compiler.Path.headed] at hn

end Bootstrap.Quotient
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation
variable {S : Type*}

theorem irreducible_of_no_infix {rs : List (List S × List S)} {w : List S}
    (h : ∀ p∈rs, ¬ p.1 <:+: w) : Irreducible (Step rs) w := by
  intro v hv
  cases hv with
  | @apply u v hp x y => exact h (u,v) hp ⟨x,y,rfl⟩

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

omit [DecidableEq A] [DecidableEq Q] [Std.Trichotomous r] in
theorem table_mono {k n : ℕ} (hkn : k≤n) {p : List S × List S}
    (hp : p∈table C wf q z k) : p∈table C wf q z n := by
  obtain ⟨w,hw,hn,he,hl,hr⟩ := (mem_table C wf q z).mp hp
  exact (mem_table C wf q z).mpr ⟨w,hw.trans hkn,hn,he,hl,hr⟩

omit [DecidableEq A] [DecidableEq Q] in
theorem canonical_no_infix (hc : ∀ n,Contextual q n) (hi : ∀ n,ZeroIdeal q n)
    {w : List A} (hw : q w≠none) {n : ℕ} {u v : List S}
    (hp : (u,v)∈table C wf q z n) : ¬ u <:+: C.encode (Canonical.least wf q w) := by
  obtain ⟨c,_,hcn,hn,rfl,rfl⟩ := (mem_table C wf q z).mp hp
  rintro ⟨x,y,he⟩
  obtain ⟨a,b,hab,hx,hy⟩ := C.occurrence_decode hcn he.symm
  have hq : q (a++c++b)=q w := hab ▸ Canonical.least_class wf q w
  by_cases hz : q c=none
  · exact hw (hq.symm.trans (hi _ a b c le_rfl hz))
  · have hlt : List.Shortlex r (Canonical.least wf q c) c := by
      rcases Canonical.least_lt_or_eq wf q c with h | h
      · exact h
      · exact False.elim (hn (by simp [output,hz,h]))
    have hb : (a++Canonical.least wf q c++b).length≤(a++c++b).length := by
      have hh := Canonical.least_length wf q c
      simp only [List.length_append]
      omega
    have hclass : q (a++Canonical.least wf q c++b)=q w :=
      (hc _ a b _ c hb le_rfl (Canonical.least_class wf q c)).trans hq
    apply Canonical.least_global_min wf q hclass
    rw [hab]
    exact shortlex_context hlt a b

omit [DecidableEq A] [DecidableEq Q] in
/-- Rules of the other code and selector/zero rules cannot occur in a pure code. -/
theorem canonical_irreducible {rs : List (List S × List S)} {n : ℕ}
    (hiso : ∀ p∈rs,p∈table C wf q z n ∨ ∃ s∈p.1,s∉C.Alphabet)
    (hc : ∀ k,Contextual q k) (hi : ∀ k,ZeroIdeal q k)
    {w : List A} (hw : q w≠none) :
    Irreducible (Step rs) (C.encode (Canonical.least wf q w)) := by
  apply irreducible_of_no_infix
  intro p hp hif
  rcases hiso p hp with hp | ⟨s,hs,hn⟩
  · exact canonical_no_infix C wf q z hc hi hw hp hif
  · exact hn (C.mem_alphabet (hif.subset hs))
omit [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q] in
theorem output_eq_iff (hz : z∉C.Alphabet) (u v : List A) :
    output C wf q z u=output C wf q z v ↔ q u=q v := by
  constructor
  · intro he
    by_cases hu : q u=none <;> by_cases hv : q v=none
    · exact hu.trans hv.symm
    · have hh : z∈C.encode (Canonical.least wf q v) := by
        rw [output,ite_eq_left hu,output,ite_eq_right hv] at he
        rw [←he]; simp
      exact False.elim (hz (C.mem_alphabet hh))
    · have hh : z∈C.encode (Canonical.least wf q u) := by
        rw [output,ite_eq_right hu,output,ite_eq_left hv] at he
        rw [he]; simp
      exact False.elim (hz (C.mem_alphabet hh))
    · rw [output,ite_eq_right hu,output,ite_eq_right hv] at he
      have h := C.encode_injective he
      exact (Canonical.least_class wf q u).symm.trans
        ((congrArg q h).trans (Canonical.least_class wf q v))
  · exact output_congr C wf q z
end Static

namespace Quotient
variable [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {t : S → S → Prop} (wt : WellFounded t)
  (good : ∀ n,GoodTable (r:=t) T n)
  (stable : ∀ k n,k≤n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
  {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)
variable (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length)
variable (hiso : ∀ n rs,rs∈T n → ∀ p∈rs,p∈Static.table C wf q z n ∨ ∃ s∈p.1,s∉C.Alphabet)
variable (hstatic : ∀ n rs,rs∈T ((C.width+1)*n) → ∀ p∈Static.table C wf q z n,p∈rs)
variable (hc : ∀ n,Static.Contextual q n) (hi : ∀ n,Static.ZeroIdeal q n) (hzero : q []≠none)
include wt good stable hshort hiso hstatic hc hi hzero

omit [DecidableEq A] [DecidableEq Q] in
theorem normal_encode (w : List A) : normal T (C.encode w)=Static.output C wf q z w := by
  have hfixed : normal T (Static.output C wf q z w)=Static.output C wf q z w := by
    by_cases hq : q w=none
    · rw [Static.output,ite_eq_left hq]
      obtain ⟨rs,hrs,_⟩ := good 1
      exact normal_eq_self T wt good stable hrs
        (irreducible_of_short (fun p hp => hshort 1 rs hrs p hp))
    · rw [Static.output,ite_eq_right hq]
      obtain ⟨rs,hrs,_⟩ := good (C.encode (Canonical.least wf q w)).length
      exact normal_eq_self T wt good stable hrs
        (Static.canonical_irreducible C wf q z (hiso _ rs hrs) hc hi hq)
  have hpres : present T (C.encode w)=present T (Static.output C wf q z w) := by
    obtain ⟨rs,hrs,hd,_⟩ := good ((C.width+1)*w.length)
    exact present_steps T hrs hd (by rw [C.encode_length])
      (steps_mono (hstatic w.length rs hrs) (Static.whole_steps C wf q z hzero le_rfl))
  exact ((present_eq_iff T wt good stable _ _).mp hpres).trans hfixed

omit [DecidableEq A] [DecidableEq Q] in
theorem present_encode_iff (hz : z∉C.Alphabet) (u v : List A) :
    present T (C.encode u)=present T (C.encode v) ↔ q u=q v := by
  rw [present_eq_iff T wt good stable,
    normal_encode T wt good stable C wf q z hshort hiso hstatic hc hi hzero,
    normal_encode T wt good stable C wf q z hshort hiso hstatic hc hi hzero]
  exact Static.output_eq_iff C wf q z hz u v
end Quotient

namespace Base
variable {A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [DecidableEq S] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (q : List A → Option Q) (g : List B → Option R) (z : S)

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem isolate_left (hz : z∉C.Alphabet) (hd : Disjoint C.Alphabet D.Alphabet)
    {n : ℕ} {p : List S × List S} (hp : p∈table C D wf wg q g z n) :
    p∈Static.table C wf q z n ∨ ∃ s∈p.1,s∉C.Alphabet := by
  rcases (mem_table C D wf wg q g z).mp hp with hp | hp | hp
  · obtain ⟨b,hb,_⟩ := (mem_absorption z).mp hp
    exact Or.inr ⟨z,by rcases hb with h | h <;> simp [h],hz⟩
  · exact Or.inl (Static.table_mono C wf q z (Nat.div_le_self n _) hp)
  · obtain ⟨hn,hs⟩ := Static.table_support D wg g z hp
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hn
    exact Or.inr ⟨b,hb,fun hc => Set.disjoint_left.mp hd hc (hs b hb)⟩
end Base

namespace Selectors
variable [DecidableEq S] (a : Markers S)
theorem process_isolate {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
    {r : A → A → Prop} [Std.Trichotomous r]
    (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q)
    {rs : List (List S × List S)} {n : ℕ}
    (hbase : ∀ p∈rs,p∈Static.table C wf q a.zero n ∨ ∃ s∈p.1,s∉C.Alphabet)
    (hd : a.d∉C.Alphabet) (stages : ℕ → Stage S) (budget j : ℕ)
    {p : List S × List S} (hp : p∈process (a:=a) rs stages budget j) :
    p∈Static.table C wf q a.zero n ∨ ∃ s∈p.1,s∉C.Alphabet := by
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hbase p hp
  · obtain ⟨w,_,he,_⟩ := (mem_rules a).mp hp
    exact Or.inr ⟨a.d,by simp [he,Markers.wrap,Envelopes.frame],hd⟩
end Selectors

namespace Build
variable {A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R))

include wf wg in
omit [DecidableEq B] in
theorem tables_isolate (hz : a.zero∉C.Alphabet) (hd : a.d∉C.Alphabet)
    (hCD : Disjoint C.Alphabet D.Alphabet) {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈tables (r:=r) (s:=s) a C D f g n) :
    ∀ p∈rs,p∈Static.table C wf (Search.value f) a.zero n ∨ ∃ b∈p.1,b∉C.Alphabet := by
  rw [tables_eq a C D wf wg hrs]
  intro p hp
  exact Selectors.process_isolate a C wf (Search.value f)
    (fun p hp => Base.isolate_left C D wf wg (Search.value f) (Search.value g) a.zero hz hCD hp)
    hd _ _ _ hp

include wf wg in
omit [DecidableEq A] [DecidableEq B] in
theorem tables_static (n : ℕ) {rs : List (List S × List S)}
    (hrs : rs∈tables (r:=r) (s:=s) a C D f g ((C.width+1)*n)) :
    ∀ p∈Static.table C wf (Search.value f) a.zero n,p∈rs := by
  rw [tables_eq a C D wf wg hrs]
  intro p hp
  apply Selectors.process_contains
  apply (Base.mem_table C D wf wg (Search.value f) (Search.value g) a.zero).mpr
  exact Or.inr (Or.inl (by simpa using hp))
end Build

namespace Quotient
variable [DecidableEq S] {A M : Type*} [Monoid M]
variable {T : ℕ → Part (List (List S × List S))} (C : BlockCode A S)

def codeHom : FreeMonoid A →* Mon T where
  toFun w := present T (C.encode w.toList)
  map_one' := by simp
  map_mul' u v := by simp only [FreeMonoid.toList_mul,BlockCode.encode_append,present_append]

variable (e : FreeMonoid A →* M) (he : Function.Surjective e)
  (hc : ∀ u v : List A,present T (C.encode u)=present T (C.encode v) ↔
    e (FreeMonoid.ofList u)=e (FreeMonoid.ofList v))

noncomputable def descendCode : M →* Mon T where
  toFun x := codeHom C (he x).choose
  map_one' := by
    have hx : e (he 1).choose=e 1 := (he 1).choose_spec.trans e.map_one.symm
    exact (hc _ []).mpr hx
  map_mul' x y := by
    change present T (C.encode ((he (x*y)).choose.toList)) =
      present T (C.encode ((he x).choose.toList))*present T (C.encode ((he y).choose.toList))
    rw [←present_append,←BlockCode.encode_append]
    apply (hc _ _).mpr
    change e (he (x*y)).choose=e ((he x).choose * (he y).choose)
    rw [e.map_mul,(he (x*y)).choose_spec,(he x).choose_spec,(he y).choose_spec]

omit [DecidableEq S] in
theorem descendCode_apply (w : List A) :
    descendCode C e he hc (e (FreeMonoid.ofList w))=present T (C.encode w) :=
  (hc _ w).mpr (he (e (FreeMonoid.ofList w))).choose_spec

omit [DecidableEq S] in
theorem descendCode_injective : Function.Injective (descendCode C e he hc) := by
  intro x y h
  exact (he x).choose_spec.symm.trans (((hc _ _).mp h).trans (he y).choose_spec)
end Quotient

end

variable {S : Type*}

namespace Separator

theorem prefix_before {z : S} {p u v : List S} (hz : z∉p)
    (h : p <+: u++z::v) : p <+: u := by
  induction u generalizing p with
  | nil =>
    have hnil : p=[] := by
      cases p with
      | nil => rfl
      | cons a p =>
        have ha := (List.cons_prefix_cons.mp h).1
        exact False.elim (hz (by simp [ha]))
    simp [hnil]
  | cons a u ih =>
    cases p with
    | nil => simp
    | cons b p =>
      obtain ⟨rfl,hp⟩ := List.cons_prefix_cons.mp h
      exact List.cons_prefix_cons.mpr ⟨rfl,ih (fun hh => hz (List.mem_cons_of_mem _ hh)) hp⟩

theorem infix_split {z : S} {p u v : List S} (hz : z∉p)
    (h : p <:+: u++z::v) : p <:+: u ∨ p <:+: v := by
  induction u with
  | nil =>
    rcases List.infix_cons_iff.mp h with hp | hp
    · have he := List.prefix_nil.mp (prefix_before (u:=[]) hz hp)
      exact Or.inl (by simp [he])
    · exact Or.inr hp
  | cons a u ih =>
    rcases List.infix_cons_iff.mp h with hp | hp
    · exact Or.inl (prefix_before hz hp).isInfix
    · rcases ih hp with hu | hv
      · exact Or.inl (List.infix_cons_iff.mpr (Or.inr hu))
      · exact Or.inr hv

theorem split_injective {z : S} {u v u' v' : List S}
    (hu : z∉u) (hu' : z∉u') (he : u++z::v=u'++z::v') : u=u' ∧ v=v' := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil => exact ⟨rfl,(List.cons.inj he).2⟩
    | cons a u' =>
      have ha : z=a := (List.cons.inj he).1
      exact False.elim (hu' (by simp [ha]))
  | cons a u ih =>
    cases u' with
    | nil =>
      have ha : a=z := (List.cons.inj he).1
      exact False.elim (hu (by simp [ha]))
    | cons b u' =>
      obtain ⟨rfl,hrest⟩ := List.cons.inj he
      obtain ⟨rfl,hv⟩ := ih (fun h => hu (List.mem_cons_of_mem _ h))
        (fun h => hu' (List.mem_cons_of_mem _ h)) hrest
      exact ⟨rfl,hv⟩
end Separator

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (zero sep : S)

omit [DecidableEq A] [DecidableEq Q] in
theorem separator_irreducible (hs : sep∉C.Alphabet)
    {rs : List (List S × List S)} {n : ℕ}
    (hiso : ∀ p∈rs,p∈table C wf q zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep)
    (hc : ∀ k,Contextual q k) (hi : ∀ k,ZeroIdeal q k)
    {u v : List A} (hu : q u≠none) (hv : q v≠none) :
    Irreducible (Step rs)
      (C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v)) := by
  apply irreducible_of_no_infix
  intro p hp hif
  rcases hiso p hp with hp | ⟨b,hb,hbc,hbs⟩
  · have hs' : sep∉p.1 := fun hh => hs ((table_support C wf q zero hp).2 sep hh)
    rcases Separator.infix_split hs' hif with hif | hif
    · exact canonical_no_infix C wf q zero hc hi hu hp hif
    · exact canonical_no_infix C wf q zero hc hi hv hp hif
  · have hh := hif.subset hb
    simp only [List.mem_append,List.mem_cons] at hh
    rcases hh with hh | hh | hh
    · exact hbc (C.mem_alphabet hh)
    · exact hbs hh
    · exact hbc (C.mem_alphabet hh)

omit [Fintype A] [DecidableEq A] [DecidableEq S] [DecidableEq Q] [Std.Trichotomous r] in
theorem separator_literal_injective (hs : sep∉C.Alphabet)
    {u v u' v' : List A}
    (he : C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v)=
      C.encode (Canonical.least wf q u')++sep::C.encode (Canonical.least wf q v')) :
    q u=q u' ∧ q v=q v' := by
  have hh := Separator.split_injective (fun h => hs (C.mem_alphabet h))
    (fun h => hs (C.mem_alphabet h)) he
  have hu := C.encode_injective hh.1
  have hv := C.encode_injective hh.2
  exact ⟨(Canonical.least_class wf q u).symm.trans
    ((congrArg q hu).trans (Canonical.least_class wf q u')),
    (Canonical.least_class wf q v).symm.trans
    ((congrArg q hv).trans (Canonical.least_class wf q v'))⟩
end Static

namespace Base
variable {A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [DecidableEq S] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (C : BlockCode A S) (D : BlockCode B S) (wf : WellFounded r) (wg : WellFounded s)
  (q : List A → Option Q) (g : List B → Option R) (zero sep : S)

omit [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
  [Std.Trichotomous r] [Std.Trichotomous s] in
theorem isolate_separator (hz : zero∉C.Alphabet) (hsep : zero≠sep)
    (hsD : sep∉D.Alphabet) (hd : Disjoint C.Alphabet D.Alphabet)
    {n : ℕ} {p : List S × List S} (hp : p∈table C D wf wg q g zero n) :
    p∈Static.table C wf q zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep := by
  rcases (mem_table C D wf wg q g zero).mp hp with hp | hp | hp
  · obtain ⟨b,hb,_⟩ := (mem_absorption zero).mp hp
    exact Or.inr ⟨zero,by rcases hb with h | h <;> simp [h],hz,hsep⟩
  · exact Or.inl (Static.table_mono C wf q zero (Nat.div_le_self n _) hp)
  · obtain ⟨hn,hs⟩ := Static.table_support D wg g zero hp
    obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hn
    exact Or.inr ⟨b,hb,(fun hc => Set.disjoint_left.mp hd hc (hs b hb)),
      fun he => hsD (he ▸ hs b hb)⟩
end Base

namespace Selectors
variable [DecidableEq S] (a : Markers S)
theorem process_isolate_separator {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
    {r : A → A → Prop} [Std.Trichotomous r]
    (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (sep : S)
    {rs : List (List S × List S)} {n : ℕ}
    (hbase : ∀ p∈rs,p∈Static.table C wf q a.zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep)
    (hd : a.d∉C.Alphabet) (hds : a.d≠sep) (stages : ℕ → Stage S) (budget j : ℕ)
    {p : List S × List S} (hp : p∈process (a:=a) rs stages budget j) :
    p∈Static.table C wf q a.zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep := by
  rcases process_members hp with hp | ⟨i,_,hp⟩
  · exact hbase p hp
  · obtain ⟨w,_,he,_⟩ := (mem_rules a).mp hp
    exact Or.inr ⟨a.d,by simp [he,Markers.wrap,Envelopes.frame],hd,hds⟩
end Selectors

namespace Build
variable {A B Q R : Type*} [Primcodable S] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop}
  [DecidableRel (List.Shortlex r)] [DecidableRel (List.Shortlex s)]
  [Std.Trichotomous r] [Std.Trichotomous s]
variable (a : Selectors.Markers S) (C : BlockCode A S) (D : BlockCode B S)
  (wf : WellFounded r) (wg : WellFounded s)
variable (f : List A → Part (Option Q)) (g : List B → Part (Option R)) (sep : S)

include wf wg in
omit [DecidableEq B] in
theorem tables_isolate_separator (hz : a.zero∉C.Alphabet) (hd : a.d∉C.Alphabet)
    (hzs : a.zero≠sep) (hds : a.d≠sep) (hsD : sep∉D.Alphabet)
    (hCD : Disjoint C.Alphabet D.Alphabet) {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs∈tables (r:=r) (s:=s) a C D f g n) :
    ∀ p∈rs,p∈Static.table C wf (Search.value f) a.zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep := by
  rw [tables_eq a C D wf wg hrs]
  intro p hp
  exact Selectors.process_isolate_separator a C wf (Search.value f) sep
    (fun p hp => Base.isolate_separator C D wf wg (Search.value f) (Search.value g)
      a.zero sep hz hzs hsD hCD hp) hd hds _ _ _ hp
end Build

namespace Quotient
variable [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {t : S → S → Prop} (wt : WellFounded t)
  (good : ∀ n,GoodTable (r:=t) T n)
  (stable : ∀ k n,k≤n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
variable {A Q : Type*} [Fintype A] [DecidableEq A] [DecidableEq Q]
  {r : A → A → Prop} [Std.Trichotomous r]
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (zero sep : S)
variable (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length)
variable (hiso : ∀ n rs,rs∈T n → ∀ p∈rs,p∈Static.table C wf q zero n ∨ ∃ b∈p.1,b∉C.Alphabet ∧ b≠sep)
variable (hstatic : ∀ n rs,rs∈T ((C.width+1)*n) → ∀ p∈Static.table C wf q zero n,p∈rs)
variable (hc : ∀ n,Static.Contextual q n) (hi : ∀ n,Static.ZeroIdeal q n) (hzero : q []≠none)
variable (hs : sep∉C.Alphabet)
include wt good stable hshort hiso hstatic hc hi hzero hs

omit [DecidableEq A] [DecidableEq Q] in
theorem normal_separator {u v : List A} (hu : q u≠none) (hv : q v≠none) :
    normal T (C.encode u++sep::C.encode v)=
      C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v) := by
  have hcode (w : List A) (hw : q w≠none) :
      normal T (C.encode w)=C.encode (Canonical.least wf q w) := by
    rw [normal_encode T wt good stable C wf q zero hshort
      (fun n rs hrs p hp => (hiso n rs hrs p hp).imp id (by rintro ⟨b,hb,hbc,_⟩; exact ⟨b,hb,hbc⟩))
      hstatic hc hi hzero,Static.output,ite_eq_right hw]
  have hleft : normal T (C.encode u++sep::C.encode v)=
      normal T (normal T (C.encode u)++sep::C.encode v) := by
    simpa only [List.nil_append] using
      (normal_context T wt good stable [] (C.encode u) (sep::C.encode v)).symm
  have hright : normal T (normal T (C.encode u)++sep::C.encode v)=
      normal T (normal T (C.encode u)++sep::normal T (C.encode v)) := by
    simpa only [List.append_nil,List.append_assoc,List.singleton_append] using
      (normal_context T wt good stable (normal T (C.encode u)++[sep]) (C.encode v) []).symm
  rw [hleft,hright,hcode u hu,hcode v hv]
  obtain ⟨rs,hrs,_⟩ := good
    (C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v)).length
  exact normal_eq_self T wt good stable hrs
    (Static.separator_irreducible C wf q zero sep hs (hiso _ rs hrs) hc hi hu hv)

omit [DecidableEq A] [DecidableEq Q] in
theorem present_separator_iff {u v u' v' : List A}
    (hu : q u≠none) (hv : q v≠none) (hu' : q u'≠none) (hv' : q v'≠none) :
    present T (C.encode u++sep::C.encode v)=present T (C.encode u'++sep::C.encode v') ↔
      q u=q u' ∧ q v=q v' := by
  rw [present_eq_iff T wt good stable,
    normal_separator T wt good stable C wf q zero sep hshort hiso hstatic hc hi hzero hs hu hv,
    normal_separator T wt good stable C wf q zero sep hshort hiso hstatic hc hi hzero hs hu' hv']
  constructor
  · exact Static.separator_literal_injective C wf q sep hs
  · rintro ⟨hu,hv⟩
    rw [Canonical.least_congr wf q hu,Canonical.least_congr wf q hv]

omit [DecidableEq A] [DecidableEq Q] in
theorem present_separator_ne_zero (hz : zero∉C.Alphabet) (hzs : zero≠sep)
    {u v : List A} (hu : q u≠none) (hv : q v≠none) :
    present T (C.encode u++sep::C.encode v)≠present T [zero] := by
  intro he
  have hn := (present_eq_iff T wt good stable _ _).mp he
  rw [normal_separator T wt good stable C wf q zero sep hshort hiso hstatic hc hi hzero hs hu hv] at hn
  obtain ⟨rs,hrs,_⟩ := good 1
  have hz0 : normal T [zero]=[zero] := normal_eq_self T wt good stable hrs
    (irreducible_of_short (fun p hp => hshort 1 rs hrs p hp))
  rw [hz0] at hn
  have hm : zero∈C.encode (Canonical.least wf q u)++sep::C.encode (Canonical.least wf q v) := by
    rw [hn]; simp
  simp only [List.mem_append,List.mem_cons] at hm
  rcases hm with hm | hm | hm
  · exact hz (C.mem_alphabet hm)
  · exact hzs hm
  · exact hz (C.mem_alphabet hm)
end Quotient

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform
variable {A B : Type*}

/-- The finite word ball over an explicit finite support. -/
def words (letters : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n+1 => [] :: letters.flatMap (fun a => (words letters n).map (a::·))

@[simp] theorem mem_words (letters : List A) (n : ℕ) (w : List A) :
    w∈words letters n ↔ w.length≤n ∧ ∀ a∈w,a∈letters := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      rw [words,List.mem_cons]
      constructor
      · rintro (he | h)
        · cases he
        · obtain ⟨b,hb,h⟩ := List.mem_flatMap.mp h
          obtain ⟨v,hv,he⟩ := List.mem_map.mp h
          obtain ⟨rfl,rfl⟩ := List.cons.inj he
          obtain ⟨hlen,hs⟩ := (ih v).mp hv
          exact ⟨by simpa using Nat.succ_le_succ hlen,by simpa [List.mem_cons] using And.intro hb hs⟩
      · rintro ⟨hlen,hs⟩
        right
        refine List.mem_flatMap.mpr ⟨a,hs a List.mem_cons_self,List.mem_map.mpr ⟨w,?_,rfl⟩⟩
        exact (ih w).mpr ⟨by simpa using hlen,fun b hb => hs b (List.mem_cons_of_mem _ hb)⟩

theorem words_map (i : A → B) (ls : List A) (n : ℕ) :
    words (ls.map i) n = (words ls n).map (List.map i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [words,ih,List.map_cons,List.map_nil,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

 theorem words_specialize [Fintype A] (n : ℕ) : words (Static.letters A) n=Static.words A n := by
  induction n <;> simp_all only [words,Static.words]

 theorem primrec_words [Primcodable A] : Primrec₂ (@words A) := by
  exact (Primrec.nat_rec (Primrec.const [[]])
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap Primrec.fst
        (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
            fun ls n => by induction n <;> simp_all [words]

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*} [Primcodable X] [Primcodable A] [Primcodable B]

/-- Finite traversal of a total computable family is a computable list map. -/
theorem computable_map_parameter {f : X → A → B} (hf : Computable₂ f) :
    Computable₂ (fun x (l : List A) => l.map (f x)) := by
  apply (partrec_traverse_parameter hf.partrec₂).of_eq_tot
  intro p
  exact Bootstrap.Search.traverse_map _ _ _ (fun a _ => Part.mem_some _)
end Effect

namespace Bootstrap.Canonical
variable {A Q : Type*} [Fintype A] [Primcodable A]
  {r : A → A → Prop} [DecidableRel (List.Shortlex r)] [Std.Trichotomous r]
  (wf : WellFounded r) (q : List A → Q)

/-- Canonical representatives do not require a coding of the semantic class
    type. Only its word-equivalence test must be algorithmic. -/
theorem computable_least (hr : PrimrecRel (List.Shortlex r))
    (hq : ComputablePred (fun p : List A × List A => q p.1=q p.2)) : Computable (least wf q) := by
  classical
  let e (w v : List A) : Option Bool := some (decide (q v=q w))
  have he : Computable₂ e := (Primrec.option_some.to_comp.comp (hq.decide.comp (Computable.snd.pair Computable.fst))).to₂
  let ps (w : List A) := (Static.words A w.length).map (fun v => (v,e w v))
  have hp : Computable ps :=
    (Effect.computable_map_parameter (Computable.snd.pair he).to₂).comp
      Computable.id (Search.primrec_words.to_comp.comp Primrec.list_length.to_comp)
  have hc : Computable (fun w => pick (r:=r) (ps w) w (some true)) :=
    ((Search.primrec_pick (Q:=Bool) hr Primrec.snd Primrec.fst (Primrec.const (some true))).to_comp.comp
      (Computable.id.pair hp))
  apply hc.of_eq
  intro w
  have hew : e w w=some true := by simp [e]
  have heq : least wf (e w) w=least wf q w := by
    apply (eq_least_iff wf q).mpr
    refine ⟨least_length wf (e w) w,?_,?_⟩
    · have hh := least_class wf (e w) w
      simpa [e] using hh
    · intro v hv hh
      apply least_min wf (e w) hv
      simp [e,hh]
  rw [← hew]
  rw [pick_eq_least wf (e w) (fun p hp => by
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    rfl)]
  · exact heq
  · apply List.mem_map.mpr
    refine ⟨least wf (e w) w,(Static.mem_words _ _).mpr (least_length wf (e w) w),?_⟩
    simp only [Prod.mk.injEq,true_and]
    exact least_class wf (e w) w

omit [Fintype A] [Primcodable A] [DecidableRel (List.Shortlex r)] in
/-- Equality of computed representatives is exactly equality in the semantic
    quotient, not merely equality of a chosen noncanonical encoding. -/
theorem least_eq_iff {u v : List A} : least wf q u=least wf q v ↔ q u=q v := by
  constructor
  · intro h
    exact (least_class wf q u).symm.trans ((congrArg q h).trans (least_class wf q v))
  · exact least_congr wf q

end Bootstrap.Canonical

namespace WordProblem
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)

/-- The original word-problem algorithm gives a genuine two-word comparison. -/
theorem computable_word_equiv (h : ComputablePred (fun w : Word n => evalWord s w=1)) :
    ComputablePred (fun p : Word n × Word n => evalWord s p.1=evalWord s p.2) := by
  classical
  have hc : ComputablePred (fun p : Word n × Word n =>
      evalWord s (p.1 ++ FreeGroup.invRev p.2)=1) :=
    ⟨inferInstance,h.decide.comp (Primrec.list_append.comp Primrec.fst
      ((invRev_primrec n).comp Primrec.snd)).to_comp⟩
  exact hc.of_eq (fun p => by rw [evalWord_append,evalWord_invRev,mul_inv_eq_one])

end WordProblem
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.WordProblem

def letterRel (n : ℕ) (a b : Fin n × Bool) : Prop := Encodable.encode a<Encodable.encode b

local instance (n : ℕ) : DecidableRel (letterRel n) := fun _ _ => inferInstanceAs (Decidable (_ < _))
local instance (n : ℕ) : Std.Trichotomous (letterRel n) := ⟨fun a b hab hba => by
  apply Encodable.encode_injective
  change ¬Encodable.encode a<Encodable.encode b at hab
  change ¬Encodable.encode b<Encodable.encode a at hba
  omega⟩

 theorem letterRel_wf (n : ℕ) : WellFounded (letterRel n) := InvImage.wf Encodable.encode Nat.lt_wfRel.wf

 theorem primrec_letterShortlex (n : ℕ) : PrimrecRel (List.Shortlex (letterRel n)) := by
  let ord : LinearOrder (Fin n × Bool) := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact @Bootstrap.Search.primrec_shortlex _ _ _ ord ⟨inferInstance,Primrec.dom_finite _⟩

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)
noncomputable def testedClass : Word n → Word n :=
  Bootstrap.Canonical.least (letterRel_wf n) (evalWord s)

 theorem computable_testedClass (h : ComputablePred (fun w : Word n => evalWord s w=1)) :
    Computable (testedClass s) := by
  classical
  exact Bootstrap.Canonical.computable_least (letterRel_wf n) (evalWord s)
    (primrec_letterShortlex n) (computable_word_equiv s h)

 theorem testedClass_eq_iff (u v : Word n) : testedClass s u=testedClass s v ↔ evalWord s u=evalWord s v := by
  classical
  exact Bootstrap.Canonical.least_eq_iff _ _

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
