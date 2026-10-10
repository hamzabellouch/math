import Mathlib
import OAI.Algebra.GroupRing.SupportedImage
import OAI.Algebra.GroupRing.WeightedGirth

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] BoundedSystem.fP BoundedSystem.fE

namespace BoundedSystem
variable {Bnd K I rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : BoundedSystem Bnd K I rep r x y)
def data (hr : r∈samples rep) : AmbientPattern.Data Bnd K I rep where
  V := VA rep⊕VB rep
  D := DA rep⊕DB rep
  P := s.P
  E := s.E
  graph := graph rep r
  side := SumPort.side
  side_edge := SumPort.side_edge _ _
  paths := s.paths
  nonempty := s.nonempty
  root := s.root
  path_bound := s.path_bound
  comparison_bound := s.comparison_bound
  path_chain := s.path_chain
  cyclic_chain := s.cyclic_chain
  girth := weighted_girth rep r hr
  length_le := s.length_le
  length_ge := s.length_ge
  comparisons := s.comparisons
  lower := s.lower
  upper := s.upper
  lower_eq := s.lower_eq
  upper_eq := s.upper_eq
  lower_le := s.lower_le
  upper_le := s.upper_le
  reduced := s.reduced
  unpaired_le := s.unpaired_le
lemma event (hr : r∈samples rep) : (s.data hr).event x y r :=
  ⟨label rep,label_reverse rep r,immersed rep r,s.compatible,
    ⟨embeddingA rep r _ x s.rootA⟩,⟨embeddingB rep r _ y s.rootB⟩⟩
end BoundedSystem

/-- A literal finite typed graph on both sides, simultaneously with diameter,
large girth, and exclusion of every bounded nearly-paired rooted path system.
This is an actual-word theorem, not a condition on encoded surrogate patterns. -/
theorem exists_avoiding (Bnd K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in Filter.atTop,∀ (x : VA rep) (y : VB rep),
      ∃ r∈samples rep,GraphSample.Diameters rep r ∧
        IsEmpty (BoundedSystem Bnd K I rep r x y) := by
  filter_upwards [AmbientPattern.with_diameter Bnd K I hK hI] with rep hrep
  intro x y
  obtain ⟨r,hr,hd,ha⟩ := hrep x y
  refine ⟨r,hr,hd,⟨?_⟩⟩
  intro s
  exact ha (s.data hr) (s.event hr)
end TorsionFreeZeroDivisors.SampleGraph
namespace TorsionFreeZeroDivisors.ShortClosure

section
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)
    (allowed : D → Prop) (z : V)

/-- Terminal vertex of a literal path, including the empty path at `z`. -/
def endpoint (l : List D) : V := ((l.getLast?).map (fun d => Γ.origin (Γ.reverse d))).getD z

omit [Fintype V] [Fintype D] in
lemma endpoint_nil : endpoint Γ z []=z := rfl
omit [Fintype V] [Fintype D] in
lemma endpoint_append (l : List D) (d : D) : endpoint Γ z (l++[d])=Γ.origin (Γ.reverse d) := by
  simp [endpoint]

def choices (l : List D) : Finset D := Finset.univ.filter fun d =>
  allowed d ∧ Γ.origin d=endpoint Γ z l ∧ ∀ e∈l.getLast?,d≠Γ.reverse e

def walks : ℕ → Finset (List D)
  | 0 => {[]}
  | k+1 => (walks k).biUnion (fun l => (choices Γ allowed z l).image (fun d => l++[d]))

omit [Fintype V] in
lemma mem_walks_succ {k : ℕ} {l : List D} : l∈walks Γ allowed z (k+1) ↔
    ∃ p∈walks Γ allowed z k,∃ d∈choices Γ allowed z p,l=p++[d] := by
  simp only [walks,Finset.mem_biUnion,Finset.mem_image]
  aesop

omit [Fintype V] in
lemma length_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) : l.length=k := by
  induction k generalizing l with
  | zero => simpa only [List.length_nil] using congrArg List.length (Finset.mem_singleton.mp hl)
  | succ k ih =>
    obtain ⟨p,hp,d,_,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    simp only [List.length_append,List.length_singleton,ih hp]

omit [Fintype V] in
lemma chain_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) :
    l.IsChain (PortWalk.step Γ.origin Γ.reverse) := by
  induction k generalizing l with
  | zero => have := Finset.mem_singleton.mp hl; subst l; simp
  | succ k ih =>
    obtain ⟨p,hp,d,hd,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    have hd := (Finset.mem_filter.mp hd).2
    refine (ih hp).append (by simp) ?_
    intro e he f hf
    have hf : f=d := by simpa [eq_comm] using hf
    subst f
    refine ⟨?_,hd.2.2 e he⟩
    have he' : p.getLast?=some e := he
    simpa only [endpoint,he',Option.map_some,Option.getD_some] using hd.2.1.symm

omit [Fintype V] in
lemma allowed_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) :
    ∀ d∈l,allowed d := by
  induction k generalizing l with
  | zero => have := Finset.mem_singleton.mp hl; subst l; simp
  | succ k ih =>
    obtain ⟨p,hp,e,he,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih hp d hd
    · have hde : d=e := by simpa [eq_comm] using hd
      subst d
      exact (Finset.mem_filter.mp he).2.1

omit [Fintype V] in
lemma head_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) :
    ∀ d∈l.head?,Γ.origin d=z := by
  induction k generalizing l with
  | zero => have := Finset.mem_singleton.mp hl; subst l; simp
  | succ k ih =>
    obtain ⟨p,hp,e,he,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    intro d hd
    cases p with
    | nil =>
      have hde : d=e := by simpa [eq_comm] using hd
      subst d
      exact (Finset.mem_filter.mp he).2.2.1
    | cons f p =>
      have hdf : d=f := by simpa [eq_comm] using hd
      subst d
      exact ih hp f (by simp)

omit [Fintype V] in
lemma choices_card (l : List D) (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    2≤(choices Γ allowed z l).card := by
  let s := Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=endpoint Γ z l)
  cases he : l.getLast? with
  | none =>
    have hh : choices Γ allowed z l=s := by ext d; simp [choices,s,he]
    rw [hh]
    exact (by omega : 2≤3).trans (hdeg _)
  | some e =>
    have hh : choices Γ allowed z l=s.erase (Γ.reverse e) := by
      ext d
      simp only [choices,s,Finset.mem_filter,Finset.mem_univ,true_and,he,
        Option.mem_some_iff,Finset.mem_erase]
      constructor
      · rintro ⟨ha,ho,hh⟩
        exact ⟨hh e rfl,ha,ho⟩
      · rintro ⟨hh,ha,ho⟩
        exact ⟨ha,ho,fun f hf => hf ▸ hh⟩
    rw [hh]
    have hc3 : s.card ≤ (s.erase (Γ.reverse e)).card+1 := by
      calc
        _ ≤ (insert (Γ.reverse e) (s.erase (Γ.reverse e))).card := Finset.card_le_card (by intro d hd; by_cases h : d=Γ.reverse e <;> simp_all)
        _ ≤ _ := Finset.card_insert_le _ _
    have hc' := hdeg (endpoint Γ z l)
    change 3 ≤ s.card at hc'
    omega

omit [Fintype V] in
lemma card_walks_succ (k : ℕ) (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    2*(walks Γ allowed z k).card≤(walks Γ allowed z (k+1)).card := by
  rw [walks,Finset.card_biUnion]
  · calc
      _ = ∑ _l∈walks Γ allowed z k,2 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro l _
        rw [Finset.card_image_of_injective _ (by intro d e h; simpa using (List.append_cancel_left h))]
        exact choices_card Γ allowed z l hdeg
  · intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro l hl hl'
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hl
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hl'
    have hh := List.append_inj (hd.trans he.symm) ((length_mem Γ allowed z hp).trans (length_mem Γ allowed z hq).symm)
    exact hpq hh.1

omit [Fintype V] in
lemma card_walks (k : ℕ) (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    2^k≤(walks Γ allowed z k).card := by
  induction k with
  | zero => simp [walks]
  | succ k ih =>
    calc
      _ = 2*2^k := by rw [pow_succ]; omega
      _ ≤ 2*(walks Γ allowed z k).card := Nat.mul_le_mul_left 2 ih
      _ ≤ _ := card_walks_succ Γ allowed z k hdeg
 
/-- Collision of equal-length nonbacktracking paths, before any cancellation. -/
def Collision (k : ℕ) : Prop :=
  ∃ p∈walks Γ allowed z k,∃ q∈walks Γ allowed z k,p≠q ∧ endpoint Γ z p=endpoint Γ z q

lemma collision_exists (k : ℕ) (hk : Fintype.card V<2^k)
    (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    Collision Γ allowed z k := by
  apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t:=Finset.univ) (f:=endpoint Γ z)
  · simpa only [Finset.card_univ] using hk.trans_le (card_walks Γ allowed z k hdeg)
  · intro p _
    exact Finset.mem_univ _

omit [Fintype V] [Fintype D] in
lemma chain_reverse {l : List D} (hl : l.IsChain (PortWalk.step Γ.origin Γ.reverse)) :
    (l.reverse.map Γ.reverse).IsChain (PortWalk.step Γ.origin Γ.reverse) := by
  rw [List.isChain_map,List.isChain_reverse]
  apply hl.imp
  intro a b hab
  refine ⟨?_,?_⟩
  · simpa only [PortWalk.step,PortGraph.reverse_reverse_apply] using hab.1.symm
  · intro hh
    apply hab.2
    simpa only [PortGraph.reverse_reverse_apply] using hh.symm

/-- A based reduced loop with excluded darts never used. No cyclic reduction at
its base is asserted or needed. Least collision length avoids common suffixes. -/
theorem based_loop (k : ℕ) (hk : Fintype.card V<2^k)
    (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card)
    (hsymm : ∀ d,allowed d → allowed (Γ.reverse d)) :
    ∃ l : List D,l≠[] ∧ l.length≤2*k ∧
      l.IsChain (PortWalk.step Γ.origin Γ.reverse) ∧
      (∀ d∈l,allowed d) ∧ (∀ d∈l.head?,Γ.origin d=z) ∧ endpoint Γ z l=z := by
  have H : ∃ m,Collision Γ allowed z m := ⟨k,collision_exists Γ allowed z k hk hdeg⟩
  let m := Nat.find H
  have hmle : m≤k := Nat.find_min' H (collision_exists Γ allowed z k hk hdeg)
  obtain ⟨p,hp,q,hq,hpq,hep⟩ := Nat.find_spec H
  have hmpos : 0 < m := by
    by_contra hn
    have hm0 : m=0 := by omega
    change p∈walks Γ allowed z m at hp
    change q∈walks Γ allowed z m at hq
    rw [hm0] at hp hq
    exact hpq ((Finset.mem_singleton.mp hp).trans (Finset.mem_singleton.mp hq).symm)
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  change p∈walks Γ allowed z m at hp
  change q∈walks Γ allowed z m at hq
  rw [hj] at hp hq
  obtain ⟨p',hp',d,hd,hpd⟩ := (mem_walks_succ Γ allowed z).mp hp
  obtain ⟨q',hq',e,he,hqe⟩ := (mem_walks_succ Γ allowed z).mp hq
  have hde : d≠e := by
    intro hde
    have hc : Collision Γ allowed z j := by
      refine ⟨p',hp',q',hq',?_,?_⟩
      · intro heq
        apply hpq
        simp only [hpd,hqe,heq,hde]
      · exact (Finset.mem_filter.mp hd).2.2.1.symm.trans
          (hde ▸ (Finset.mem_filter.mp he).2.2.1)
    exact Nat.find_min H (by change j < m; omega) hc
  have hpne : p≠[] := by
    intro hh
    have hh' := length_mem Γ allowed z hp
    simp only [hh,List.length_nil] at hh'
    omega
  have hqne : q≠[] := by
    intro hh
    have hh' := length_mem Γ allowed z hq
    simp only [hh,List.length_nil] at hh'
    omega
  refine ⟨p++q.reverse.map Γ.reverse,?_,?_,?_,?_,?_,?_⟩
  · intro hh
    exact hpne (List.append_eq_nil_iff.mp hh).1
  · simp only [List.length_append,List.length_map,List.length_reverse,
      length_mem Γ allowed z hp,length_mem Γ allowed z hq]
    omega
  · apply (chain_mem Γ allowed z hp).append (chain_reverse Γ (chain_mem Γ allowed z hq))
    intro x hx y hy
    have hxd : x=d := by simpa only [hpd,List.getLast?_append,List.getLast?_singleton,
      Option.some_or,Option.some.injEq] using hx.symm
    have hye : y=Γ.reverse e := by
      simpa only [hqe,List.head?_map,List.head?_reverse,List.getLast?_append,
        List.getLast?_singleton,Option.some_or,Option.map_some,Option.some.injEq] using hy.symm
    subst x; subst y
    refine ⟨?_,fun h => hde (Γ.reverse_reverse.injective h).symm⟩
    simpa only [hpd,hqe,endpoint_append] using hep
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact allowed_mem Γ allowed z hp x hx
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact hsymm y (allowed_mem Γ allowed z hq y (List.mem_reverse.mp hy))
  · intro x hx
    apply head_mem Γ allowed z hp x
    cases p with
    | nil => exact (hpne rfl).elim
    | cons a p => simpa using hx
  · cases hqq : q with
    | nil => exact (hqne hqq).elim
    | cons a q' =>
      simp only [List.reverse_cons,List.map_append,List.map_singleton,←List.append_assoc,endpoint_append,
        PortGraph.reverse_reverse_apply]
      exact head_mem Γ allowed z (hqq ▸ hq) a (by simp)

/-- A logarithmic loop bound, valid even before excluding loops and parallel edges. -/
theorem logarithmic_based_loop
    (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card)
    (hsymm : ∀ d,allowed d → allowed (Γ.reverse d)) :
    ∃ l : List D,l≠[] ∧ l.length≤2*(Nat.log 2 (Fintype.card V)+1) ∧
      l.IsChain (PortWalk.step Γ.origin Γ.reverse) ∧
      (∀ d∈l,allowed d) ∧ (∀ d∈l.head?,Γ.origin d=z) ∧ endpoint Γ z l=z :=
  based_loop Γ allowed z _ (Nat.lt_pow_succ_log_self (by decide) _) hdeg hsymm

end
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

structure ReducedPath (a b : V) (l : List D) : Prop where
  chain : l.IsChain (PortWalk.step Γ.origin Γ.reverse)
  start : ∀ d∈l.head?,Γ.origin d=a
  finish : endpoint Γ a l=b

lemma endpoint_append_list (a : V) (p q : List D) :
    endpoint Γ a (p++q)=endpoint Γ (endpoint Γ a p) q := by
  simp only [endpoint,List.getLast?_append]
  cases p.getLast? <;> cases q.getLast? <;> rfl

namespace ReducedPath
variable {Γ} {a b c : V} {p q : List D}
lemma nil_iff (h : ReducedPath Γ a b []) : a=b := h.finish
lemma last (h : ReducedPath Γ a b p) {d : D} (hd : d∈p.getLast?) : Γ.origin (Γ.reverse d)=b := by
  have hd : p.getLast?=some d := hd
  simpa only [endpoint,hd,Option.map_some,Option.getD_some] using h.finish

lemma append (hp : ReducedPath Γ a b p) (hq : ReducedPath Γ b c q)
    (hb : ∀ᵉ (x∈p.getLast?) (y∈q.head?),y≠Γ.reverse x) :
    ReducedPath Γ a c (p++q) where
  chain := hp.chain.append hq.chain fun x hx y hy => ⟨(hp.last hx).trans (hq.start y hy).symm,hb x hx y hy⟩
  start := by
    cases p with
    | nil =>
      have hab : a=b := hp.nil_iff
      intro d hd
      simpa only [List.nil_append,hab] using hq.start d hd
    | cons d p =>
      intro e he
      exact hp.start e (by simpa using he)
  finish := by rw [endpoint_append_list,hp.finish]; exact hq.finish

lemma cyclic_join (hp : ReducedPath Γ a a p)
    (hb : ∀ᵉ (x∈p.getLast?) (y∈p.head?),y≠Γ.reverse x) :
    ∀ᵉ (x∈p.getLast?) (y∈p.head?),PortWalk.step Γ.origin Γ.reverse x y := by
  intro x hx y hy
  exact ⟨(hp.last hx).trans (hp.start y hy).symm,hb x hx y hy⟩
end ReducedPath

/-- Excluding an undirected edge means excluding both of its darts. -/
def forbidden (d e : D) : Finset D := {d,Γ.reverse d,e,Γ.reverse e}
def avoids (d e x : D) : Prop := x∉forbidden Γ d e
lemma avoids_symm (d e x : D) (hx : avoids Γ d e x) : avoids Γ d e (Γ.reverse x) := by
  simp only [avoids,forbidden,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  rcases not_or.mp hx with ⟨h₁,hx⟩
  rcases not_or.mp hx with ⟨h₂,hx⟩
  rcases not_or.mp hx with ⟨h₃,h₄⟩
  intro hx
  rcases hx with hx|hx|hx|hx
  · exact h₂ (by simpa using congrArg Γ.reverse hx)
  · exact h₁ (Γ.reverse_reverse.injective hx)
  · exact h₄ (by simpa using congrArg Γ.reverse hx)
  · exact h₃ (Γ.reverse_reverse.injective hx)
lemma avoids_left (d e x : D) (hx : avoids Γ d e x) : x≠d ∧ x≠Γ.reverse d := by
  have hx : x≠d ∧ x≠Γ.reverse d ∧ x≠e ∧ x≠Γ.reverse e := by
    simpa only [avoids,forbidden,Finset.mem_insert,Finset.mem_singleton,not_or] using hx
  exact ⟨hx.1,hx.2.1⟩
lemma avoids_right (d e x : D) (hx : avoids Γ d e x) : x≠e ∧ x≠Γ.reverse e := by
  have hx : x≠d ∧ x≠Γ.reverse d ∧ x≠e ∧ x≠Γ.reverse e := by
    simpa only [avoids,forbidden,Finset.mem_insert,Finset.mem_singleton,not_or] using hx
  exact hx.2.2

variable [Fintype V] [Fintype D]
omit [Fintype V] in
lemma avoiding_degree (d e : D)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card) :
    ∀ v,3≤(Finset.univ.filter (fun x => avoids Γ d e x ∧ Γ.origin x=v)).card := by
  intro v
  have hsub : Finset.univ.filter (fun x : D => Γ.origin x=v) ⊆
      Finset.univ.filter (fun x => avoids Γ d e x ∧ Γ.origin x=v) ∪ forbidden Γ d e := by
    intro x hx
    have hv := (Finset.mem_filter.mp hx).2
    by_cases hb : x∈forbidden Γ d e
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hv⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hf : (forbidden Γ d e).card≤4 := by
    unfold forbidden
    calc
      _ ≤ ({Γ.reverse d,e,Γ.reverse e}:Finset D).card+1 := Finset.card_insert_le _ _
      _ ≤ ({e,Γ.reverse e}:Finset D).card+2 := by have := Finset.card_insert_le (Γ.reverse d) ({e,Γ.reverse e}:Finset D); omega
      _ ≤ ({Γ.reverse e}:Finset D).card+3 := by have := Finset.card_insert_le e ({Γ.reverse e}:Finset D); omega
      _ = 4 := by simp
  have hv := hdeg v
  omega

/-- Literal reduced based loops avoiding both prescribed unoriented edges. -/
lemma avoiding_loop (d e : D) (z : V)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card) :
    ∃ l : List D,l≠[] ∧ l.length≤2*(Nat.log 2 (Fintype.card V)+1) ∧
      ReducedPath Γ z z l ∧ ∀ x∈l,avoids Γ d e x := by
  obtain ⟨l,hn,hl,hc,ha,hs,he⟩ := logarithmic_based_loop Γ (avoids Γ d e) z
    (avoiding_degree Γ d e hdeg) (avoids_symm Γ d e)
  exact ⟨l,hn,hl,⟨hc,hs,he⟩,ha⟩

omit [Fintype D] in
lemma mem_head_eq {l : List D} (hn : l≠[]) {x : D} (hx : x∈l.head?) : x=l.head hn := by
  have h := List.head?_eq_some_head hn
  rw [h] at hx
  exact Option.some.inj hx.symm
omit [Fintype D] in
lemma mem_last_eq {l : List D} (hn : l≠[]) {x : D} (hx : x∈l.getLast?) : x=l.getLast hn := by
  have h := List.getLast?_eq_some_getLast hn
  rw [h] at hx
  exact Option.some.inj hx.symm

/-- Short closure, before the uniform logarithmic-to-L bound.
Only a reduced return path is used; its length need not be minimal. -/
theorem extend_of_return {a b : V} {p q : List D}
    (hp : ReducedPath Γ a b p) (hpn : p≠[]) (hq : ReducedPath Γ b a q)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card) :
    ∃ t : List D,t.length≤q.length+4*(Nat.log 2 (Fintype.card V)+1) ∧
      ReducedPath Γ a a (p++t) ∧
      ∀ᵉ (x∈(p++t).getLast?) (y∈(p++t).head?),PortWalk.step Γ.origin Γ.reverse x y := by
  by_cases hqn : q=[]
  · subst q
    have hba : b=a := hq.nil_iff
    subst b
    obtain ⟨j,hjn,hjl,hj,ha⟩ := avoiding_loop Γ (p.getLast hpn) (p.head hpn) a hdeg
    have hjp : ReducedPath Γ a a (p++j) := hp.append hj (by
      intro x hx y hy
      have hx := mem_last_eq hpn hx
      subst x
      exact (avoids_left Γ _ _ _ (ha y (List.mem_of_mem_head? hy))).2)
    refine ⟨j,?_,hjp,hjp.cyclic_join ?_⟩
    · simp only [List.length_nil,zero_add]
      omega
    · intro x hx y hy
      rw [List.getLast?_append_of_ne_nil _ hjn] at hx
      rw [List.head?_append_of_ne_nil _ hpn] at hy
      have hy := mem_head_eq hpn hy
      subst y
      intro he
      have hx' := (avoids_right Γ _ _ _ (ha x (List.mem_of_mem_getLast? hx))).2
      exact hx' (by simpa using (congrArg Γ.reverse he).symm)
  · obtain ⟨jb,hjbn,hjbl,hjb,hab⟩ := avoiding_loop Γ (p.getLast hpn) (q.head hqn) b hdeg
    obtain ⟨ja,hjan,hjal,hja,haa⟩ := avoiding_loop Γ (q.getLast hqn) (p.head hpn) a hdeg
    have hpjb : ReducedPath Γ a b (p++jb) := hp.append hjb (by
      intro x hx y hy
      have hx := mem_last_eq hpn hx
      subst x
      exact (avoids_left Γ _ _ _ (hab y (List.mem_of_mem_head? hy))).2)
    have hpjbq : ReducedPath Γ a a ((p++jb)++q) := hpjb.append hq (by
      intro x hx y hy
      rw [List.getLast?_append_of_ne_nil _ hjbn] at hx
      have hy := mem_head_eq hqn hy
      subst y
      intro he
      have hx' := (avoids_right Γ _ _ _ (hab x (List.mem_of_mem_getLast? hx))).2
      exact hx' (by simpa using (congrArg Γ.reverse he).symm))
    have hall : ReducedPath Γ a a (((p++jb)++q)++ja) := hpjbq.append hja (by
      intro x hx y hy
      rw [List.getLast?_append_of_ne_nil _ hqn] at hx
      have hx := mem_last_eq hqn hx
      subst x
      exact (avoids_left Γ _ _ _ (haa y (List.mem_of_mem_head? hy))).2)
    refine ⟨jb++q++ja,?_,?_,?_⟩
    · simp only [List.length_append]
      omega
    · simpa only [List.append_assoc] using hall
    · have hcy := hall.cyclic_join (by
        intro x hx y hy
        rw [List.getLast?_append_of_ne_nil _ hjan] at hx
        rw [List.append_assoc,List.append_assoc,List.head?_append_of_ne_nil _ hpn] at hy
        have hy := mem_head_eq hpn hy
        subst y
        intro he
        have hx' := (avoids_right Γ _ _ _ (haa x (List.mem_of_mem_getLast? hx))).2
        exact hx' (by simpa using (congrArg Γ.reverse he).symm))
      simpa only [List.append_assoc] using hcy

end TorsionFreeZeroDivisors.ShortClosure

end

end OAI
