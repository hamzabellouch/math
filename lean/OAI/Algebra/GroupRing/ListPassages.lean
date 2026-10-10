import Mathlib
import OAI.Algebra.GroupRing.TypeWeights
import OAI.Algebra.GroupRing.PathIncidences

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ListPassages
open scoped Classical BigOperators

lemma rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val+1=n then 0 else i.val+1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [coe_finRotate]
    have h : i=Fin.last n ↔ i.val+1=n+1 := by
      constructor
      · intro he; subst i; rfl
      · intro he; apply Fin.ext; simp only [Fin.val_last]; omega
    simp only [h]

variable {D : Type*} (p : List D) (hp : p ≠ [])

def start : Fin p.length := ⟨0,List.length_pos_iff.mpr hp⟩

def cut (cyclic : Bool) : Option (Fin p.length) :=
  if cyclic then none else some (start p hp)

lemma last_mem (i : Fin p.length) (hi : i.val+1=p.length) :
    p.get i ∈ p.getLast? := by
  have hp : p≠[] := List.length_pos_iff.mp (Nat.zero_lt_of_lt i.isLt)
  rw [List.getLast?_eq_some_getLast hp]
  apply Option.mem_def.mpr
  congr 1
  rw [List.getLast_eq_getElem,List.get_eq_getElem]
  congr 1
  omega

lemma first_mem (i : Fin p.length) (hi : i.val=0) : p.get i ∈ p.head? := by
  cases p with
  | nil => exact Fin.elim0 i
  | cons a p =>
    have he : i=⟨0,by simp⟩ := Fin.ext hi
    subst i
    rfl

/-- The cyclic successor on actual list occurrences pairs exactly the internal
passages, plus the closing passage precisely when the path is cyclic. -/
theorem passage {R : D → D → Prop} (hc : p.IsChain R) (cyclic : Bool)
    (hclose : cyclic=true → ∀ᵉ (x∈p.getLast?) (y∈p.head?),R x y)
    (i : Fin p.length) (hcut : cut p hp cyclic ≠ some (finRotate p.length i)) :
    R (p.get i) (p.get (finRotate p.length i)) := by
  by_cases hi : i.val+1=p.length
  · have hr : (finRotate p.length i).val=0 := by rw [rotate_val,ite_eq_left hi]
    have hcyc : cyclic=true := by
      cases cyclic
      · exfalso
        apply hcut
        apply congrArg some
        apply Fin.ext
        exact hr.symm
      · rfl
    exact hclose hcyc _ (last_mem p i hi) _ (first_mem p _ hr)
  · have hir : i.val+1<p.length := by omega
    have hr : (finRotate p.length i).val=i.val+1 := by rw [rotate_val,ite_eq_right hi]
    have h := (List.isChain_iff_getElem.mp hc) i.val hir
    simpa only [List.get_eq_getElem,hr] using h

end TorsionFreeZeroDivisors.ListPassages
namespace TorsionFreeZeroDivisors.ChainPathTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open WeightedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "w" => word Γ mark h2

omit [Fintype D] in
lemma outWord_head {k : ℕ} (p : WeightedMoore.Chain D k) :
    (SuppressedMoore.outWord p).head?=some (WeightedMoore.head p) := by
  cases k <;> rfl

lemma word_head (d : B) : (w d).head?=some d.val := by
  rw [word,outWord_head,head_iterChain]

lemma word_last (d : B) : (w d).getLast?=some (Γ.reverse ((S).reverse d).val) := by
  rw [word,outWord_last]
  apply congrArg some
  exact Γ.reverse_reverse.injective (by rw [chain_last,Γ.reverse_reverse])

lemma word_ne_nil (d : B) : w d ≠ [] := by
  intro he
  have h := word_length Γ mark h2 d
  rw [he,List.length_nil] at h
  have hp := chainLength_pos Γ mark h2 d
  omega

/-- A genuine reduced original path transports to a genuine reduced path in
its suppressed graph. Adjacency is read from the actual last/first darts;
no graph path property is imposed on the decomposition as a hypothesis. -/
theorem isChain (ds : List B)
    (hp : (ds.flatMap w).IsChain (PortWalk.step Γ.origin Γ.reverse)) :
    ds.IsChain (PortWalk.step (S).origin (S).reverse) := by
  have hn : [] ∉ ds.map w := by
    intro he
    obtain ⟨d,_,hd⟩ := List.mem_map.mp he
    exact word_ne_nil Γ mark h2 d hd
  have hc := (List.isChain_flatten hn).mp hp
  have hc' := (List.isChain_map w).mp hc.2
  apply hc'.imp
  intro a b hab
  have he := hab _ (word_last Γ mark h2 a) _ (word_head Γ mark h2 b)
  simp only [PortWalk.step] at he
  rw [Γ.reverse_reverse] at he
  refine ⟨he.1,?_⟩
  intro hb
  exact he.2 (congrArg Subtype.val hb)

lemma flatMap_head (ds : List B) :
    (ds.flatMap w).head? = ds.head?.map Subtype.val := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    rw [List.flatMap_cons,List.head?_append_of_ne_nil _ (word_ne_nil Γ mark h2 d)]
    exact word_head Γ mark h2 d

lemma flatMap_last (ds : List B) :
    (ds.flatMap w).getLast? = ds.getLast?.map (fun d => Γ.reverse ((S).reverse d).val) := by
  induction ds using List.reverseRecOn with
  | nil => rfl
  | append_singleton ds d _ih =>
    simp only [List.flatMap_append,List.flatMap_singleton]
    rw [List.getLast?_append_of_ne_nil _ (word_ne_nil Γ mark h2 d)]
    simp only [List.getLast?_concat,Option.map_some,word_last]

/-- The closing passage of a cyclically immersed path survives suppression. -/
theorem closing (ds : List B)
    (hc : ∀ᵉ (x∈(ds.flatMap w).getLast?) (y∈(ds.flatMap w).head?),
      PortWalk.step Γ.origin Γ.reverse x y) :
    ∀ᵉ (a∈ds.getLast?) (b∈ds.head?),PortWalk.step (S).origin (S).reverse a b := by
  intro a ha b hb
  have hl : Γ.reverse ((S).reverse a).val ∈ (ds.flatMap w).getLast? := by
    rw [flatMap_last]
    exact Option.mem_map_of_mem _ ha
  have hh : b.val ∈ (ds.flatMap w).head? := by
    rw [flatMap_head]
    exact Option.mem_map_of_mem _ hb
  have he := hc _ hl _ hh
  simp only [PortWalk.step] at he
  rw [Γ.reverse_reverse] at he
  exact ⟨he.1,fun h => he.2 (congrArg Subtype.val h)⟩

/-- The decomposition retains all reduced passages and both geometric
endpoints. Cyclic closing passages therefore also transport unchanged. -/
theorem decomposes (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hs : ∀ d∈p.head?,mark (Γ.origin d))
    (ht : ∀ d∈p.getLast?,mark (Γ.origin (Γ.reverse d))) :
    ∃ ds : List B, ds.flatMap w=p ∧
      ds.IsChain (PortWalk.step (S).origin (S).reverse) ∧
      ds.head?.map Subtype.val=p.head? ∧
      ds.getLast?.map (fun d => Γ.reverse ((S).reverse d).val)=p.getLast? := by
  obtain ⟨ds,hd⟩ := path_decomposes Γ mark h2 p hp hs ht
  refine ⟨ds,hd,isChain Γ mark h2 ds (hd.symm ▸ hp),?_,?_⟩
  · rw [←flatMap_head,hd]
  · rw [←flatMap_last,hd]

end TorsionFreeZeroDivisors.ChainPathTransport
namespace TorsionFreeZeroDivisors.ListStageExponents
open scoped Classical BigOperators
open PortSubdivision WeightedMoore StageSubgraphs
variable {V D I : Type*} [Fintype V] [Fintype D] [Fintype I]
    (Γ : PortGraph V D) (p : I → List D) (hp : ∀ i,p i ≠ [])
    (cyclic : I → Bool)
    (hc : ∀ i,(p i).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(p i).getLast?) (y∈(p i).head?),
      PortWalk.step Γ.origin Γ.reverse x y)

abbrev edge (i : I) : Fin (p i).length → D := (p i).get
abbrev mult : D → ℕ := multiplicity Γ (edge p)

omit [Fintype D] in
theorem cut_count : (∑ i,if (ListPassages.cut (p i) (hp i) (cyclic i)).isSome then 1 else 0 : ℕ) =
    Fintype.card {i : I // cyclic i=false} := by
  rw [Fintype.card_subtype,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases cyclic i <;> simp [ListPassages.cut]

include hp hc hclose in
/-- The exact signed stage exponent of literal immersed paths, including a
root saving for each noncyclic interval only at the first stage. -/
theorem exponent_nonpos (M : ℕ) (hM : 0<M) (hm : ∀ d,mult Γ p d ≤ M) :
    (∑ j : Fin M, ((Fintype.card (ActiveV Γ (mult Γ p) j.val):ℤ)-
      (edges (stage Γ (mult Γ p) (multiplicity_reverse Γ (edge p)) j.val)).card-
      if j.val=0 then Fintype.card {i : I // cyclic i=false} else 0)) ≤ 0 := by
  have hv : ∀ i (e : Fin (p i).length),
      ListPassages.cut (p i) (hp i) (cyclic i) ≠ some (finRotate (p i).length e) →
      Γ.origin (edge p i (finRotate (p i).length e))=Γ.origin (Γ.reverse (edge p i e)) := by
    intro i e he
    exact (ListPassages.passage (p i) (hp i) (hc i) (cyclic i) (hclose i) e he).1.symm
  have hr : ∀ i (e : Fin (p i).length),
      ListPassages.cut (p i) (hp i) (cyclic i) ≠ some (finRotate (p i).length e) →
      edge p i (finRotate (p i).length e)≠Γ.reverse (edge p i e) := by
    intro i e he
    exact (ListPassages.passage (p i) (hp i) (hc i) (cyclic i) (hclose i) e he).2
  have h := family_exponent_nonpos Γ (edge p) (fun i => finRotate (p i).length)
    (fun i => ListPassages.cut (p i) (hp i) (cyclic i)) hv hr M hM hm
  rw [cut_count] at h
  exact h

end TorsionFreeZeroDivisors.ListStageExponents

/-! A choice of one direction for each unoriented edge of a finite port graph.
The reversal has no fixed points. No graph is assumed bipartite or loop-free. -/
namespace TorsionFreeZeroDivisors.InvolutionOrientation
open scoped Classical BigOperators
variable {D : Type*} [Fintype D] (σ : D → D)

def rank (d : D) : Fin (Fintype.card D) := Fintype.equivFin D d

def Chosen (d : D) : Prop := rank d < rank (σ d)
abbrev Representative := {d : D // Chosen σ d}

variable (hσ : Function.Involutive σ) (hne : ∀d,σ d≠d)

include hne in
lemma rank_ne (d : D) : rank d ≠ rank (σ d) := by
  intro h
  exact hne d ((Fintype.equivFin D).injective h).symm

include hσ hne

lemma chosen_or_reverse (d : D) : Chosen σ d ∨ Chosen σ (σ d) := by
  unfold Chosen
  rw [hσ]
  exact lt_or_gt_of_ne (rank_ne σ hne d)

lemma chosen_reverse_iff (d : D) : Chosen σ (σ d) ↔ ¬Chosen σ d := by
  unfold Chosen
  rw [hσ]
  exact ⟨fun h h' => (lt_asymm h h'),fun h => lt_of_le_of_ne (le_of_not_gt h) (rank_ne σ hne d).symm⟩

def orient (x : Representative σ × Bool) : D := if x.2 then σ x.1.val else x.1.val

lemma orient_injective : Function.Injective (orient σ) := by
  rintro ⟨⟨a,ha⟩,i⟩ ⟨⟨b,hb⟩,j⟩ he
  cases i <;> cases j
  · simp only [orient,Bool.false_eq_true,ite_false] at he
    cases he
    rfl
  · simp only [orient,Bool.false_eq_true,ite_false,ite_true] at he
    have hna := (chosen_reverse_iff σ hσ hne b).mp (he ▸ ha)
    exact (hna hb).elim
  · simp only [orient,Bool.false_eq_true,ite_false,ite_true] at he
    have hnb := (chosen_reverse_iff σ hσ hne a).mp (he.symm ▸ hb)
    exact (hnb ha).elim
  · simp only [orient,ite_true] at he
    have hab := hσ.injective he
    cases hab
    rfl

lemma orient_surjective : Function.Surjective (orient σ) := by
  intro d
  rcases chosen_or_reverse σ hσ hne d with hd|hd
  · exact ⟨(⟨d,hd⟩,false),rfl⟩
  · exact ⟨(⟨σ d,hd⟩,true),hσ d⟩

def equiv : Representative σ × Bool ≃ D :=
  Equiv.ofBijective (orient σ) ⟨orient_injective σ hσ hne,orient_surjective σ hσ hne⟩

@[simp] lemma equiv_false (c : Representative σ) : equiv σ hσ hne (c,false) = c.val := rfl
@[simp] lemma equiv_true (c : Representative σ) : equiv σ hσ hne (c,true) = σ c.val := rfl

lemma rep_card : 2*Fintype.card (Representative σ) = Fintype.card D := by
  have h := Fintype.card_congr (equiv σ hσ hne)
  simpa only [Fintype.card_prod,Fintype.card_bool,mul_comm] using h

lemma sum_invariant (f : D → ℕ) (hf : ∀d,f (σ d)=f d) :
    ∑d,f d = 2*∑c : Representative σ,f c.val := by
  rw [←Equiv.sum_comp (equiv σ hσ hne)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,equiv_true,equiv_false,hf]
  rw [Finset.sum_add_distrib]
  omega

end TorsionFreeZeroDivisors.InvolutionOrientation
namespace TorsionFreeZeroDivisors.ChainIsomorphism
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => InvolutionOrientation.Representative (PortGraph.reverse (suppressed Γ mark h2))
local notation "len" => chainLength Γ mark h2

abbrev Rep := R
abbrev repLength (c : R) := len c.val
abbrev Mark := {v : V // mark v}

def first (c : R) : Mark mark :=
  ⟨Γ.origin c.val.val,(turn_fixed_iff Γ.origin mark h2 _).mp c.val.property⟩
def last (c : R) : Mark mark :=
  ⟨Γ.origin ((S).reverse c.val).val,(turn_fixed_iff Γ.origin mark h2 _).mp ((S).reverse c.val).property⟩

local notation "P" => ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2)

def dartMap (d : ChainSubdivision.Dart (repLength Γ mark h2)) : D :=
  if d.2 then Γ.reverse (F^[d.1.2.val] d.1.1.val.val) else F^[d.1.2.val] d.1.1.val.val

lemma forward_mem (c : R) (i : Fin (len c.val)) :
    F^[i.val] c.val.val ∈ ChainPaths.word Γ mark h2 c.val :=
  (ChainPaths.mem_word_iff Γ mark h2 _ _).mpr ⟨i,rfl⟩

lemma dart_mem (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    dartMap Γ mark h2 d ∈ ChainPaths.word Γ mark h2
      (InvolutionOrientation.orient (S).reverse (d.1.1,d.2)) := by
  cases hb : d.2
  · simpa only [dartMap,InvolutionOrientation.orient,hb,Bool.false_eq_true,ite_false] using
      forward_mem Γ mark h2 d.1.1 d.1.2
  · simpa only [dartMap,InvolutionOrientation.orient,hb,ite_true] using
      ChainPaths.reverse_mem_word Γ mark h2 _ _ (forward_mem Γ mark h2 d.1.1 d.1.2)

lemma same_word {a b : B} {x : D} (ha : x∈ChainPaths.word Γ mark h2 a)
    (hb : x∈ChainPaths.word Γ mark h2 b) : a=b := by
  by_contra h
  exact ChainPaths.words_disjoint Γ mark h2 h ha hb

lemma dartMap_injective : Injective (dartMap Γ mark h2) := by
  rintro ⟨⟨a,i⟩,u⟩ ⟨⟨b,j⟩,v⟩ he
  have hw := same_word Γ mark h2 (dart_mem Γ mark h2 ((⟨a,i⟩),u))
    (he.symm ▸ dart_mem Γ mark h2 ((⟨b,j⟩),v))
  have hab := InvolutionOrientation.orient_injective (S).reverse (S).reverse_reverse (S).reverse_ne hw
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hab
  have hi : F^[i.val] a.val.val=F^[j.val] a.val.val := by
    cases u
    · exact he
    · exact Γ.reverse_reverse.injective he
  have hij := chain_dart_injective Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    (a₁ := ⟨a.val,i⟩) (a₂ := ⟨a.val,j⟩) hi
  have hij' : i=j := Fin.ext (congrArg (fun z => z.2.val) hij)
  cases hij'
  rfl

lemma dartMap_surjective (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : Surjective (dartMap Γ mark h2) := by
  intro x
  rcases hcovered x with ⟨b,i,hi⟩
  rcases InvolutionOrientation.chosen_or_reverse (S).reverse
    (S).reverse_reverse (S).reverse_ne b with hb|hb
  · exact ⟨(⟨⟨b,hb⟩,i⟩,false),hi⟩
  · have hx : x∈ChainPaths.word Γ mark h2 b :=
      (ChainPaths.mem_word_iff Γ mark h2 _ _).mpr ⟨i,hi⟩
    have hr := ChainPaths.reverse_mem_word Γ mark h2 b x hx
    rcases (ChainPaths.mem_word_iff Γ mark h2 _ _).mp hr with ⟨j,hj⟩
    refine ⟨(⟨⟨(S).reverse b,hb⟩,j⟩,true),?_⟩
    exact (congrArg Γ.reverse hj).trans (Γ.reverse_reverse x)

def dartEquiv (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : ChainSubdivision.Dart (repLength Γ mark h2) ≃ D :=
  Equiv.ofBijective (dartMap Γ mark h2)
    ⟨dartMap_injective Γ mark h2,dartMap_surjective Γ mark h2 hcovered⟩

lemma dartMap_reverse (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    dartMap Γ mark h2 ((P).reverse d)=Γ.reverse (dartMap Γ mark h2 d) := by
  cases hb : d.2 <;> simp only [ChainSubdivision.reverse,dartMap,hb,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,ite_false,ite_true]
  exact (Γ.reverse_reverse _).symm

def vertexMap : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) → V
  | .inl v => v.val
  | .inr ⟨c,i⟩ => Γ.origin (F^[i.val+1] c.val.val)

lemma internal_unmarked (v : ChainSubdivision.Interior (repLength Γ mark h2)) :
    ¬mark (vertexMap Γ mark h2 (.inr v)) := by
  intro hh
  have hf := (turn_fixed_iff Γ.origin mark h2 _).mpr hh
  have hi : v.2.val+1 < len v.1.val := by have h:=v.2.isLt; dsimp only [repLength] at h; omega
  exact no_internal_mark Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    v.1.val.val v.1.val.property (by omega : 0<v.2.val+1) hi hf

lemma origin_map (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    vertexMap Γ mark h2 ((P).origin d) = Γ.origin (dartMap Γ mark h2 d) := by
  rcases d with ⟨⟨c,i⟩,b⟩
  cases b
  · rw [ChainSubdivision.origin_forward]
    by_cases hz : i.val=0
    · simp only [ChainSubdivision.point,Fin.val_mk,hz,dite_eq_left,vertexMap,first,dartMap,
        Bool.false_eq_true,ite_false]
      rfl
    · have hl : i.val≠repLength Γ mark h2 c := Nat.ne_of_lt i.isLt
      simp only [ChainSubdivision.point,hz,hl,vertexMap,dartMap,
        Bool.false_eq_true,ite_false]
      change Γ.origin (F^[i.val-1+1] c.val.val) = Γ.origin (F^[i.val] c.val.val)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hz)]
  · rw [ChainSubdivision.origin_backward]
    have hz : i.val+1≠0 := by omega
    by_cases hl : i.val+1=repLength Γ mark h2 c
    · have hp : repLength Γ mark h2 c≠0 := Nat.ne_of_gt (chainLength_pos Γ mark h2 c.val)
      simp only [ChainSubdivision.point,Fin.val_mk,hl,hp,dite_eq_left,vertexMap,last,
        dartMap,ite_true]
      have hi : i.val=len c.val-1 := by change i.val+1=len c.val at hl; omega
      have he := chain_last Γ mark h2 c.val
      rw [last_iterChain] at he
      change Γ.origin ((S).reverse c.val).val = Γ.origin (Γ.reverse (F^[i.val] c.val.val))
      rw [hi,he]
    · simp only [ChainSubdivision.point,hz,hl,vertexMap,dartMap,ite_true]
      change Γ.origin (F^[i.val+1-1+1] c.val.val) = Γ.origin (Γ.reverse (F^[i.val] c.val.val))
      rw [Nat.add_sub_cancel,iterate_succ_apply']
      exact turn_origin Γ.origin mark h2 _

lemma original_two_ports (v : ChainSubdivision.Interior (repLength Γ mark h2))
    (d : D) (hd : Γ.origin d=vertexMap Γ mark h2 (.inr v)) :
    d=dartMap Γ mark h2 (ChainSubdivision.front (repLength Γ mark h2) v) ∨
    d=dartMap Γ mark h2 (ChainSubdivision.back (repLength Γ mark h2) v) := by
  let a := ChainSubdivision.front (repLength Γ mark h2) v
  let b := ChainSubdivision.back (repLength Γ mark h2) v
  have ha : Γ.origin (dartMap Γ mark h2 a)=vertexMap Γ mark h2 (.inr v) := by
    rw [←origin_map,ChainSubdivision.front_origin]
  have hb : Γ.origin (dartMap Γ mark h2 b)=vertexMap Γ mark h2 (.inr v) := by
    rw [←origin_map,ChainSubdivision.back_origin]
  by_cases hda : d=dartMap Γ mark h2 a
  · exact Or.inl hda
  · right
    have hba : dartMap Γ mark h2 b≠dartMap Γ mark h2 a := by
      intro hh
      exact ChainSubdivision.back_ne_front _ v (dartMap_injective Γ mark h2 hh)
    exact ((unique_other Γ.origin (dartMap Γ mark h2 a)
      (h2 _ (ha ▸ internal_unmarked Γ mark h2 v))).unique
        ⟨hd.trans ha.symm,hda⟩ ⟨hb.trans ha.symm,hba⟩)

lemma vertexMap_injective : Injective (vertexMap Γ mark h2) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext he)
    | inr b => exact (internal_unmarked Γ mark h2 b (he ▸ a.property)).elim
  | inr a =>
    cases b with
    | inl b => exact (internal_unmarked Γ mark h2 a (he.symm ▸ b.property)).elim
    | inr b =>
      have hb : Γ.origin (dartMap Γ mark h2 (ChainSubdivision.front (repLength Γ mark h2) b)) =
          vertexMap Γ mark h2 (.inr a) := by
        rw [←origin_map,ChainSubdivision.front_origin,he]
      rcases original_two_ports Γ mark h2 a _ hb with h|h
      · have hh := dartMap_injective Γ mark h2 h
        have h' := congrArg (fun d => (P).origin d) hh
        simpa only [ChainSubdivision.front_origin] using h'.symm
      · have hh := dartMap_injective Γ mark h2 h
        have h' := congrArg Prod.snd hh
        cases h'

lemma vertexMap_surjective (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : Surjective (vertexMap Γ mark h2) := by
  intro v
  by_cases hv : mark v
  · exact ⟨.inl ⟨v,hv⟩,rfl⟩
  · have hp : (out Γ.origin v).Nonempty := Finset.card_pos.mp (by rw [h2 v hv]; decide)
    obtain ⟨d,hd⟩ := hp
    obtain ⟨a,ha⟩ := dartMap_surjective Γ mark h2 hcovered d
    refine ⟨(P).origin a,?_⟩
    rw [origin_map,ha]
    exact (mem_out Γ.origin v d).mp hd

def vertexEquiv (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) ≃ V :=
  Equiv.ofBijective (vertexMap Γ mark h2)
    ⟨vertexMap_injective Γ mark h2,vertexMap_surjective Γ mark h2 hcovered⟩

/-- Replacing each actual maximal marked chain by a coordinate interval loses no
vertices, darts, loop chains, parallel chains or reversal information. -/
theorem subdivision_isomorphic (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) :
    ∃ (eV : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) ≃ V)
      (eD : ChainSubdivision.Dart (repLength Γ mark h2) ≃ D),
      (∀d,eV ((P).origin d)=Γ.origin (eD d)) ∧
      (∀d,eD ((P).reverse d)=Γ.reverse (eD d)) :=
  ⟨vertexEquiv Γ mark h2 hcovered,dartEquiv Γ mark h2 hcovered,
    origin_map Γ mark h2,dartMap_reverse Γ mark h2⟩

/-- Both orientations of every actual-image edge are retained exactly once. -/
theorem total_length
    (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d) :
    2 * ∑ c : Rep Γ mark h2, repLength Γ mark h2 c = Fintype.card D := by
  have he := Fintype.card_congr (dartEquiv Γ mark h2 hcovered)
  simpa only [ChainSubdivision.card_darts] using he

variable [Fintype V]
/-- The marked/interior count gives the precise signed stage vertex exponent. -/
theorem vertex_count
    (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d) :
    Fintype.card V + Fintype.card (Rep Γ mark h2) =
      Fintype.card (Mark mark) + ∑ c : Rep Γ mark h2, repLength Γ mark h2 c := by
  rw [←Fintype.card_congr (vertexEquiv Γ mark h2 hcovered)]
  exact ChainSubdivision.card_vertices _ (fun c => chainLength_pos Γ mark h2 c.val)

omit [Fintype V] in
/-- The needed coverage is furnished by the actual immersed path system, not
asserted as an additional structural property of a proposed pattern. -/
theorem actual_image_isomorphic {J : Type*} (paths : J → List D)
    (hpaths : ∀ j, (paths j).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hstarts : ∀ j d, d∈(paths j).head? → mark (Γ.origin d))
    (himage : ∀ d : D, ∃ j, d∈paths j ∨ Γ.reverse d∈paths j) :
    ∃ (eV : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) ≃ V)
      (eD : ChainSubdivision.Dart (repLength Γ mark h2) ≃ D),
      (∀ d,eV ((P).origin d)=Γ.origin (eD d)) ∧
      (∀ d,eD ((P).reverse d)=Γ.reverse (eD d)) :=
  subdivision_isomorphic Γ mark h2
    (ActualMarkedChains.actual_image_covered Γ mark h2 paths hpaths hstarts himage)

end TorsionFreeZeroDivisors.ChainIsomorphism

end

end OAI
