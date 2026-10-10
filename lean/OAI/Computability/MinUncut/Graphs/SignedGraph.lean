import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable

structure Demand (V : Type*) where
  left : V
  right : V
  equal : Bool

variable {V D : Type*}
abbrev Vertex (V D : Type*) := V ⊕ (D × Fin 3)

def failure (e : Demand V) (s : V → Bool) : ℕ :=
  if (s e.left == s e.right) = e.equal then 0 else 1

def mono (x y : Bool) : ℕ := if x=y then 1 else 0

def localCost (equal x y a b c : Bool) : ℕ :=
  mono x a + mono a b + if equal then mono b c+mono c y else mono b y

lemma local_lower (equal x y a b c : Bool) :
    (if (x==y) = equal then 0 else 1) ≤ localCost equal x y a b c := by
  cases equal <;> cases x <;> cases y <;> cases a <;> cases b <;> cases c <;>
    decide

lemma local_extension (equal x y : Bool) :
    localCost equal x y (!x) x (!x) = (if (x==y)=equal then 0 else 1) := by
  cases equal <;> cases x <;> cases y <;> decide

abbrev EdgeIndex (e : D → Demand V) := {p : D×Fin 4 // p.2.val < if (e p.1).equal then 4 else 3}

def ends (e : D → Demand V) (p : D×Fin 4) : Vertex V D × Vertex V D :=
  match p.2.val with
  | 0 => (.inl (e p.1).left,.inr (p.1,0))
  | 1 => (.inr (p.1,0),.inr (p.1,1))
  | 2 => if (e p.1).equal then (.inr (p.1,1),.inr (p.1,2))
      else (.inr (p.1,1),.inl (e p.1).right)
  | _ => (.inr (p.1,2),.inl (e p.1).right)

def edge (e : D → Demand V) (p : EdgeIndex e) : Sym2 (Vertex V D) :=
  s((ends e p.val).1,(ends e p.val).2)

lemma ends_ne (e : D → Demand V) (p : EdgeIndex e) :
    (ends e p.val).1 ≠ (ends e p.val).2 := by
  obtain ⟨⟨d,i⟩,hi⟩ := p
  fin_cases i <;> simp only [ends] <;> (try split_ifs) <;> simp

lemma edge_injective (e : D → Demand V) : Function.Injective (edge e) := by
  intro p q he
  obtain ⟨⟨d,i⟩,hi⟩ := p
  obtain ⟨⟨f,j⟩,hj⟩ := q
  apply Subtype.ext
  fin_cases i <;> fin_cases j <;>
    simp only [edge,ends] at he <;> (try split_ifs at he) <;>
    simp_all

variable [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]

def edgeSet (e : D → Demand V) : Finset (Sym2 (Vertex V D)) :=
  Finset.univ.image (edge e)

omit [Fintype V] in
lemma edgeSet_nondiag (e : D → Demand V) (z : Sym2 (Vertex V D)) (hz : z ∈ edgeSet e) :
    ¬ z.IsDiag := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hz
  simpa only [edge,Sym2.mk_isDiag_iff] using ends_ne e p

def graph (e : D → Demand V) : SimpleGraph (Vertex V D) where
  Adj x y := s(x,y) ∈ edgeSet e
  symm := ⟨by intro x y h; simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨by intro x hx; exact edgeSet_nondiag e s(x,x) hx (by simp)⟩

instance (e : D → Demand V) : DecidableRel (graph e).Adj := Classical.decRel _

lemma graph_edgeFinset (e : D → Demand V) : (graph e).edgeFinset=edgeSet e := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    simp only [SimpleGraph.edgeFinset, Set.mem_toFinset]
    rfl

def uncut (e : D → Demand V) (s : Vertex V D → Bool) : ℕ :=
  ∑ p : EdgeIndex e, mono (s (ends e p.val).1) (s (ends e p.val).2)

def totalFailure (e : D → Demand V) (s : V → Bool) : ℕ := ∑ d, failure (e d) s

def extend (e : D → Demand V) (s : V → Bool) : Vertex V D → Bool
  | .inl v => s v
  | .inr (d,i) => if i.val=1 then s (e d).left else !(s (e d).left)

omit [Fintype V] [DecidableEq V] [DecidableEq D] in
lemma uncut_locals (e : D → Demand V) (s : Vertex V D → Bool) :
    uncut e s = ∑ d, localCost (e d).equal (s (.inl (e d).left)) (s (.inl (e d).right))
      (s (.inr (d,0))) (s (.inr (d,1))) (s (.inr (d,2))) := by
  unfold uncut
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : D×Fin 4 => p.2.val < if (e p.1).equal then 4 else 3)) (by simp) (fun p : D×Fin 4 => mono (s (ends e p).1) (s (ends e p).2))]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fin.sum_univ_four]
  cases h : (e d).equal <;> simp [h,ends,localCost,add_assoc]

omit [Fintype V] [DecidableEq V] [DecidableEq D] in
lemma uncut_lower (e : D → Demand V) (s : Vertex V D → Bool) :
    totalFailure e (fun v => s (.inl v)) ≤ uncut e s := by
  rw [uncut_locals]
  exact Finset.sum_le_sum (fun d _ => local_lower _ _ _ _ _ _)

omit [Fintype V] [DecidableEq V] [DecidableEq D] in
lemma uncut_extend (e : D → Demand V) (s : V → Bool) : uncut e (extend e s)=totalFailure e s := by
  rw [uncut_locals]
  apply Finset.sum_congr rfl
  intro d _
  simpa [extend,failure] using
    local_extension (e d).equal (s (e d).left) (s (e d).right)

end MinUncut.PathRealization

end
namespace MinUncut.FiniteProof

def orient (b x : Bool) : Bool := if b then x else !x

def rep {A : Type*} (a : A) (P : A → Bool) : {R : A → Bool // R a=true} :=
  ⟨fun x => P a == P x, by simp⟩

lemma rep_not {A : Type*} (a : A) (P : A → Bool) :
    rep a (fun x => !(P x))=rep a P := by
  apply Subtype.ext
  funext x
  simp [rep]

lemma rep_restore {A : Type*} (a : A) (P : A → Bool) :
    (fun x => orient (P a) ((rep a P).val x))=P := by
  funext x
  cases h : P a <;> cases hx : P x <;> simp [orient,rep,h,hx]

lemma rep_fixed {A : Type*} (a : A) (R : {R : A → Bool // R a=true}) :
    rep a R.val=R := by
  apply Subtype.ext
  funext x
  simp [rep,R.property]

variable {Q : Type*} {A : Q → Type*} (base : ∀ q, A q)

abbrev Query := Σ q, A q → Bool
abbrev Variable := Σ q, {R : A q → Bool // R (base q)=true}

def vertex (p : Query (A := A)) : Variable base := ⟨p.1,rep (base p.1) p.2⟩

def answer (y : Variable base → Bool) (q : Q) (P : A q → Bool) : Bool :=
  orient (P (base q)) (y (vertex base ⟨q,P⟩))

def Folded (f : ∀ q, (A q → Bool) → Bool) : Prop :=
  ∀ q P, f q (fun x => !(P x))= !(f q P)

lemma answer_folded (y : Variable base → Bool) : Folded (answer base y) := by
  intro q P
  simp only [answer,vertex,rep_not]
  cases h : P (base q) <;> simp [orient]

lemma answer_rep (y : Variable base → Bool) (q : Q)
    (R : {R : A q → Bool // R (base q)=true}) : answer base y q R.val=y ⟨q,R⟩ := by
  simp [answer,vertex,R.property,rep_fixed,orient]

lemma answer_of_folded (f : ∀ q, (A q → Bool) → Bool) (hf : Folded f) :
    answer base (fun p => f p.1 p.2.val)=f := by
  funext q P
  unfold answer vertex
  cases h : P (base q)
  · have hr : (rep (base q) P).val=(fun x => !(P x)) := by
      funext x
      simp [rep,h]
    simp only [hr,orient,Bool.false_eq_true,ite_false,hf q P,Bool.not_not]
  · have hr : (rep (base q) P).val=P := by
      funext x
      simp [rep,h]
    simp [hr,orient]

structure QueryDemand where
  left : Query (A := A)
  right : Query (A := A)
  equal : Bool

def QueryDemand.signed (d : QueryDemand (A := A)) : PathRealization.Demand (Variable base) where
  left := vertex base d.left
  right := vertex base d.right
  equal := if d.equal then (d.left.2 (base d.left.1)==d.right.2 (base d.right.1))
    else !(d.left.2 (base d.left.1)==d.right.2 (base d.right.1))

def QueryDemand.failure (d : QueryDemand (A := A))
    (f : ∀ q, (A q → Bool) → Bool) : ℕ :=
  if (f d.left.1 d.left.2 == f d.right.1 d.right.2)=d.equal then 0 else 1

lemma QueryDemand.failure_signed (d : QueryDemand (A := A)) (y : Variable base → Bool) :
    PathRealization.failure (d.signed base) y=d.failure (answer base y) := by
  unfold PathRealization.failure QueryDemand.signed QueryDemand.failure answer
  cases d.equal <;> cases d.left.2 (base d.left.1) <;> cases d.right.2 (base d.right.1) <;>
    cases y (vertex base d.left) <;> cases y (vertex base d.right) <;> rfl

end MinUncut.FiniteProof

end OAI
