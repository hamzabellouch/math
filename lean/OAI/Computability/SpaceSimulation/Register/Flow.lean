import OAI.Computability.SpaceSimulation.Register.Arithmetic

namespace OAI

/-! Compile bounded-stack algorithms whose steps may themselves be
space-bounded computations. A Flow is just *semantics*, no computability
in its definition; the compilation criterion requires a uniformly
computable step on the packed code, in the *same* unit being bounded.
The interpreted machine manipulates ONE GLOBAL word, outside
the activation stack. To charge the stack we measure the sizes of
suspended (continuation) frame codes. -/
namespace Fifths
open Bin

inductive FlowMove (A : Type)
  | finish
  | cont (f : A)
  | call (child after : A)

structure Flow where
  G : Type
  F : Type
  packG : G → ℕ
  packF : F → ℕ
  act : G → F → G × FlowMove F

namespace Flow
variable (m : Flow)

/-- Cost to *stack* this frame in our fixed prefix encoding. -/
def fee (f : m.F) := 2*(m.packF f).size + 1

/-- Contract of one activation. B upper bounds the sum of fees of
frames simultaneously suspended by (or under) this invocation.
Current frame not included; uniformly small active frame will also
be required. -/
inductive Executes : ℕ → m.G → m.F → m.G → Prop
  | done {B g f h} (step : m.act g f = (h,.finish)) :
    Executes B g f h
  | next {B g f h j w}
    (step : m.act g f = (h,.cont j))
    (after : Executes B h j w) :
    Executes B g f w
  | call {A B g f h j k u w}
    (step : m.act g f = (h,.call j k))
    (child : Executes A h j u)
    (bound : m.fee k + A ≤ B)
    (after : Executes B u k w) :
    Executes B g f w

namespace Executes
theorem up {m : Flow} {B C g f h} (r : m.Executes B g f h) (b : B ≤ C) :
    m.Executes C g f h := by
  induction r with
  | done s => exact .done s
  | next s _ ih => exact .next s (ih b)
  | call s r a _ _ ih => exact .call s r (a.trans b) (ih b)
end Executes

/-- Reaches another frame at the same level, with any children
finished. (For use proving Executes via a schedule of loops.) -/
inductive Continues : ℕ → m.G → m.F → m.G → m.F → Prop
  | stop {B g f} : Continues B g f g f
  | next {B g f h j w l}
    (step : m.act g f = (h,.cont j))
    (after : Continues B h j w l) :
    Continues B g f w l
  | call {A B g f h j k u w l}
    (step : m.act g f = (h,.call j k))
    (child : m.Executes A h j u)
    (bound : m.fee k + A ≤ B)
    (after : Continues B u k w l) :
    Continues B g f w l
namespace Continues
variable {m} {B} {g h u : m.G} {f j k : m.F}

theorem trans (p : m.Continues B g f h j) (q : m.Continues B h j u k) :
    m.Continues B g f u k := by
  induction p with
  | stop => exact q
  | next s _ ih => exact .next s (ih q)
  | call s h b _ ih => exact .call s h b (ih q)

theorem then_exec (p : m.Continues B g f h j) (q : m.Executes B h j u) :
    m.Executes B g f u := by
  induction p with
  | stop => exact q
  | next s _ ih => exact .next s (ih q)
  | call s h b _ ih => exact .call s h b (ih q)
end Continues

def packFs (m : Flow) : List m.F → ℕ
  | [] => 0
  | f :: l => pair (m.packF f) (m.packFs l)
theorem packFs_cons (f : m.F) (l : List m.F) :
    (m.packFs (f::l)).size = m.fee f + (m.packFs l).size := by
  rw [packFs,pair_size]; rfl

theorem pack_ne (l : List m.F) :
    m.packFs l ≠ 0 ↔ l ≠ [] := by
  cases l
  · simp [packFs]
  · simp [packFs, pair_ne_zero]

abbrev Cfg := m.G × List m.F
def next (c : m.Cfg) : m.Cfg :=
  match c.2 with
  | [] => c
  | f :: l =>
    let (g,a) := m.act c.1 f
    match a with
    | .finish => (g,l)
    | .cont f => (g,f::l)
    | .call f h => (g,f::h::l)

@[simp] def path (m : Flow) (s : m.Cfg) : ℕ → m.Cfg
  | 0 => s
  | i+1 => m.next (m.path s i)

theorem path_add (s : m.Cfg) (n l : ℕ) :
    m.path s (n+l) = m.path (m.path s n) l := by
  induction l <;> simp [*]

/-- Segment of `n` flow moves. Suspended-frame total at each nonfinal
point bounded by `B`. Active frame exists at such points. -/
structure Segment (s t : m.Cfg) (n B : ℕ) : Prop where
  endIs : m.path s n = t
  active : ∀ j < n, (m.path s j).2 ≠ [] ∧
    (m.packFs (m.path s j).2.tail).size ≤ B

namespace Segment
variable {m} {s t u : m.Cfg} {n l B C : ℕ}
theorem mono (h : m.Segment s t n B) (g : B ≤ C) : m.Segment s t n C :=
  ⟨h.endIs, fun j i => (h.active j i).imp_right (fun x => x.trans g)⟩
theorem trans (h : m.Segment s t n B) (g : m.Segment t u l B) :
    m.Segment s u (n+l) B := by
  constructor
  · rw [path_add,h.endIs,g.endIs]
  · intro j a
    by_cases e : j < n
    · exact h.active j e
    · have q := g.active (j-n) (show j-n < l by omega)
      have f : m.path s j = m.path t (j-n) := by
        rw [← h.endIs, ← path_add, show n+(j-n)=j by omega]
      rwa [f]
theorem one {g : m.G} {f : m.F} {l : List m.F} (e : m.next (g,f::l) = t)
    (q : (m.packFs l).size ≤ B) :
    m.Segment (g,f::l) t 1 B := by
  refine ⟨e, fun j i => ?_⟩
  obtain rfl : j = 0 := by omega
  simpa using q
end Segment

theorem trajectory {B} {g h f} (r : m.Executes B g f h) (l : List m.F) :
    ∃ n, m.Segment (g,f::l) (h,l) n (B+(m.packFs l).size) := by
  induction r generalizing l with
  | done e =>
    exact ⟨1,Segment.one (by simp [next,e]) (by omega)⟩
  | next s _ ih =>
    obtain ⟨n,h⟩ := ih l
    refine ⟨_,Segment.trans (Segment.one (by simp [next,s]) (by omega)) h⟩
  | @call A B g f h j k u w e _ b _ ih₁ ih₂ =>
    obtain ⟨n,x⟩ := ih₁ (k :: l)
    obtain ⟨p,y⟩ := ih₂ l
    have z := Segment.trans (Segment.mono x (show _ ≤ B + (m.packFs l).size from by
      rw [packFs_cons]; omega)) y
    exact ⟨_,Segment.trans (Segment.one (by simp [next,e]) (by omega)) z⟩

-- Code for a move: a leading tag, plus zero-padded first and second frame encodings.
def tag : FlowMove m.F → ℕ
  | .finish => 0
  | .cont _ => 1
  | .call _ _ => 2
def arg1 : FlowMove m.F → ℕ
  | .finish => 0
  | .cont f | .call f _ => m.packF f
def arg2 : FlowMove m.F → ℕ
  | .call _ f => m.packF f
  | _ => 0
def packMove (r : m.G × FlowMove m.F) :=
  pair (m.packG r.1) (pair (m.tag r.2) (pair (m.arg1 r.2) (m.arg2 r.2)))

/-- Inspect the current activation in the presence of immutable
integer parameter `cp`. -/
def input (cp : ℕ) (g : m.G) (f : m.F) :=
  pair cp (pair (m.packG g) (m.packF f))

def code (cp : ℕ) (c : m.Cfg) :=
  pair cp (pair (m.packG c.1) (m.packFs c.2))

@[simp] theorem next_code (cp : ℕ) (g : m.G) (f : m.F) (l : List m.F) :
    m.code cp (m.next (g,f::l)) =
      let r := m.act g f
      let k := m.tag r.2
      pair cp (pair (m.packG r.1)
        (if k=0 then m.packFs l
         else Bin.pair (m.arg1 r.2) (if k=1 then m.packFs l
           else Bin.pair (m.arg2 r.2) (m.packFs l)))) := by
  obtain ⟨y,a,e⟩ : ∃ y a, m.act g f = (y,a) := ⟨_,_,rfl⟩
  cases a <;> simp [next,e,tag,arg1,arg2,code,packFs]

section Uniform
variable {I X : Type} {x : I → List X} {S cp : I → ℕ}

/-- Local indexed hypothesis. Global pool and program counter may be
any encoded state of the corresponding semantic type. -/
abbrev Points (M : I → Flow) := Σ i, (M i).G × (M i).F

def uniform (M : I → Flow) (x : I → List X) (S cp : I → ℕ) : Prop :=
  Comp (fun i : Points M => x i.1) (fun i => S i.1)
    (fun i => (M i.1).input (cp i.1) i.2.1 i.2.2)
    (fun i => (M i.1).packMove ((M i.1).act i.2.1 i.2.2))

-- Apply the move over a nonempty stack, incorporating local step computation.
theorem uniform_move {M : I → Flow} (p : uniform M x S cp)
    {U : Type} (e : U → I) (g : ∀ i, (M (e i)).G)
    (f : ∀ i, (M (e i)).F) (l : ∀ i, List (M (e i)).F) (s : U → ℕ)
    (h : Comp (fun i => x (e i)) (fun i => S (e i)) s
      (fun i => (M (e i)).code (cp (e i)) (g i,f i :: l i))) :
    Comp (fun i => x (e i)) (fun i => S (e i)) s
      (fun i => (M (e i)).code (cp (e i)) ((M (e i)).next (g i,f i :: l i))) := by
  have u : Comp _ _ s (fun i => (M (e i)).input (cp (e i)) (g i) (f i)) :=
    h.left.pair (h.right.left.pair h.right.right.left)
  have v := u.trans (Comp.pull p (fun i => ⟨e i,g i,f i⟩))
  have a := v.right.left
  have b := v.right.right
  have t := h.right.right.right
  have o := a.eq (Comp.constant h.source 1)
  have q := a.eq (Comp.constant h.source 0)
  refine (h.left.pair (v.left.pair (q.iteB t (b.left.pair (o.iteB t (b.right.pair t))))))
    |>.congr (fun i => ?_)
  -- boolean test via decide_eq_true
  simp

theorem uniform_result {M : I → Flow} (p : uniform M x S cp)
    (g h : ∀ i, (M i).G) (f : ∀ i, (M i).F) (B : I → ℕ) (b : Scaled S B)
    (q : ∀ i, (M i).Executes (B i) (g i) (f i) (h i)) :
    Comp x S (fun i => (M i).input (cp i) (g i) (f i))
      (fun i => (M i).packG (h i)) := by
  classical
  choose n r using fun i => (M i).trajectory (q i) []
  let cfg := fun (i : I) j => (M i).path (g i,[f i]) j
  have seg : ∀ i, cfg i (n i) = (h i,[]) := fun i => (r i).endIs
  have active : ∀ i j, j<n i → (cfg i j).2 ≠ [] ∧
      ((M i).packFs (cfg i j).2.tail).size ≤ B i := fun i j e =>
    (show _ from by
      have w := (r i).active j e
      simpa only [packFs,Nat.size_zero,Nat.add_zero] using w)
  let z : I → ℕ → ℕ := fun i j => (M i).code (cp i) (cfg i j)
  have sizes : Fits (fun i : Through n => S i.1.1) (fun i => z i.1.1 i.1.2) := by
    obtain ⟨c,v⟩ := Comp.source p
    obtain ⟨d,u⟩ := b
    have V (i : I) j (a : (M i).F) :
        ((M i).input (cp i) (cfg i j).1 a).size ≤ c*(S i+1) :=
      v ⟨i,(cfg i j).1,a⟩
    refine ⟨2*c+d+2,?_⟩
    rintro ⟨⟨i,j⟩,e⟩
    change j ≤ n i at e
    change (pair _ (pair _ ((M i).packFs _))).size ≤ (2*c+d+2)*(S i+1)
    rcases e.lt_or_eq with e|e
    · obtain ⟨q,t⟩ := active i j e
      cases l : (cfg i j).2 with
      | nil => contradiction
      | cons a w =>
        have q := V i j a
        unfold input at q
        rw [l,List.tail_cons] at t
        have u := u i
        simp only [pair_size, packFs_cons, fee, add_mul, mul_assoc] at *
        omega
    · subst j
      have v := V i (n i) (f i)
      unfold input at v
      -- input at the endpoint instead contains a frame; enlarge bound
      simp only [pair_size,seg,packFs,Nat.size_zero,add_mul,mul_assoc] at *
      omega
  have L : Comp x S (fun i => z i 0) (fun i => z i (n i)) := by
    refine Comp.loop n z ?_ ?_
    · let e : Before n → I := fun i => i.1.1
      let j : Before n → ℕ := fun i => i.1.2
      let lift : Before n → Through n := fun i => ⟨i.val,i.property.le⟩
      let v := fun (i : Before n) => cfg (e i) (j i)
      let a := fun (i : Before n) => (v i).2.headD (f (e i))
      let t := fun (i : Before n) => (v i).2.tail
      have E (i : Before n) : v i = ((v i).1,a i :: t i) := by
        refine Prod.ext rfl ?_
        have w : (v i).2 ≠ [] := (active (e i) (j i) i.property).1
        change (v i).2 = a i :: t i
        unfold a t
        cases eqn : (v i).2 with
        | nil => contradiction
        | cons _ _ => rfl
      let H : Comp (fun i => x (e i)) (fun i => S (e i))
          (fun i => z (e i) (j i)) (fun i => z (e i) (j i)) :=
        Comp.refl (sizes.pull lift)
      have G := uniform_move p e (fun i => (v i).1) a t _
        (H.congr (fun i => by
          change (M (e i)).code _ (v i) = _
          exact congrArg _ (E i)))
      apply G.congr
      intro i
      change (M (e i)).code _ _ = (M (e i)).code _ ((M (e i)).next (v i))
      exact congrArg _ (congrArg ((M (e i)).next) (E i).symm)
    · let H : Comp (fun i : Through n => x i.1.1) (fun i => S i.1.1)
          (fun i => z i.1.1 i.1.2) (fun i => z i.1.1 i.1.2) := Comp.refl sizes
      refine H.right.right.testnz.congr (fun i => ?_)
      rcases i with ⟨⟨i,j⟩,w⟩
      change j ≤ n i at w
      change (Comp.notZero ((M i).packFs (cfg i j).2)).toNat =
        (decide (j<n i)).toNat
      rcases w.lt_or_eq with l|l
      · have h := ((M i).pack_ne _).mpr (active i j l).1
        simp [Comp.notZero,h,l]
      · subst j; simp [seg,packFs,Comp.notZero]
  have e := Comp.refl (x := x) ((Comp.source p).pull (fun i => ⟨i,g i,f i⟩))
  have w : Comp x S (fun i => (M i).input (cp i) (g i) (f i)) (fun i => z i 0) :=
    e.left.pair (e.right.left.pair
      (e.right.right.pair (Comp.constant e.source 0)))
  exact ((w.trans L).right.left).congr (fun i => by rw [seg])
end Uniform
end Flow
end Fifths

end OAI
