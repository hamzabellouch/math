import Mathlib
import OAI.Combinatorics.ThinTrees.Pencil.FiniteFamilies
import OAI.Combinatorics.ThinTrees.Pencil.Parameters

namespace OAI

/-! Point programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α β : Type*} {ea : α → Word} {eb : β → Word}
def Realizes.cons {f : α → β} {g : α → List β}
    (r : Realizes ea eb f) (s : Realizes ea (listCode eb) g) :
    Realizes ea (listCode eb) (fun a => f a :: g a) := (r.both s).then (consList eb)
instance poly_cons {f : α → β} {g : α → List β}
    (r : Realizes ea eb f) (s : Realizes ea (listCode eb) g) [PolyTime r] [PolyTime s] :
    PolyTime (r.cons s) := by unfold Realizes.cons;infer_instance

def select3 {i : α → Fin 3} (ri : Realizes ea natCode (fun a => (i a).val))
    {f g h : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g)
    (t : Realizes ea ratCode h) : Realizes ea ratCode (fun a => ![f a,g a,h a] (i a)) :=
  ((ri.both (r.cons (s.cons (t.then (singleton ratCode))))).then (getD ratCode 0)).congr (by
    intro a
    exact getD_ofFn ![f a,g a,h a] (i a) 0)
instance poly_select3 {i : α → Fin 3} (ri : Realizes ea natCode (fun a => (i a).val))
    {f g h : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g)
    (t : Realizes ea ratCode h) [PolyTime ri] [PolyTime r] [PolyTime s] [PolyTime t] :
    PolyTime (select3 ri r s t) := by unfold select3;apply poly_congr

def select7 {i : α → Fin 7} (ri : Realizes ea natCode (fun a => (i a).val))
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : α → ℚ}
    (r₀ : Realizes ea ratCode f₀) (r₁ : Realizes ea ratCode f₁) (r₂ : Realizes ea ratCode f₂)
    (r₃ : Realizes ea ratCode f₃) (r₄ : Realizes ea ratCode f₄) (r₅ : Realizes ea ratCode f₅)
    (r₆ : Realizes ea ratCode f₆) :
    Realizes ea ratCode (fun a => ![f₀ a,f₁ a,f₂ a,f₃ a,f₄ a,f₅ a,f₆ a] (i a)) :=
  ((ri.both (r₀.cons (r₁.cons (r₂.cons (r₃.cons (r₄.cons (r₅.cons
    (r₆.then (singleton ratCode))))))))).then (getD ratCode 0)).congr (by
      intro a
      exact getD_ofFn ![f₀ a,f₁ a,f₂ a,f₃ a,f₄ a,f₅ a,f₆ a] (i a) 0)
instance poly_select7 {i : α → Fin 7} (ri : Realizes ea natCode (fun a => (i a).val))
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : α → ℚ}
    (r₀ : Realizes ea ratCode f₀) (r₁ : Realizes ea ratCode f₁) (r₂ : Realizes ea ratCode f₂)
    (r₃ : Realizes ea ratCode f₃) (r₄ : Realizes ea ratCode f₄) (r₅ : Realizes ea ratCode f₅)
    (r₆ : Realizes ea ratCode f₆) [PolyTime ri] [PolyTime r₀] [PolyTime r₁] [PolyTime r₂]
    [PolyTime r₃] [PolyTime r₄] [PolyTime r₅] [PolyTime r₆] :
    PolyTime (select7 ri r₀ r₁ r₂ r₃ r₄ r₅ r₆) := by unfold select7;apply poly_congr
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {a : α → Point}

private theorem poly_nadd_explicit {f g : α → ℕ}
    {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.nadd s) := by
  have := hr
  have := hs
  infer_instance

private theorem poly_nmul_explicit {f g : α → ℕ}
    {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    (hr : PolyTime r) (hs : PolyTime s) : PolyTime (r.nmul s) := by
  have := hr
  have := hs
  infer_instance

def edgeCoord (p : Fin 3) (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea ratCode (fun b => (a b).v (edgeIndex p (e b))) :=
  let n := r.then pointN
  let m := r.then pointM
  coordinate r (fun b => edgeIndex p (e b))
    ((n.nmul n).nadd ((n.nmul (n.nmul n)).nadd (re.nadd (m.nmul (constant ea natCode p.val)))))
instance poly_edgeCoord (p : Fin 3) (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (edgeCoord p r e re) := by
  have hn : PolyTime (r.then pointN) := by infer_instance
  have hm : PolyTime (r.then pointM) := by infer_instance
  unfold edgeCoord
  refine @poly_coordinate _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · exact poly_nadd_explicit (poly_nmul_explicit hn hn)
      (poly_nadd_explicit (poly_nmul_explicit hn (poly_nmul_explicit hn hn))
        (poly_nadd_explicit ‹PolyTime re›
          (poly_nmul_explicit hm (poly_constant ea natCode p.val))))

def flowCoord (p : Fin 2) (r : Realizes ea pointCode a)
    (v : (b : α) → Fin (a b).p.graph.n) (e : (b : α) → Fin (a b).p.graph.m)
    (rv : Realizes ea natCode (fun b => (v b).val)) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea ratCode (fun b => (a b).v (flowIndex p (v b) (e b))) :=
  let n := r.then pointN
  let m := r.then pointM
  coordinate r (fun b => flowIndex p (v b) (e b))
    ((n.nmul n).nadd ((n.nmul (n.nmul n)).nadd
      (((constant ea natCode 3).nmul m).nadd
        ((re.nadd (m.nmul rv)).nadd ((n.nmul m).nmul (constant ea natCode p.val))))))
instance poly_flowCoord (p : Fin 2) (r : Realizes ea pointCode a)
    (v : (b : α) → Fin (a b).p.graph.n) (e : (b : α) → Fin (a b).p.graph.m)
    (rv : Realizes ea natCode (fun b => (v b).val)) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime rv] [PolyTime re] : PolyTime (flowCoord p r v e rv re) := by
  have hn : PolyTime (r.then pointN) := by infer_instance
  have hm : PolyTime (r.then pointM) := by infer_instance
  unfold flowCoord
  refine @poly_coordinate _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · exact poly_nadd_explicit (poly_nmul_explicit hn hn)
      (poly_nadd_explicit (poly_nmul_explicit hn (poly_nmul_explicit hn hn))
        (poly_nadd_explicit (poly_nmul_explicit (poly_constant ea natCode 3) hm)
          (poly_nadd_explicit (poly_nadd_explicit ‹PolyTime re› (poly_nmul_explicit hm ‹PolyTime rv›))
            (poly_nmul_explicit (poly_nmul_explicit hn hm) (poly_constant ea natCode p.val)))))

def storedU (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea ratCode (fun b => (a b).p.u (e b)) :=
  ((re.both (r.then pointU)).then (getD ratCode 0)).congr (fun b => getD_ofFn _ (e b) 0)
instance poly_storedU (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (storedU r e re) := by unfold storedU;apply poly_congr

def graphEdge (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea GraphStack.edgeCode (fun b => ⟨(a b).p.graph,e b⟩) :=
  ((r.then pointGraph).both re).changeOutput GraphStack.edgeCode (fun b => ⟨(a b).p.graph,e b⟩)
    (fun _ => rfl)
instance poly_graphEdge (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (graphEdge r e re) := by unfold graphEdge;apply poly_changeOutput

abbrev vEquiv (a : Point) := Equiv.refl (Fin a.p.graph.n)
abbrev eEquiv (a : Point) := Equiv.refl (Fin a.p.graph.m)
abbrev pairEquiv := prodEquiv vEquiv vEquiv
abbrev tripleEquiv := prodEquiv vEquiv pairEquiv
abbrev tripleCode := indexedCode pointCode tripleEquiv
abbrev triplePoint := indexedFirst (ea:=pointCode) tripleEquiv
abbrev tripleHead := indexedProductLeft (ea:=pointCode) vEquiv pairEquiv (pointN.nmul pointN)
abbrev tripleTail := indexedProductRight (ea:=pointCode) vEquiv pairEquiv (pointN.nmul pointN)
abbrev pairHead := indexedProductLeft (ea:=pointCode) vEquiv vEquiv pointN
abbrev pairTail := indexedProductRight (ea:=pointCode) vEquiv vEquiv pointN
abbrev tripleI := tripleHead.then (indexedIndex vEquiv)
abbrev tripleJ := tripleTail.then pairHead |>.then (indexedIndex vEquiv)
abbrev tripleK := tripleTail.then pairTail |>.then (indexedIndex vEquiv)

def tripleCoordinate : Realizes tripleCode ratCode (fun p => p.1.v (mulIndex p.2)) :=
  let n := triplePoint.then pointN
  coordinate triplePoint (fun p => mulIndex p.2)
    ((n.nmul n).nadd ((tripleK.nadd (n.nmul tripleJ)).nadd ((n.nmul n).nmul tripleI)))
instance poly_tripleCoordinate : PolyTime tripleCoordinate := by
  have hi : PolyTime tripleI := by infer_instance
  have hj : PolyTime tripleJ := by infer_instance
  have hk : PolyTime tripleK := by infer_instance
  have hn : PolyTime (triplePoint.then pointN) := by infer_instance
  unfold tripleCoordinate
  refine @poly_coordinate _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · exact poly_nadd_explicit (poly_nmul_explicit hn hn)
      (poly_nadd_explicit (poly_nadd_explicit hk (poly_nmul_explicit hn hj))
        (poly_nmul_explicit (poly_nmul_explicit hn hn) hi))

def tripleDistinct : Realizes tripleCode boolCode
    (fun p => decide (p.2.1≠p.2.2.1 ∧ p.2.2.1≠p.2.2.2 ∧ p.2.1≠p.2.2.2)) :=
  (tripleI.finEq tripleJ).not.and ((tripleJ.finEq tripleK).not.and (tripleI.finEq tripleK).not)
instance poly_tripleDistinct : PolyTime tripleDistinct := by
  have : PolyTime tripleI := by infer_instance
  have : PolyTime tripleJ := by infer_instance
  have : PolyTime tripleK := by infer_instance
  unfold tripleDistinct
  refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_not

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
