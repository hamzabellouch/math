import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TableMarking
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptions
import OAI.Combinatorics.MatchingCount.Machines.TreeStateTable

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction ExecutableOptions ExecutableLadder

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]
abbrev MarkInput (C E : Type) := (C×StateTable E (List Bool))×Finset E
abbrev Marks (E : Type) := List (E×ℕ)

def markEdge (g : C×E→Options ℕ) (x : (C×StateTable E (List Bool))×E) : E×ℕ :=
  (x.2,draw 0 (g (x.1.1,x.2),lookup [] (x.1.2,x.2)))
def markEdgeRealizer {g : C×E→Options ℕ} (G : Realizer g)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (markEdge g) :=
  (pair second (composition (pair (composition (pair first.fst second) G)
    (composition (pair first.snd second) (lookupRealizer [] Eq))) (drawRealizer 0))).congr (fun _=>rfl)
lemma polynomial_markEdge {g : C×E→Options ℕ} {G : Realizer g}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime Eq) : PolynomialTime (markEdgeRealizer G Eq) := by
  unfold markEdgeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_lookup ([] : List Bool) hE
  have := polynomial_draw (0 : ℕ)
  tree_cost

def assign (g : C×E→Options ℕ) (x : MarkInput C E) : Marks E :=
  (x.2.sort (·≤·)).map (fun e=>markEdge g (x.1,e))
def assignRealizer {g : C×E→Options ℕ} (G : Realizer g)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (assign g) :=
  composition (pair first (composition second finsetList)) (mapWith (markEdgeRealizer G Eq))
lemma polynomial_assign {g : C×E→Options ℕ} {G : Realizer g}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime Eq) : PolynomialTime (assignRealizer G Eq) := by
  unfold assignRealizer
  exact polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith (polynomial_markEdge hG hE))

def marksRep (s : Finset E) (f : E→Fin 3) : Marks E :=
  (s.sort (·≤·)).map (fun e=>(e,(f e).val))
omit [Codec C] [Codec E] [Inhabited E] in
lemma assign_rep (g : C×E→Options ℕ) (c : C) (tables : E→WeightedOptions (Fin 3))
    (hg : ∀ e,g (c,e)=ExecutableOptions.repr Fin.val (tables e))
    (keys : List E) (hk : ∀ e,e∈keys) (s : Finset E) {k : ℕ} (bits : E→Fin k→Bool) :
    assign g ((c,stateRep keys (fun e=>List.ofFn (bits e))),s)=
      marksRep s (fun e=>(tables e).draw k (bits e)) := by
  unfold assign marksRep
  apply List.map_congr_left
  intro e he
  unfold markEdge
  rw [hg,lookup_stateRep [] keys _ e (hk e),draw_repr Fin.val (tables e) 0 (bits e)]

omit [Codec C] [Codec E] [Inhabited E] in
lemma assign_draw (g : C×E→Options ℕ) (c : C) (tables : E→WeightedOptions (Fin 3))
    (hg : ∀ e,g (c,e)=ExecutableOptions.repr Fin.val (tables e))
    (keys : List E) (hk : ∀ e,e∈keys) {V A : Type} [Fintype V] [Fintype E]
    [Fintype A] [Nonempty A] (inc : E→V→Prop) (f : A→Transport.PM inc)
    {k : ℕ} (a : A) (bits : E→Fin k→Bool) :
    assign g ((c,stateRep keys (fun e=>List.ofFn (bits e))),(f a).val)=
      marksRep (TableMarking.draw inc f tables k (a,bits)).1.val
        (fun e=>(tables e).draw k (bits e)) := assign_rep g c tables hg keys hk _ bits
end MatchingFPRAS.ExecutableMarking

end OAI
