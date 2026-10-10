import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreePreparedTop
import OAI.Combinatorics.MatchingCount.Sampling.TreeNumericMarking

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

abbrev SampleContext := (Prepared×Finset ℕ)×Tables
abbrev SampleBits := List (List Bool×Bits)×StateTable ℕ (List Bool)
abbrev SampleInput := SampleContext×SampleBits

def sample (x : SampleInput) : ExecutableMarking.Marks ℕ :=
  assign ((x.1.2,x.2.2),preparedTop (x.2.1,x.1.1))
def sampleRealizer : Realizer sample := (composition (pair (pair first.snd second.snd)
  (composition (pair second.fst first.fst) preparedTopRealizer)) assignRealizer).congr (fun _=>rfl)
lemma polynomial_sample : PolynomialTime sampleRealizer := by
  unfold sampleRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_preparedTop
  have := polynomial_assign
  tree_cost

def sampleMany (x : SampleContext×List SampleBits) : List (ExecutableMarking.Marks ℕ) :=
  x.2.map (fun b=>sample (x.1,b))
def sampleManyRealizer : Realizer sampleMany := mapWith sampleRealizer
lemma polynomial_sampleMany : PolynomialTime sampleManyRealizer := polynomial_mapWith polynomial_sample

theorem sampleMany_post : ∃ p : Polynomial ℕ,∀ x : SampleContext×List SampleBits,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine sampleManyRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine sampleManyRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (sampleMany x)) :=
  TreePost.polynomial_compiles sampleManyRealizer polynomial_sampleMany

open Replica.Ladder Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p<rank l)
lemma sample_source (ft fq : List Bool) (hq : 0<fq.length)
    (w : BagEdge bags→ℚ) (hw : ∀ e,0≤w e) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    (f : BagEdge bags→WeightedOptions (Fin 3))
    {k n km : ℕ} (bits : Fin n→ScanBits V k) (mb : BagEdge bags→Fin km→Bool) :
    sample (((sourcePrepared rank parent w a ft fq,Numbered.set M.val),tableRep f),
      (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
        (List.ofFn (orderedEnum (BagEdge bags))).map (fun e=>(index e,List.ofFn (mb e)))))=
      numericMarks (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
          (fun e=>(f e).draw km (mb e)) := by
  rw [sample,preparedTop_source hbags hG rank parent hb hne hp ft fq hq w hw M a ha bits]
  apply assign_rep
  intro e
  exact List.mem_ofFn.mpr ⟨(orderedEnum _).symm e,Equiv.apply_symm_apply _ _⟩
end MatchingFPRAS.NumericMarking

end OAI
