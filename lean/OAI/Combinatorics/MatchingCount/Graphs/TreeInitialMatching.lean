import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeRefresh

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

abbrev InitialInput := List Key×CountInput

def initial (x : InitialInput) : Finset ℕ :=
  refresh (x,x.2.1.1.map (fun _=>([] : List Bool)))
def initialRealizer : Realizer initial := (composition
  (pair identity (composition second.fst.fst (map (constant ([] : List Bool)))))
  refreshRealizer).congr (fun _=>rfl)
lemma polynomial_initial : PolynomialTime initialRealizer := by
  unfold initialRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_refresh
  tree_cost

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
lemma initial_valid (bags : V→Finset L) (rank : L→ℕ) (parent : L→Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (hex : Nonempty (BagPM bags))
    (a : Bags) (ha : List.Forall₂ List.Perm a (orderedRep (numberedBags bags))) :
    ∃ M : BagPM bags,
      initial (storedCatalog (a,List.range (Fintype.card L)),
        ((a,parentRep (numberedParent parent)),(Materialized.plan (numberedRank rank)).map Fin.val))=
      Numbered.set M.val := by
  obtain ⟨M⟩:=hex
  let bits : Fin (Fintype.card V)→Fin 0→Bool := fun _ i=>Fin.elim0 i
  refine ⟨sampleMatching 0 bags rank parent hb hne hp M bits,?_⟩
  unfold initial
  have haLen : a.length=Fintype.card V := by
    simpa only [orderedRep,List.length_ofFn] using ha.length_eq
  have he : a.map (fun _=>([] : List Bool))=List.ofFn (fun i=>List.ofFn (bits i)) := by
    simp only [List.map_const',List.ofFn_zero]
    rw [haLen]
    exact (List.ofFn_const _ _).symm
  dsimp only
  rw [he]
  exact refresh_sampleMatching bags rank parent hb hne hp M a ha bits

open TreePost Turing

theorem initial_post : ∃ p : Polynomial ℕ,∀ x : InitialInput,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine initialRealizer.program) (packed x) coins).state=none ∧
      (run (machine initialRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (initial x)) :=
  polynomial_compiles initialRealizer polynomial_initial
end MatchingFPRAS.ExecutableRefresh

end OAI
