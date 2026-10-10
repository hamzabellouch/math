import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeNumberedSets
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization
import OAI.Combinatorics.MatchingCount.Algorithm.TreeReweight
import OAI.Combinatorics.MatchingCount.Sampling.TreeMarking

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder ExecutableMarking ExecutableOptions TreeTyped.Numbered UnitRefresh

abbrev Tables := List (Options ℕ)
def table (x : Tables×ℕ) : Options ℕ := x.1.getD x.2 []
def tableRealizer : Realizer table := getDFast []
lemma polynomial_table : PolynomialTime tableRealizer := polynomial_getDFast []
def assign (x : MarkInput Tables ℕ) : Marks ℕ := ExecutableMarking.assign table x
def assignRealizer : Realizer assign := ExecutableMarking.assignRealizer tableRealizer natEqual
lemma polynomial_assign : PolynomialTime assignRealizer :=
  ExecutableMarking.polynomial_assign polynomial_table polynomial_natEqual

variable {E : Type} [Fintype E] [LinearOrder E]
noncomputable def tableRep (f : E→WeightedOptions (Fin 3)) : Tables :=
  List.ofFn (fun i=>ExecutableOptions.repr Fin.val (f (orderedEnum E i)))
def numericMarks (s : Finset E) (f : E→Fin 3) : Marks ℕ :=
  (s.sort (·≤·)).map (fun e=>(index e,(f e).val))
lemma table_rep (f : E→WeightedOptions (Fin 3)) (e : E) :
    table (tableRep f,index e)=ExecutableOptions.repr Fin.val (f e) := by
  simp only [table,tableRep,index,List.getD,List.getElem?_ofFn,
    ((orderedEnum E).symm e).isLt,↓reduceDIte,Fin.eta,Option.getD_some,Equiv.apply_symm_apply]

lemma assign_rep (f : E→WeightedOptions (Fin 3)) (keys : List E) (hk : ∀ e,e∈keys)
    (s : Finset E) {k : ℕ} (bits : E→Fin k→Bool) :
    assign ((tableRep f,keys.map (fun e=>(index e,List.ofFn (bits e)))),Numbered.set s)=
      numericMarks s (fun e=>(f e).draw k (bits e)) := by
  unfold assign ExecutableMarking.assign numericMarks
  rw [sort_set,List.map_map]
  apply List.map_congr_left
  intro e _
  dsimp only [Function.comp_def,markEdge]
  rw [table_rep,lookup_image [] keys index (fun e=>List.ofFn (bits e)) index_injective e (hk e),draw_repr Fin.val (f e) 0 (bits e)]

theorem source_marking_post : ∃ p : Polynomial ℕ,
    ∀ {E : Type} [Fintype E] [LinearOrder E] (f : E→WeightedOptions (Fin 3))
      (keys : List E), (∀ e,e∈keys) → ∀ (s : Finset E) {k : ℕ} (bits : E→Fin k→Bool) (t : ℕ),
      let x := ((tableRep f,keys.map (fun e=>(index e,List.ofFn (bits e)))),Numbered.set s)
      p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine assignRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine assignRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (numericMarks s (fun e=>(f e).draw k (bits e)))) := by
  obtain ⟨p,hp⟩:=TreePost.polynomial_compiles assignRealizer polynomial_assign
  refine ⟨p,fun {E} _ _ f keys hk s {k} bits t ht coins=>?_⟩
  have h:=hp ((tableRep f,keys.map (fun e=>(index e,List.ofFn (bits e)))),Numbered.set s) t ht coins
  rwa [assign_rep f keys hk s bits] at h
end MatchingFPRAS.NumericMarking

end OAI
