import Mathlib
import OAI.Computability.QuantumFactoring.PrimeRecords
import OAI.Computability.QuantumFactoring.LoggedExecution
import OAI.Computability.QuantumFactoring.ControllerQueries

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree FactorController

namespace DataProducer

/-- Each occurrence carries its complete ancestral path. Equal labels under
separate parents are never identified or memoized. -/
abbrev NodeKey := List ℕ × ℕ
abbrev Choices := NodeKey→ℕ→ℕ→ℕ

def nodeRun (n : ℕ) (choose : Choices) (path : List ℕ) (m : ℕ) : Logged NodeKey (List ℕ) :=
  ⟨run (choose (path,m)) (2*n) 0 [m],[(path,m)]⟩

def NodeGood (n : ℕ) (choose : Choices) (k : NodeKey) : Prop :=
  ∀ im∈queries (choose k) (2*n) 0 [k.2], ProperDivisor im.2 (choose k im.1 im.2)

/-- The source's factor-and-recurse producer, with a depth cap. The Finsupp is
only a representation of the multiplicities in the returned prime list;
`primeRecord` never computes an unknown prime factorization. -/
noncomputable def build (n : ℕ) (choose : Choices) : ℕ→List ℕ→ℕ→Logged NodeKey FactorData
  | 0, _, _ => Logged.abort
  | depth+1, path, m => (nodeRun n choose path m).bind (fun ps =>
      (Logged.traverse (fun d => build n choose depth (path++[d]) d)
        (recordChildren (primeRecord ps))).map (FactorData.node m (primeRecord ps)))

lemma nodeRun_complete {m n : ℕ} (hm : 2 ≤ m) (hb : m<2^n)
    (choose : Choices) (path : List ℕ) (hg : Logged.Good (NodeGood n choose) (nodeRun n choose path m)) :
    ∃ ps, (nodeRun n choose path m).result=some ps := by
  apply run_complete_on_queries (choose (path,m))
  · intro a ha
    have he : a=m := by simpa using ha
    subst a
    exact hm
  · have hw := splitWeight_bound (by omega) hb
    simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega
  · exact hg (path,m) (by simp [nodeRun])

lemma nodeRun_record {n m : ℕ} {choose : Choices} {path : List ℕ} {ps : List ℕ}
    (h : (nodeRun n choose path m).result=some ps) : primeRecord ps=m.factorization := by
  have hs := run_sound (choose (path,m)) h
  have hp : ps.prod=m := by simpa using hs.2
  rw [primeRecord_eq_factorization ps hs.1,hp]

lemma child_level_empty {m depth d : ℕ} (h : level m (depth+1)=[]) (hd : d∈children m) :
    level d depth=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  have hh : e∈level m (depth+1) := List.mem_flatMap.mpr ⟨d,hd,he⟩
  rw [h] at hh
  exact List.not_mem_nil hh

/-- Literal all-good completion follows the actual short-circuit trace. There
is no hypothesis about queries or child occurrences that this run never made. -/
theorem build_complete (n : ℕ) (choose : Choices) (depth : ℕ) (path : List ℕ) (m : ℕ)
    (hm : 2 ≤ m) (hb : m<2^n) (hd : level m depth=[])
    (hg : Logged.Good (NodeGood n choose) (build n choose depth path m)) :
    (build n choose depth path m).result=some (trueData m) := by
  induction depth generalizing path m with
  | zero => simp only [level,List.cons_ne_self] at hd
  | succ depth ih =>
    have hroot := Logged.good_bind_left (NodeGood n choose) _ _ hg
    obtain ⟨ps,hps⟩ := nodeRun_complete hm hb choose path hroot
    have hf := nodeRun_record hps
    have hg' := Logged.good_bind_right (NodeGood n choose) _ _ hps hg
    have hchildren := (Logged.good_map (NodeGood n choose) _ _).mp hg'
    rw [hf,recordChildren_factorization] at hchildren
    have hc : (Logged.traverse (fun d => build n choose depth (path++[d]) d)
        (children m)).result=some ((children m).map trueData) := by
      apply Logged.traverse_complete (NodeGood n choose) _ trueData _ ?_ hchildren
      intro d hdm hgd
      have hbounds := child_bounds hdm
      exact ih _ _ hbounds.1 (hbounds.2.trans hb) (child_level_empty hd hdm) hgd
    rw [build,Logged.bind_result_some _ _ hps,Logged.map_result,hf,recordChildren_factorization,
      hc,Option.map_some,trueData_eq]

/-- Even a bad run cannot produce false accepted data. Every successful local
prime list and all ordered descendants agree with the canonical occurrence tree. -/
theorem build_sound (n : ℕ) (choose : Choices) (depth : ℕ) (path : List ℕ) (m : ℕ)
    {d : FactorData} (hs : (build n choose depth path m).result=some d) : d=trueData m := by
  induction depth generalizing path m d with
  | zero => simp only [build,Logged.abort] at hs; contradiction
  | succ depth ih =>
    cases hroot : (nodeRun n choose path m).result with
    | none => simp only [build,Logged.bind,hroot] at hs; contradiction
    | some ps =>
      have hf := nodeRun_record hroot
      rw [build,Logged.bind_result_some _ _ hroot,Logged.map_result,hf,recordChildren_factorization] at hs
      obtain ⟨ds,hds,he⟩ := Option.map_eq_some_iff.mp hs
      have hcan := Logged.traverse_sound (fun a => build n choose depth (path++[a]) a)
        trueData (children m) (fun a _ b hab => ih (path++[a]) a hab) hds
      subst d
      rw [hcan]
      exact (trueData_eq m).symm

theorem bounded_complete {m n : ℕ} (hm : 2 ≤ m) (hb : m<2^n)
    (choose : Choices) (hg : Logged.Good (NodeGood n choose) (build n choose (2*n) [] m)) :
    (build n choose (2*n) [] m).result=some (trueData m) ∧ (trueData m).Valid :=
  ⟨build_complete n choose (2*n) [] m hm hb (level_empty hm hb) hg,trueData_valid hm⟩

end DataProducer
end ExactQuantumFactoring


end

end OAI
