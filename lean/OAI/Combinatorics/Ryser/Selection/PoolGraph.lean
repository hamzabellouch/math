import OAI.Combinatorics.Ryser.Selection.Definitions
import OAI.Combinatorics.Ryser.Domination.Main

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [DecidableEq F] {n K : ℕ}

def candidateGraph (data : Data F n) (pool : Pool F n K) :
    Graph (Position n K) where
  Adj e f := e.1 ≠ f.1 ∧ Conflict data e.1 f.1 (pool e) (pool f)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem candidateGraph_adj (data : Data F n) (pool : Pool F n K)
    (e f : Position n K) :
    (candidateGraph data pool).Adj e f ↔
      e.1 ≠ f.1 ∧ Conflict data e.1 f.1 (pool e) (pool f) := Iff.rfl

theorem compatibleChoice_of_transversal (data : Data F n) (pool : Pool F n K)
    {U : Finset (Position n K)}
    (hU : IsTransversalOn (candidateGraph data pool) Prod.fst Finset.univ U) :
    HasCompatibleChoice data pool := by
  classical
  have hex (i : Fin n) : ∃ k : Fin K, (i, k) ∈ U := by
    have hi : i ∈ U.image Prod.fst := by
      rw [hU.2.2]
      exact Finset.mem_univ i
    obtain ⟨⟨j, k⟩, hjk, hji⟩ := Finset.mem_image.mp hi
    change j = i at hji
    subst j
    exact ⟨k, hjk⟩
  let choice : Fin n → Fin K := fun i => Classical.choose (hex i)
  have hchoice (i : Fin n) : (i, choice i) ∈ U := Classical.choose_spec (hex i)
  refine ⟨choice, ?_⟩
  intro i j hij hconflict
  exact hU.1 (i, choice i) (hchoice i) (j, choice j) (hchoice j)
    ⟨hij, hconflict⟩

theorem transversal_of_compatibleChoice (data : Data F n) (pool : Pool F n K)
    (h : HasCompatibleChoice data pool) :
    ∃ U : Finset (Position n K),
      IsTransversalOn (candidateGraph data pool) Prod.fst Finset.univ U := by
  classical
  obtain ⟨choice, hchoice⟩ := h
  refine ⟨Finset.univ.image (fun i : Fin n => (i, choice i)), ?_, ?_, ?_⟩
  · intro e he f hf hadj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    exact hchoice i j hadj.1 hadj.2
  · intro e he f hf hfst
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    change i = j at hfst
    subst j
    rfl
  · apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact Finset.mem_image.mpr ⟨(i, choice i),
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, rfl⟩

theorem transversal_iff_hasCompatibleChoice (data : Data F n) (pool : Pool F n K) :
    (∃ U : Finset (Position n K),
      IsTransversalOn (candidateGraph data pool) Prod.fst Finset.univ U) ↔
        HasCompatibleChoice data pool := by
  constructor
  · rintro ⟨U, hU⟩
    exact compatibleChoice_of_transversal data pool hU
  · exact transversal_of_compatibleChoice data pool

theorem position_fst_surjective (hK : 0 < K) :
    Function.Surjective (Prod.fst : Position n K → Fin n) :=
  fun i => ⟨(i, ⟨0, hK⟩), rfl⟩

theorem not_hasCompatibleChoice_domination (data : Data F n) (pool : Pool F n K)
    (hK : 0 < K) (hbad : ¬ HasCompatibleChoice data pool) :
    ∃ I : Finset (Fin n), ∃ T : Finset (Position n K), I.Nonempty ∧
      T ⊆ Finset.univ.filter (fun e => e.1 ∈ I) ∧
      T.card ≤ 2 * (I.card - 1) ∧
      DominatesOn (candidateGraph data pool) Prod.fst I T := by
  apply domination_of_no_transversal (candidateGraph data pool) Prod.fst
    (position_fst_surjective hK)
  intro htransversal
  exact hbad ((transversal_iff_hasCompatibleChoice data pool).mp htransversal)

theorem not_feasible_of_dominates (data : Data F n) (pool : Pool F n K)
    {I : Finset (Fin n)} {T : Finset (Position n K)}
    (hdom : DominatesOn (candidateGraph data pool) Prod.fst I T)
    {e : Position n K} (he : e.1 ∈ I) (heT : e ∉ T) :
    ¬ Feasible data T pool e.1 (pool e) := by
  intro hfeasible
  obtain ⟨f, hf, hadj⟩ := hdom e he heT
  exact hfeasible f hf hadj.2

theorem not_hasCompatibleChoice_obstruction (data : Data F n) (pool : Pool F n K)
    (hK : 0 < K) (hbad : ¬ HasCompatibleChoice data pool) :
    ∃ I : Finset (Fin n), ∃ T : Finset (Position n K), I.Nonempty ∧
      T ⊆ Finset.univ.filter (fun e => e.1 ∈ I) ∧
      T.card ≤ 2 * I.card ∧
      ∀ e : Position n K, e.1 ∈ I → e ∉ T →
        ¬ Feasible data T pool e.1 (pool e) := by
  obtain ⟨I, T, hI, hT, hcard, hdom⟩ :=
    not_hasCompatibleChoice_domination data pool hK hbad
  refine ⟨I, T, hI, hT, ?_, ?_⟩
  · exact hcard.trans (Nat.mul_le_mul_left 2 (Nat.sub_le I.card 1))
  · intro e he heT
    exact not_feasible_of_dominates data pool hdom he heT

end RyserCoveringCounterexample.Selection

end OAI
