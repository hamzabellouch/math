import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.TerminalStream

namespace OAI

namespace SharpRamseyFive.FlagConstruction

open scoped LinearAlgebra.Projectivization
open Module

variable {K : Type*} [Field K]
abbrev Space (K : Type*) := Fin 5 → K
abbrev Point (K : Type*) [Field K] := ℙ K (Space K)
abbrev DualPoint (K : Type*) [Field K] := ℙ K (Module.Dual K (Space K))

def Incident (a : Point K) (b : DualPoint K) : Prop :=
  a.submodule ≤ LinearMap.ker b.rep

lemma incident_iff (a : Point K) (b : DualPoint K) :
    Incident a b ↔ b.rep a.rep = 0 := by
  rw [Incident, Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    LinearMap.mem_ker]

abbrev Flag (K : Type*) [Field K] :=
  {ab : Point K × DualPoint K // Incident ab.1 ab.2}

def graph {N : ℕ} (X : Fin N → Flag K) : SimpleGraph (Fin N) where
  Adj i j := (i < j ∧ Incident (X i).1.1 (X j).1.2 ∧
      ¬ Incident (X j).1.1 (X i).1.2) ∨
    (j < i ∧ Incident (X j).1.1 (X i).1.2 ∧
      ¬ Incident (X i).1.1 (X j).1.2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; simp⟩

lemma adj_iff_of_lt {N : ℕ} (X : Fin N → Flag K) {i j : Fin N} (h : i < j) :
    (graph X).Adj i j ↔ Incident (X i).1.1 (X j).1.2 ∧
      ¬ Incident (X j).1.1 (X i).1.2 := by
  simp only [graph, h, true_and, not_lt_of_ge h.le, false_and, or_false]

private lemma five_independent {v : Fin 5 → Space K}
    {b : Fin 5 → Module.Dual K (Space K)} (hv : v 0 ≠ 0)
    (hz : ∀ i j, i ≤ j → b j (v i) = 0)
    (hn : ∀ i j, i < j → b i (v j) ≠ 0) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : c 0 • v 0 + c 1 • v 1 + c 2 • v 2 + c 3 • v 3 + c 4 • v 4 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hc
  have h4 : c 4 = 0 := by
    have h := congrArg (b 3) hsum
    simp only [map_add, map_smul, map_zero] at h
    simp only [hz 0 3 (by decide), hz 1 3 (by decide), hz 2 3 (by decide),
      hz 3 3 le_rfl, smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 3 4 (by decide))
  have h3 : c 3 = 0 := by
    have h := congrArg (b 2) hsum
    simp only [map_add, map_smul, map_zero, h4, zero_smul, add_zero] at h
    simp only [hz 0 2 (by decide), hz 1 2 (by decide), hz 2 2 le_rfl,
      smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 2 3 (by decide))
  have h2 : c 2 = 0 := by
    have h := congrArg (b 1) hsum
    simp only [map_add, map_smul, map_zero, h4, h3, zero_smul, add_zero] at h
    simp only [hz 0 1 (by decide), hz 1 1 le_rfl, smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 1 2 (by decide))
  have h1 : c 1 = 0 := by
    have h := congrArg (b 0) hsum
    simp only [map_add, map_smul, map_zero, h4, h3, h2, zero_smul, add_zero] at h
    simp only [hz 0 0 le_rfl, smul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (hn 0 1 (by decide))
  have h0 : c 0 = 0 := by
    simp only [h4, h3, h2, h1, zero_smul, add_zero] at hsum
    exact (smul_eq_zero.mp hsum).resolve_right hv
  intro i
  fin_cases i <;> assumption

theorem cliqueFree_five {N : ℕ} (X : Fin N → Flag K) : (graph X).CliqueFree 5 := by
  intro s hs
  let e : Fin 5 ↪o Fin N := s.orderEmbOfFin hs.card_eq
  have he (i : Fin 5) : e i ∈ s := s.orderEmbOfFin_mem hs.card_eq i
  have hadj (i j : Fin 5) (hij : i < j) :
      Incident (X (e i)).1.1 (X (e j)).1.2 ∧
      ¬ Incident (X (e j)).1.1 (X (e i)).1.2 := by
    apply (adj_iff_of_lt X (e.strictMono hij)).mp
    exact hs.isClique (he i) (he j) (ne_of_lt (e.strictMono hij))
  let v : Fin 5 → Space K := fun i => (X (e i)).1.1.rep
  let b : Fin 5 → Module.Dual K (Space K) := fun i => (X (e i)).1.2.rep
  have hz (i j : Fin 5) (hij : i ≤ j) : b j (v i) = 0 := by
    apply (incident_iff _ _).mp
    rcases lt_or_eq_of_le hij with h | rfl
    · exact (hadj i j h).1
    · exact (X (e i)).2
  have hn (i j : Fin 5) (hij : i < j) : b i (v j) ≠ 0 := by
    exact fun h => (hadj i j hij).2 ((incident_iff _ _).mpr h)
  have hli : LinearIndependent K v := five_independent (Projectivization.rep_nonzero _) hz hn
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Space])
  have hker : Submodule.span K (Set.range v) ≤ LinearMap.ker (b 4) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hz i 4 (by omega)
  rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hker
  exact (X (e 4)).1.2.rep_nonzero hker

end SharpRamseyFive.FlagConstruction

namespace SharpRamseyFive.FlagConstruction
open Module SharpRamseyFive.Marking SharpRamseyFive.FiniteEntropy SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K : Type*} [Field K] {N n : ℕ}

lemma independent_selector_of_not_cliqueFree (X : Fin N → Flag K)
    (h : ¬(graph X)ᶜ.CliqueFree n) :
    ∃ e : Fin n ↪o Fin N, TupleIncident (fun i=>(X (e i)).val) ∧
      TupleConsistent (fun i=>(X (e i)).val) := by
  rw [SimpleGraph.CliqueFree] at h
  push Not at h
  obtain ⟨s,hs⟩:=h
  let e : Fin n ↪o Fin N:=s.orderEmbOfFin hs.card_eq
  have he : ∀ i,e i∈s := fun i=>s.orderEmbOfFin_mem hs.card_eq i
  refine ⟨e,fun i=>(X (e i)).property,?_⟩
  intro i j hij hab
  by_contra hba
  have hadj:=hs.isClique (he i) (he j) (ne_of_lt (e.strictMono hij))
  have hg : (graph X).Adj (e i) (e j) :=
    (adj_iff_of_lt X (e.strictMono hij)).mpr ⟨hab,hba⟩
  exact hadj.2 hg

variable [Nonempty (Flag K)]
def encodeRaw (z : FlagPair K (Space K)) : Flag K :=
  if h : Incident z.1 z.2 then ⟨z,h⟩ else Classical.choice inferInstance

lemma encodeRaw_leftInverse : Function.LeftInverse (encodeRaw (K:=K)) Subtype.val := by
  intro x
  apply Subtype.ext
  simp only [encodeRaw,dite_eq_left x.property]

variable [Fintype (Point K)] [Fintype (DualPoint K)]

theorem initial_consistent_stream (hn : n≤N) (admissible : (Fin N → Flag K) → Prop)
    (E : Finset (Fin N → Flag K))
    (hE : 0<eventMass (iid (uniform Fintype.card_pos) (Fin N)) E)
    (hgood : ∀ s,s∈E → admissible s)
    (hno : ∀ s : Fin N → Flag K, ¬(graph s)ᶜ.CliqueFree n) :
    ∃ S : SelectedStream (Ω:=Fin N → Flag K) (β:=FlagPair K (Space K)) N n admissible,
      S.density=1/eventMass (iid (uniform Fintype.card_pos) (Fin N)) E ∧
      ∀ s,0<S.law s → TupleIncident (S.tuple s) ∧ TupleConsistent (S.tuple s) := by
  exact initial_selected_exists hn admissible (fun x=>TupleIncident x ∧ TupleConsistent x)
    E hE hgood Subtype.val encodeRaw encodeRaw_leftInverse
    (fun s _=>independent_selector_of_not_cliqueFree s (hno s))
end
end SharpRamseyFive.FlagConstruction

namespace SharpRamseyFive.Marking
open Module SelectedTuple FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n l : ℕ}
lemma tupleIncident_comp (x : Fin n → FlagPair K V) (h : TupleIncident x)
    (e : Fin l → Fin n) : TupleIncident (x ∘ e) := fun i=>h (e i)
lemma tupleConsistent_comp (x : Fin n → FlagPair K V) (h : TupleConsistent x)
    (e : Fin l ↪o Fin n) : TupleConsistent (x ∘ e) :=
  fun i j hij=>h (e i) (e j) (e.strictMono hij)
lemma retained_incident (hl : l≤n) (x : Fin n → FlagPair K V) (h : TupleIncident x)
    (S : Finset (Fin n)) : TupleIncident (retainedTuple hl x S) := by
  apply tupleIncident_comp x h
lemma retained_consistent (hl : l≤n) (x : Fin n → FlagPair K V) (h : TupleConsistent x)
    (S : Finset (Fin n)) : TupleConsistent (retainedTuple hl x S) := by
  apply tupleConsistent_comp x h
end SharpRamseyFive.Marking

end OAI
