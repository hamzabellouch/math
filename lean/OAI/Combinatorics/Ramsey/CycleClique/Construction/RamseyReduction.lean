import OAI.Combinatorics.Ramsey.CycleClique.Construction.Reduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Monotonicity

namespace OAI

/-! The precise minimal-parameter reduction in manuscript Section 2. -/

namespace CycleClique.Construction
variable {V : Type*} [Fintype V]

theorem cycleNext_ne_self {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : cycleNext i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (i.val + 1) % m = i.val at hv
  by_cases hi : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have he : i.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hv
    omega

theorem complete_hasCycle {G : SimpleGraph V} {m : ℕ} (hm : 2 ≤ m)
    (hcomplete : ∀ x y, x ≠ y → G.Adj x y) (hcard : m ≤ Fintype.card V) :
    HasCycle G m := by
  classical
  obtain ⟨I, _, hI⟩ := Finset.exists_subset_card_eq
    (show m ≤ (Finset.univ : Finset V).card by simpa using hcard)
  let e : Fin m ≃ I := (Finset.equivFinOfCardEq hI).symm
  let f : Fin m → V := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  refine ⟨f, hf, fun i => hcomplete _ _ ?_⟩
  exact fun h => cycleNext_ne_self hm i (hf h).symm

omit [Fintype V] in
theorem independent_pair {G : SimpleGraph V} {x y : V} (hne : x ≠ y)
    (hadj : ¬ G.Adj x y) : HasIndependent G 2 := by
  refine ⟨![x, y], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j
    have hyx : ¬ G.Adj y x := fun h => hadj h.symm
    fin_cases i <;> fin_cases j <;> simp_all

theorem independenceBound_zero {G : SimpleGraph V} (h : IndependenceBound G 0) :
    Fintype.card V = 0 := by
  classical
  have hempty : IsEmpty V := ⟨fun v => by
    have hs : G.IsIndepSet (({v} : Finset V) : Set V) := by simp
    have := h {v} hs
    simp at this⟩
  exact Fintype.card_eq_zero

theorem independenceBound_one {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hcycle : ¬ HasCycle G (k + 1)) (h : IndependenceBound G 1) :
    Fintype.card V ≤ k := by
  have hn : ¬ HasIndependent G 2 := independenceBound_iff_not_hasIndependent.mp h
  have hcomplete : ∀ x y, x ≠ y → G.Adj x y := by
    intro x y hxy
    by_contra hnon
    exact hn (independent_pair hxy hnon)
  by_contra hcard
  exact hcycle (complete_hasCycle (by omega) hcomplete (by omega))

/-- A Ramsey property bounds every larger cycle-free graph with the given
independence bound, by restricting it to exactly the forcing order. -/
theorem card_lt_of_ramseyProperty {G : SimpleGraph V} {m n N : ℕ}
    (hRamsey : RamseyProperty m (n + 1) N)
    (hcycle : ¬ HasCycle G m) (hbound : IndependenceBound G n) :
    Fintype.card V < N := by
  classical
  by_contra hcard
  obtain ⟨I, _, hI⟩ := Finset.exists_subset_card_eq
    (show N ≤ (Finset.univ : Finset V).card by simpa using (show N ≤ Fintype.card V by omega))
  let e : Fin N ≃ I := (Finset.equivFinOfCardEq hI).symm
  let f : Fin N → V := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  rcases hRamsey (G.comap f) with hc | hi
  · exact hcycle (hc.map f hf (fun h => h))
  · exact (independenceBound_iff_not_hasIndependent.mp hbound)
      (hi.map f hf (fun h => h))

/-- Manuscript Lemma `red:smaller`, including the zero and one cases. -/
theorem smaller_parameter_bound {k a b : ℕ} (hk : 3 ≤ k) (hb : b < a)
    (hprior : ∀ c, 2 ≤ c → c < a → RamseyProperty (k + 1) (c + 1) (k * c + 1))
    (G : SimpleGraph V) (hcycle : ¬ HasCycle G (k + 1))
    (hbound : IndependenceBound G b) : Fintype.card V ≤ k * b := by
  by_cases hb0 : b = 0
  · subst b
    simp [independenceBound_zero hbound]
  by_cases hb1 : b = 1
  · subst b
    simpa using independenceBound_one (by omega) hcycle hbound
  have hc := card_lt_of_ramseyProperty (hprior b (by omega) hb) hcycle hbound
  omega

/-- The expansion premise is supplied by induction on the independence
parameter, rather than assumed as an additional graph theorem. -/
theorem expansion_of_smaller_ramsey {k a : ℕ} (hk : 3 ≤ k)
    (hprior : ∀ b, 2 ≤ b → b < a → RamseyProperty (k + 1) (b + 1) (k * b + 1))
    (G : SimpleGraph V) (hcard : Fintype.card V = k * a + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hbound : IndependenceBound G a)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    k * I.card + 1 ≤ (closedNeighborhood G I).card := by
  classical
  apply minimal_counterexample_expansion hcard hcycle hbound
    (fun b hb Y hcy hi => ?_) I hI hne
  simpa using smaller_parameter_bound hk hb hprior
    (G.induce (Y : Set V)) hcy hi

/-- A failure in the main range supplies precisely the expanded graph
used by the rest of the manuscript, at the least failed parameter. -/
theorem exists_minimal_counterexample {k a₀ : ℕ} (hk : 3 ≤ k)
    (ha₀ : 2 ≤ a₀) (ha₀k : a₀ ≤ k)
    (hfail : ¬ RamseyProperty (k + 1) (a₀ + 1) (k * a₀ + 1)) :
    ∃ (a : ℕ) (G : SimpleGraph (Fin (k * a + 1))),
      2 ≤ a ∧ a ≤ k ∧ ¬ HasCycle G (k + 1) ∧ IndependenceBound G a ∧
      ∀ I : Finset (Fin (k * a + 1)),
        G.IsIndepSet (I : Set _) → I.Nonempty →
        k * I.card + 1 ≤ (closedNeighborhood G I).card := by
  classical
  let P : ℕ → Prop := fun a =>
    2 ≤ a ∧ a ≤ k ∧ ¬ RamseyProperty (k + 1) (a + 1) (k * a + 1)
  have hex : ∃ a, P a := ⟨a₀, ha₀, ha₀k, hfail⟩
  let a := Nat.find hex
  obtain ⟨ha, hak, hbad⟩ := Nat.find_spec hex
  have hprior : ∀ b, 2 ≤ b → b < a →
      RamseyProperty (k + 1) (b + 1) (k * b + 1) := by
    intro b hb hba
    by_contra h
    exact Nat.find_min hex hba ⟨hb, by omega, h⟩
  change ¬ ∀ G : SimpleGraph (Fin (k * a + 1)),
    HasCycle G (k + 1) ∨ HasIndependent G (a + 1) at hbad
  obtain ⟨G, hG⟩ := not_forall.mp hbad
  obtain ⟨hcy, hi⟩ := not_or.mp hG
  have hbound : IndependenceBound G a := independenceBound_iff_not_hasIndependent.mpr hi
  refine ⟨a, G, ha, hak, hcy, hbound, ?_⟩
  intro I hI hne
  exact expansion_of_smaller_ramsey hk hprior G (Fintype.card_fin _) hcy hbound I hI hne

end CycleClique.Construction

end OAI
