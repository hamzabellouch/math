import OAI.Probability.SATVariance.LifetimePotential

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def clauseRead {n k : ℕ} (c : Clause n k) (v : Fin n) : Option Bool :=
  if h : v ∈ c.1.1 then some (c.2 ⟨v,h⟩) else none

lemma clauseRead_isSome {n k : ℕ} (c : Clause n k) (v : Fin n) :
    (clauseRead c v).isSome ↔ v ∈ c.1.1 := by
  simp only [clauseRead]
  split <;> simp_all

lemma clause_ext {n k : ℕ} {c d : Clause n k}
    (h : ∀ v, clauseRead c v = clauseRead d v) : c = d := by
  have hs : c.1 = d.1 := by
    apply Subtype.ext
    ext v
    rw [← clauseRead_isSome, ← clauseRead_isSome, h]
  rcases c with ⟨s,f⟩
  rcases d with ⟨t,g⟩
  dsimp only at hs
  subst t
  have hf : f = g := by
    funext v
    have hh := h v
    simpa [clauseRead, v.property] using hh
  subst g
  rfl

lemma satisfies_iff_read {n k : ℕ} (c : Clause n k) (a : Assignment n) :
    Satisfies c a ↔ ∃ v, clauseRead c v = some (a v) := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v, by simp [clauseRead, v.property, hv]⟩
  · rintro ⟨v,hv⟩
    unfold clauseRead at hv
    split_ifs at hv with h
    exact ⟨⟨v,h⟩, (Option.some.inj hv).symm⟩

abbrev RootType (k : ℕ) := Fin k → Option Bool

def rootSupport {k : ℕ} (t : RootType k) : Finset (Fin k) :=
  Finset.univ.filter fun j => (t j).isSome

def rootSize {k : ℕ} (t : RootType k) : ℕ := (rootSupport t).card

lemma rootSize_le {k : ℕ} (t : RootType k) : rootSize t ≤ k := by
  simpa [rootSize] using (Finset.card_le_univ (rootSupport t))

def mergeClause {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) : Clause n k :=
  ⟨⟨((rootSupport t).disjSum c.1.1).map e.toEmbedding, by
      rw [Finset.card_map, Finset.card_disjSum, c.1.property]
      exact Nat.add_sub_of_le (rootSize_le t)⟩,
    fun v => match e.symm v with
      | Sum.inl j => (t j).getD false
      | Sum.inr j => (clauseRead c j).getD false⟩

lemma mem_merge_inl {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin k) :
    e (Sum.inl j) ∈ (mergeClause e t c).1.1 ↔ (t j).isSome := by
  simp [mergeClause, rootSupport]

lemma mem_merge_inr {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin u) :
    e (Sum.inr j) ∈ (mergeClause e t c).1.1 ↔ j ∈ c.1.1 := by
  simp [mergeClause]

lemma read_merge_inl {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin k) :
    clauseRead (mergeClause e t c) (e (Sum.inl j)) = t j := by
  have hm := mem_merge_inl e t c j
  unfold clauseRead
  split_ifs with h
  · have ht : (t j).isSome := hm.mp h
    cases hx : t j with
    | none => simp [hx] at ht
    | some b => simp [mergeClause, hx]
  · have ht : ¬(t j).isSome := mt hm.mpr h
    cases hx : t j with
    | none => rfl
    | some b => simp [hx] at ht

lemma read_merge_inr {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (j : Fin u) :
    clauseRead (mergeClause e t c) (e (Sum.inr j)) = clauseRead c j := by
  have hm := mem_merge_inr e t c j
  by_cases h : j ∈ c.1.1
  · simp [clauseRead, mergeClause, h]
  · simp [clauseRead, mt hm.mp h, h]

lemma mergeClause_injective {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    Function.Injective (fun p : (t : RootType k) × Clause u (k-rootSize t) =>
      mergeClause e p.1 p.2) := by
  rintro ⟨t,c⟩ ⟨s,d⟩ h
  have ht : t = s := by
    funext j
    have hh := congrArg (fun x => clauseRead x (e (Sum.inl j))) h
    simpa only [read_merge_inl] using hh
  subst s
  have hc : c = d := by
    apply clause_ext
    intro j
    have hh := congrArg (fun x => clauseRead x (e (Sum.inr j))) h
    simpa only [read_merge_inr] using hh
  subst d
  rfl

def rootRead {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) : RootType k :=
  fun j => clauseRead c (e (Sum.inl j))

def partSupport {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) : Finset (Fin u) :=
  Finset.univ.filter fun j => e (Sum.inr j) ∈ c.1.1

lemma split_support {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) :
    (rootSupport (rootRead e c)).disjSum (partSupport e c) = c.1.1.map e.symm.toEmbedding := by
  ext z
  cases z <;> simp [rootSupport, rootRead, partSupport, clauseRead_isSome]

lemma partSupport_card {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) :
    (partSupport e c).card = k-rootSize (rootRead e c) := by
  have hh := congrArg Finset.card (split_support e c)
  rw [Finset.card_disjSum, Finset.card_map, c.1.property] at hh
  change rootSize (rootRead e c) + _ = k at hh
  omega

def partRead {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) :
    Clause u (k-rootSize (rootRead e c)) :=
  ⟨⟨partSupport e c, partSupport_card e c⟩,
    fun v => c.2 ⟨e (Sum.inr v), by simpa [partSupport] using v.property⟩⟩

lemma read_partRead {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) (c : Clause n k) (j : Fin u) :
    clauseRead (partRead e c) j = clauseRead c (e (Sum.inr j)) := by
  by_cases h : e (Sum.inr j) ∈ c.1.1
  · simp [clauseRead, partRead, partSupport, h]
  · simp [clauseRead, partRead, partSupport, h]

lemma mergeClause_surjective {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    Function.Surjective (fun p : (t : RootType k) × Clause u (k-rootSize t) =>
      mergeClause e p.1 p.2) := by
  intro c
  refine ⟨⟨rootRead e c, partRead e c⟩, ?_⟩
  apply clause_ext
  intro v
  obtain ⟨z,rfl⟩ := e.surjective v
  cases z with
  | inl j => exact read_merge_inl e _ _ j
  | inr j => rw [read_merge_inr, read_partRead]

def splitClauseEquiv {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n) :
    ((t : RootType k) × Clause u (k-rootSize t)) ≃ Clause n k :=
  Equiv.ofBijective _ ⟨mergeClause_injective e, mergeClause_surjective e⟩

def RootSatisfies {k : ℕ} (t : RootType k) (a : Assignment k) : Prop :=
  ∃ j, t j = some (a j)

lemma satisfies_merge {n k u : ℕ} (e : Fin k ⊕ Fin u ≃ Fin n)
    (t : RootType k) (c : Clause u (k-rootSize t)) (a : Assignment n) :
    Satisfies (mergeClause e t c) a ↔
      RootSatisfies t (fun j => a (e (Sum.inl j))) ∨
      Satisfies c (fun j => a (e (Sum.inr j))) := by
  rw [satisfies_iff_read, satisfies_iff_read]
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨z,rfl⟩ := e.surjective v
    cases z with
    | inl j => exact Or.inl ⟨j, by simpa only [read_merge_inl] using hv⟩
    | inr j => exact Or.inr ⟨j, by simpa only [read_merge_inr] using hv⟩
  · rintro (⟨j,hj⟩ | ⟨j,hj⟩)
    · exact ⟨e (Sum.inl j), by simpa only [read_merge_inl] using hj⟩
    · exact ⟨e (Sum.inr j), by simpa only [read_merge_inr] using hj⟩

end RandomKSAT

end

end OAI
