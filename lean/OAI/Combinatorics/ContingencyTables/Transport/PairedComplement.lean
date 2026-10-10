import OAI.Combinatorics.ContingencyTables.Transport.DegreeCompletion

namespace OAI

/-!
# Complementation of paired conditional masses

Complementing a transversal assignment swaps its fixed inclusions and
exclusions and reverses the empty/full defect labels. These are identities
of the actual finite coefficient sums, used to keep the omission and
addition roles of the two factorial lifts separate.
-/

namespace ContingencyTables.PairedComplement

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

lemma paired_children (ps : List (Γ × Γ)) (A B : Set Γ) (p : Γ × Γ)
    (hAB : Disjoint A B) (hps : SlotsFresh (p::ps) (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport (p::ps) = Set.univ) :
    Disjoint (insert p.1 A) (insert p.2 B) ∧
      SlotsFresh ps (insert p.1 A ∪ insert p.2 B) ∧
      insert p.1 A ∪ insert p.2 B ∪ pairSupport ps = Set.univ := by
  obtain ⟨hp, ha, hb, ht⟩ := hps
  refine ⟨?_, ht.mono ?_, ?_⟩
  · simp only [Set.disjoint_insert_left, Set.disjoint_insert_right, Set.mem_insert_iff,
      not_or]
    exact ⟨⟨hp.symm, fun h => hb (Or.inl h)⟩, fun h => ha (Or.inr h), hAB⟩
  · intro x hx
    simp only [Set.mem_union, Set.mem_insert_iff] at hx ⊢
    tauto
  · rw [← hcover, pairSupport_cons]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto

/-- Exact complement identity for a residual paired choice sum. -/
theorem slotTotal_complement (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ) :
    slotTotal ps (complementWeight f) A = slotTotal ps f B := by
  induction ps generalizing A B with
  | nil =>
    have hcompl : Aᶜ = B := by
      ext x
      have hx : x ∈ A ∪ B := by
        have h := Set.mem_univ x
        rw [← hcover] at h
        simpa using h
      constructor
      · intro ha
        exact hx.resolve_left ha
      · intro hb ha
        exact Set.disjoint_left.mp hAB ha hb
    simp only [slotTotal_nil, complementWeight, hcompl]
  | cons p ps ih =>
    have hA := hps.mono Set.subset_union_left
    have hB := hps.mono Set.subset_union_right
    obtain ⟨hd₁, hf₁, hc₁⟩ := paired_children ps A B p hAB hps hcover
    have hswap : SlotsFresh ((p.2,p.1)::ps) (A ∪ B) := by
      refine ⟨hps.1.symm, hps.2.2.1, hps.2.1, ?_⟩
      convert hps.2.2.2 using 1
      ext x
      simp only [Set.mem_insert_iff]
      tauto
    have hcovswap : A ∪ B ∪ pairSupport ((p.2,p.1)::ps) = Set.univ := by
      rw [← hcover, pairSupport_cons, pairSupport_cons]
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff]
      tauto
    obtain ⟨hd₂, hf₂, hc₂⟩ := paired_children ps A B (p.2,p.1) hAB hswap hcovswap
    rw [slotTotal_cons p ps _ A hA.1 hA.2.1 hA.2.2.1,
      slotTotal_cons p ps _ B hB.1 hB.2.1 hB.2.2.1,
      ih _ _ hd₁ hf₁ hc₁, ih _ _ hd₂ hf₂ hc₂, add_comm]

omit [Fintype Γ] in
lemma VarianceNode.cover {gs ps : List (Γ × Γ)} {A B : Set Γ}
    (hnode : VarianceNode gs ps A B) (hcover : pairSupport gs = Set.univ) :
    A ∪ B ∪ pairSupport ps = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ pairSupport gs := hcover ▸ Set.mem_univ x
  obtain ⟨r, hr, hx⟩ := hx
  by_cases hm : r ∈ ps
  · exact Or.inr ⟨r, hm, hx⟩
  · rcases hnode.2.2.2 r hr hm with h | h
    · rcases hx with rfl | rfl
      · exact Or.inl (Or.inl h.1)
      · exact Or.inl (Or.inr h.2)
    · rcases hx with rfl | rfl
      · exact Or.inl (Or.inr h.2)
      · exact Or.inl (Or.inl h.1)

omit [Fintype Γ] [DecidableEq Γ] in
lemma VarianceNode.complement {gs ps : List (Γ × Γ)} {A B : Set Γ}
    (hnode : VarianceNode gs ps A B) : VarianceNode gs ps B A := by
  refine ⟨hnode.1.symm, ?_, hnode.2.2.1, ?_⟩
  · simpa only [Set.union_comm] using hnode.2.1
  · intro r hr hn
    rcases hnode.2.2.2 r hr hn with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

/-- Complementation reverses the two distinguished defect labels. -/
theorem slotDefect_complement (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    slotDefect ps (complementWeight f) A p r = slotDefect ps f B r p := by
  let qs := (ps.erase p).erase r
  have hperm : ps.Perm (p::r::qs) := slots_perm_two hp hr hpr
  have hh := (SlotsFresh.perm hperm (A ∪ B)).mp hps
  have hcov : A ∪ B ∪ pairSupport (p::r::qs) = Set.univ := by
    rwa [← pairSupport_perm hperm]
  have hfr : SlotsFresh qs ((insert r.1 (insert r.2 A)) ∪ insert p.1 (insert p.2 B)) := by
    apply hh.2.2.2.2.2.2.mono
    intro x hx
    simp only [Set.mem_union, Set.mem_insert_iff] at hx ⊢
    tauto
  have hab : Disjoint (insert r.1 (insert r.2 A)) (insert p.1 (insert p.2 B)) := by
    have hp₁ : p.1 ∉ A ∪ B := hh.2.1
    have hp₂ : p.2 ∉ A ∪ B := hh.2.2.1
    have hr₁ := hh.2.2.2.2.1
    have hr₂ := hh.2.2.2.2.2.1
    simp only [Set.mem_insert_iff, Set.mem_union, not_or] at hp₁ hp₂ hr₁ hr₂
    apply Set.disjoint_left.mpr
    intro x hx hy
    simp only [Set.mem_insert_iff] at hx hy
    rcases hx with rfl | rfl | hx
    · tauto
    · tauto
    · rcases hy with rfl | rfl | hy
      · tauto
      · tauto
      · exact Set.disjoint_left.mp hAB hx hy
  have hc : insert r.1 (insert r.2 A) ∪ insert p.1 (insert p.2 B) ∪ pairSupport qs = Set.univ := by
    rw [← hcov, pairSupport_cons, pairSupport_cons]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  unfold slotDefect
  rw [List.erase_comm r p]
  exact slotTotal_complement qs f _ _ hab hfr hc

/-- The complementary second lift satisfies the same oriented defect
inequalities, although its raw signature role is omission rather than addition. -/
theorem complement_defect_pair (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (hdegree : B.ncard + ps.length = k)
    (p r : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    4 * slotDefect ps (complementWeight f) A p r *
      slotDefect ps (complementWeight f) A r p ≤ (slotTotal ps (complementWeight f) A)^2 := by
  rw [slotDefect_complement ps f A B hAB hps hcover p r hp hr hpr,
    slotDefect_complement ps f A B hAB hps hcover r p hr hp hpr.symm,
    slotTotal_complement ps f A B hAB hps hcover]
  exact slotDefect_pair_bound_degree ps f k hf hsig B hdegree
    (hps.mono Set.subset_union_right) r p hr hp hpr.symm

/-- Reversing all defect labels preserves the three-pair cross-entry bound. -/
theorem complement_defect_triple (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (k : ℕ)
    (hf : DegreePositive f k) (hsig : AdditionProperty f k)
    (A B : Set Γ) (hAB : Disjoint A B) (hps : SlotsFresh ps (A ∪ B))
    (hcover : A ∪ B ∪ pairSupport ps = Set.univ)
    (hdegree : B.ncard + ps.length = k)
    (p r t : Γ × Γ) (hp : p ∈ ps) (hr : r ∈ ps) (ht : t ∈ ps)
    (hpr : p ≠ r) (hrt : r ≠ t) (hpt : p ≠ t) :
    slotDefect ps (complementWeight f) A p r * slotDefect ps (complementWeight f) A r t ≤
      slotTotal ps (complementWeight f) A * slotDefect ps (complementWeight f) A p t := by
  rw [slotDefect_complement ps f A B hAB hps hcover p r hp hr hpr,
    slotDefect_complement ps f A B hAB hps hcover r t hr ht hrt,
    slotDefect_complement ps f A B hAB hps hcover p t hp ht hpt,
    slotTotal_complement ps f A B hAB hps hcover]
  simpa only [mul_comm] using slotDefect_triple_bound_degree ps f k hf hsig B hdegree
    (hps.mono Set.subset_union_right) t r p ht hr hp hrt.symm hpr.symm hpt.symm

end ContingencyTables.PairedComplement

end OAI
