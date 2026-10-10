import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CoarseAssignment

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointAssignmentLoss

open JointExtraction JointCoarseAssignment

attribute [local instance] Classical.propDecidable

variable {A B C I V Ω : Type*}

theorem uniqueAssignment_of_unique (candidates : Finset I)
    (compatible : I → V → Prop) (v : V) (i : I)
    (hi : i ∈ candidates) (hc : compatible i v)
    (hu : ∀ j, j ∈ candidates → compatible j v → j = i) :
    uniqueAssignment candidates compatible v = some i := by
  classical
  have hex : ∃ j, j ∈ candidates ∧ compatible j v ∧
      ∀ k, k ∈ candidates → compatible k v → k = j := ⟨i, hi, hc, hu⟩
  unfold uniqueAssignment
  rw [dite_eq_left hex]
  exact congrArg some (hu _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2.1)

theorem assignUseful_of_unique (candidates : Finset I)
    (compatible useful : I → V → Prop) (v : V) (i : I)
    (hi : i ∈ candidates) (hc : compatible i v) (huse : useful i v)
    (hu : ∀ j, j ∈ candidates → compatible j v → j = i) :
    assignUseful candidates compatible useful v = some i := by
  have hassign := uniqueAssignment_of_unique candidates compatible v i hi hc hu
  have hkeep : ∃ j, uniqueAssignment candidates compatible v = some j ∧ useful j v :=
    ⟨i, hassign, huse⟩
  simp only [assignUseful, retainAssignment, ite_eq_left hkeep]
  exact hassign

def ambientXCollision (ambient : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C) : Prop :=
  ∃ f ∈ ambient, f ≠ e ∧ survives hx hy hz f ∧ f.1 = e.1

def targetCompatibleCollision (targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible : Triple A B C → V → Prop) (e : Triple A B C) (v : V) : Prop :=
  ∃ f ∈ targets, f ≠ e ∧ survives hx hy hz f ∧ compatible f v

theorem eligible_of_no_ambientXCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e)
    (hno : ¬ ambientXCollision ambient hx hy hz e) :
    e ∈ eligible ambient targets hx hy hz := by
  apply (mem_eligible_iff ambient targets hx hy hz e).2
  refine ⟨ha, ht, hs, ?_⟩
  intro f hf hfs hfx
  by_contra hne
  exact hno ⟨f, hf, hne, hfs, hfx⟩

theorem not_eligible_iff_ambientXCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop) (e : Triple A B C)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e) :
    e ∉ eligible ambient targets hx hy hz ↔ ambientXCollision ambient hx hy hz e := by
  constructor
  · intro h
    by_contra hno
    exact h (eligible_of_no_ambientXCollision ambient targets hx hy hz e ha ht hs hno)
  · rintro ⟨f, hf, hne, hfs, hfx⟩ he
    exact hne (((mem_eligible_iff ambient targets hx hy hz e).1 he).2.2.2 f hf hfs hfx)

theorem assignUseful_of_no_targetCollision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible useful : Triple A B C → V → Prop) (e : Triple A B C) (v : V)
    (he : e ∈ eligible ambient targets hx hy hz)
    (hc : compatible e v) (hu : useful e v)
    (hno : ¬ targetCompatibleCollision targets hx hy hz compatible e v) :
    assignUseful (eligible ambient targets hx hy hz) compatible useful v = some e := by
  apply assignUseful_of_unique _ _ _ _ _ he hc hu
  intro f hf hcf
  have hfe := (mem_eligible_iff ambient targets hx hy hz f).1 hf
  by_contra hne
  exact hno ⟨f, hfe.2.1, hne, hfe.2.2.1, hcf⟩

theorem assignment_failure_implies_collision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible useful : Triple A B C → V → Prop) (e : Triple A B C) (v : V)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e)
    (hc : compatible e v) (hu : useful e v)
    (hfail : assignUseful (eligible ambient targets hx hy hz) compatible useful v ≠ some e) :
    ambientXCollision ambient hx hy hz e ∨
      targetCompatibleCollision targets hx hy hz compatible e v := by
  by_cases hX : ambientXCollision ambient hx hy hz e
  · exact Or.inl hX
  apply Or.inr
  by_contra hC
  have he := eligible_of_no_ambientXCollision ambient targets hx hy hz e ha ht hs hX
  exact hfail (assignUseful_of_no_targetCollision ambient targets hx hy hz
    compatible useful e v he hc hu hC)

theorem retained_assignment_of_no_collision
    (ambient targets : Finset (Triple A B C))
    (hx : A → Prop) (hy : B → Prop) (hz : C → Prop)
    (compatible useful : Triple A B C → V → Prop) (keep : V → Prop)
    (e : Triple A B C) (v : V)
    (ha : e ∈ ambient) (ht : e ∈ targets) (hs : survives hx hy hz e)
    (hc : compatible e v) (hu : useful e v) (hk : keep v)
    (hX : ¬ ambientXCollision ambient hx hy hz e)
    (hC : ¬ targetCompatibleCollision targets hx hy hz compatible e v) :
    retainAssignment (assignUseful (eligible ambient targets hx hy hz) compatible useful)
      keep v = some e := by
  have he := eligible_of_no_ambientXCollision ambient targets hx hy hz e ha ht hs hX
  have hassign := assignUseful_of_no_targetCollision ambient targets hx hy hz
    compatible useful e v he hc hu hC
  simpa only [retainAssignment, ite_eq_left hk] using hassign

theorem passing_assignment_failure_subset
    (samples : Finset Ω) (ambient targets : Finset (Triple A B C))
    (hx : Ω → A → Prop) (hy : Ω → B → Prop) (hz : Ω → C → Prop)
    (compatible useful : Triple A B C → V → Prop) (keep : V → Prop)
    (e : Triple A B C) (v : V) (ha : e ∈ ambient) (ht : e ∈ targets)
    (hc : compatible e v) (hu : useful e v) (hk : keep v) :
    samples.filter (fun ω => survives (hx ω) (hy ω) (hz ω) e ∧
      retainAssignment
        (assignUseful (eligible ambient targets (hx ω) (hy ω) (hz ω)) compatible useful)
        keep v ≠ some e) ⊆
    samples.filter (fun ω => survives (hx ω) (hy ω) (hz ω) e ∧
      (ambientXCollision ambient (hx ω) (hy ω) (hz ω) e ∨
        targetCompatibleCollision targets (hx ω) (hy ω) (hz ω) compatible e v)) := by
  intro ω hω
  obtain ⟨hωs, hs, hfail⟩ := Finset.mem_filter.1 hω
  apply Finset.mem_filter.2
  refine ⟨hωs, hs, ?_⟩
  have hfail' : assignUseful (eligible ambient targets (hx ω) (hy ω) (hz ω))
      compatible useful v ≠ some e := by
    simpa only [retainAssignment, ite_eq_left hk] using hfail
  exact assignment_failure_implies_collision ambient targets (hx ω) (hy ω) (hz ω)
    compatible useful e v ha ht hs hc hu hfail'

end MatrixMultiplication.JointAssignmentLoss

end

end OAI
