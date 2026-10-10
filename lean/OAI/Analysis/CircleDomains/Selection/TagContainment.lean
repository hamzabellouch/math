import OAI.Analysis.CircleDomains.Topology.PathTags

namespace OAI

/-! Closed level-containment tests for the actual finite unions in tag slots. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def labeledLevelGraph (H : ℕ → Set (UnitAddCircle × X)) :
    Set (ℕ × (UnitAddCircle × X)) := {q | q.2 ∈ H q.1}

theorem isClosed_labeledLevelGraph {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (labeledLevelGraph H) := by
  have heq : (labeledLevelGraph H)ᶜ = ⋃ i : ℕ, {i} ×ˢ (H i)ᶜ := by
    ext q
    simp [labeledLevelGraph]
  rw [← isOpen_compl_iff, heq]
  exact isOpen_iUnion fun i => (isOpen_discrete _).prod (hH i).isOpen_compl

def activeTagLevelGraph (H : ℕ → Set (UnitAddCircle × X)) : Set (TagData × X) :=
  {q | ∃ i : Fin (q.1.1 + 1), (q.1.2.2.1 i, q.2) ∈ H (q.1.2.1 i)}

theorem isClosed_activeTagLevelGraph {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (activeTagLevelGraph H) := by
  let A : Set (Σ n : ℕ, TagParameters n × X) :=
    {q | ∃ i : Fin (q.1 + 1), (q.2.1.2.1 i, q.2.2) ∈ H (q.2.1.1 i)}
  have hA : IsClosed A := by
    apply isClosed_sigma_iff.mpr
    intro n
    change IsClosed {q : TagParameters n × X |
      ∃ i : Fin (n + 1), (q.1.2.1 i, q.2) ∈ H (q.1.1 i)}
    simp only [ofPred_exists]
    apply isClosed_iUnion_of_finite
    intro i
    exact (isClosed_labeledLevelGraph hH).preimage
      (show Continuous (fun q : TagParameters n × X =>
        (q.1.1 i, (q.1.2.1 i, q.2))) from by fun_prop)
  exact hA.preimage (Homeomorph.sigmaProdDistrib (Y := X)).continuous

def tagLevelGraph (H : ℕ → Set (UnitAddCircle × X)) : Set (TagSlot × X) :=
  {q | match q.1 with
    | Sum.inl _ => True
    | Sum.inr t => (t, q.2) ∈ activeTagLevelGraph H}

theorem isClosed_tagLevelGraph {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (tagLevelGraph H) := by
  let A : Set ((Unit × X) ⊕ (TagData × X)) :=
    {q | match q with
      | Sum.inl _ => True
      | Sum.inr t => t ∈ activeTagLevelGraph H}
  have hA : IsClosed A :=
    isClosed_sum_iff.mpr ⟨isClosed_univ, isClosed_activeTagLevelGraph hH⟩
  have heq : tagLevelGraph H =
      (Homeomorph.sumProdDistrib (X := Unit) (Y := TagData) (Z := X)) ⁻¹' A := by
    ext ⟨s, x⟩
    cases s <;> rfl
  rw [heq]
  exact hA.preimage (Homeomorph.sumProdDistrib (X := Unit) (Y := TagData) (Z := X)).continuous

def tagContainment (H : ℕ → Set (UnitAddCircle × X)) : Set (C(PathTime, X) × TagSlot) :=
  {q | ∀ t : PathTime, tagLeft q.2 < t → t < tagRight q.2 → (q.2, q.1 t) ∈ tagLevelGraph H}

theorem isClosed_tagContainment {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (tagContainment H) := by
  have heq : tagContainment H = ⋂ t : PathTime,
      {q | (t : ℝ) ≤ tagLeft q.2 ∨ (tagRight q.2 : ℝ) ≤ t ∨
        (q.2, q.1 t) ∈ tagLevelGraph H} := by
    ext q
    simp only [tagContainment, mem_ofPred_eq, mem_iInter]
    change (∀ t : PathTime, (tagLeft q.2 : ℝ) < t → (t : ℝ) < tagRight q.2 →
      (q.2, q.1 t) ∈ tagLevelGraph H) ↔ _
    simp only [← not_lt, ← imp_iff_not_or, ← imp_iff_not_or]
  rw [heq]
  apply isClosed_iInter
  intro t
  exact (isClosed_le continuous_const
    (continuous_subtype_val.comp (continuous_tagLeft.comp continuous_snd))).union
    ((isClosed_le (continuous_subtype_val.comp
      (continuous_tagRight.comp continuous_snd)) continuous_const).union
      ((isClosed_tagLevelGraph hH).preimage
        (continuous_snd.prodMk ((continuous_eval_const t).comp continuous_fst))))

end CircleDomainRigidity

end

end OAI
