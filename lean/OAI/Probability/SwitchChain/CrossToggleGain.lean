import OAI.Probability.SwitchChain.CrossToggleCells

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def gain (a b : Finset (Fin n)) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  if ha : a.card = 2 then
    if hb : b.card = 2 then pairProjection ⟨a, ha⟩ ⟨b, hb⟩ else 0
  else 0

theorem gain_of_pairs (a b : Finset (Fin n)) (ha : a.card = 2) (hb : b.card = 2) :
    gain (d := d) a b = pairProjection ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [gain, ha, hb]

theorem gain_pair_eq (i j k l : Fin n) (h : FourDistinct i j k l) :
    gain (d := d) {i,j} {k,l} = SwitchFlip.projection (crossProposal i j k l h) := by
  have ha : ({i,j} : Finset (Fin n)).card = 2 := by simp [h.1]
  have hb : ({k,l} : Finset (Fin n)).card = 2 := by simp [h.2.2.2.2.2]
  have hd : Disjoint ({i,j} : Finset (Fin n)) {k,l} := by
    simp [Finset.disjoint_left, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]
  rw [gain_of_pairs _ _ ha hb]
  exact pairProjection_eq_explicit ⟨_,ha⟩ ⟨_,hb⟩ hd i j k l rfl rfl h

theorem gain_pair_apply (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    gain {i,j} {k,l} f G =
      (f G - f (SwitchFlip.flip (crossProposal i j k l h) G)) / 2 := by
  rw [gain_pair_eq i j k l h, SwitchFlip.projection_apply]

theorem norm_gain_pair_sq (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : PairResampling.StateSpace n d) :
    ‖gain {i,j} {k,l} f‖ ^ 2 = (1 / 4 : ℝ) *
      ∑ G : GraphState n d, (f G - f (SwitchFlip.flip (crossProposal i j k l h) G)) ^ 2 := by
  rw [gain_pair_eq i j k l h]
  exact SwitchFlip.norm_projection_sq _ f

theorem gain_symm (a b : Finset (Fin n)) : gain (d := d) a b = gain b a := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb, gain_of_pairs b a hb ha, pairProjection_symm]
  all_goals simp [gain, ha, hb]

theorem gain_eq_zero_of_not_disjoint (a b : Finset (Fin n)) (h : ¬ Disjoint a b) :
    gain (d := d) a b = 0 := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2 <;>
    simp [gain, ha, hb, pairProjection, h]

theorem gain_pair_eq_ordered (i j k l : Fin n) :
    gain (d := d) {i,j} {k,l} =
      if h : FourDistinct i k l j then
        SwitchFlip.projection (fourVertexProposal i k l j h) else 0 := by
  by_cases h : FourDistinct i k l j
  · rw [dite_eq_left h]
    have h' : FourDistinct i j k l :=
      ⟨h.2.2.1, h.1, h.2.1, h.2.2.2.2.1.symm,
        h.2.2.2.2.2.symm, h.2.2.2.1⟩
    rw [gain_pair_eq i j k l h']
    rfl
  · rw [dite_eq_right h]
    by_cases hij : i = j
    · subst j
      simp [gain]
    by_cases hkl : k = l
    · subst l
      simp [gain]
    apply gain_eq_zero_of_not_disjoint
    intro hd
    apply h
    have hik : i ≠ k := by
      intro e
      exact Finset.disjoint_left.mp hd (show i ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hil : i ≠ l := by
      intro e
      exact Finset.disjoint_left.mp hd (show i ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hjk : j ≠ k := by
      intro e
      exact Finset.disjoint_left.mp hd (show j ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hjl : j ≠ l := by
      intro e
      exact Finset.disjoint_left.mp hd (show j ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    exact ⟨hik, hil, hij, hkl, hjk.symm, hjl.symm⟩

theorem gain_idempotent (a b : Finset (Fin n)) (f : PairResampling.StateSpace n d) :
    gain a b (gain a b f) = gain a b f := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb, pairProjection_idempotent]
  all_goals simp [gain, ha, hb]

theorem gain_isSymmetric (a b : Finset (Fin n)) :
    (gain (d := d) a b).toLinearMap.IsSymmetric := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    exact pairProjection_isSymmetric _ _
  all_goals
    intro f g
    simp [gain, ha, hb]

theorem gain_expectation_left (a b : Finset (Fin n))
    (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.expectation n d a f) = 0 := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    by_cases h : Disjoint a b
    · rw [pairProjection_of_disjoint _ _ h]
      exact SwitchFlip.projection_expectation _ a
        (pairProposal_crosses_left ⟨a,ha⟩ ⟨b,hb⟩ h) f
    · simp [pairProjection, h]
  all_goals simp [gain, ha, hb]

theorem gain_expectation_right (a b : Finset (Fin n))
    (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.expectation n d b f) = 0 := by
  rw [gain_symm a b]
  exact gain_expectation_left b a f

theorem gain_mem_common (a b : Finset (Fin n)) (f : PairResampling.StateSpace n d) :
    gain a b f ∈ (PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    exact pairProjection_mem_common ⟨a, ha⟩ ⟨b, hb⟩ f
  all_goals simp [gain, ha, hb]

theorem gain_norm_le_common (a b : Finset (Fin n)) (f : PairResampling.StateSpace n d) :
    ‖gain a b f‖ ≤ ‖(PairResampling.fiberSpace n d a ⊔
      PairResampling.fiberSpace n d b)ᗮ.starProjection f‖ := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    by_cases h : Disjoint a b
    · rw [pairProjection_of_disjoint _ _ h]
      exact SwitchFlip.norm_projection_le_jointOrthogonal _ a b
        (pairProposal_crosses_left ⟨a, ha⟩ ⟨b, hb⟩ h)
        (pairProposal_crosses_right ⟨a, ha⟩ ⟨b, hb⟩ h) f
    · simp only [pairProjection, dite_eq_right h, zero_apply, norm_zero]
      exact norm_nonneg _
  all_goals simp [gain, ha, hb]

theorem gain_restrictCell (a b : Finset (Fin n)) (C : GraphState n d → Prop)
    (hC : PairResampling.CellInvariant a C) (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.restrictCell C f) =
      PairResampling.restrictCell C (gain a b f) := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2
  · rw [gain_of_pairs a b ha hb]
    exact pairProjection_restrictCell ⟨a, ha⟩ ⟨b, hb⟩ C hC f
  all_goals
    ext G
    simp [gain, ha, hb, PairResampling.restrictCell_apply]

end Problem315.CrossToggle

end

end OAI
