import OAI.Algebra.DepthFive.IsolatedWeight
import OAI.Algebra.DepthFive.ScheduleEnds

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335.BalancedSchedule

/-- The graph edges joining consecutive layers, indexed by internal vertices. -/
def internalEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.image (fun v : Fin (n - 1) => (leftLayer v, rightLayer v))

/-- On a successor number of layers this is the canonical path graph. -/
theorem internalEdges_eq_pathEdges (n : ℕ) :
    internalEdges (n + 1) = SwitchRestoration.pathEdges n := rfl

/-- Each graph edge joins adjacent layers in either direction. -/
theorem internalEdges_adjacent {n : ℕ} {e : Fin n × Fin n}
    (he : e ∈ internalEdges n) : adjacent e.1 e.2 ∧ adjacent e.2 e.1 := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
  exact ⟨adjacent_left_right v, (adjacent_left_right v).symm⟩

/-- Graph incidence degree and internal-end cardinality agree exactly. -/
theorem endpointDegree_internalEdges {n : ℕ} (i : Fin n) :
    SwitchRestoration.endpointDegree (internalEdges n) i = (internalEnds i).card := by
  classical
  unfold SwitchRestoration.endpointDegree internalEdges
  rw [Finset.sum_image]
  · rw [internalEnds, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v hv
    have hl : leftLayer v = i ↔ v.val = i.val := by
      constructor
      · exact fun h => congrArg Fin.val h
      · exact fun h => Fin.ext h
    have hr : rightLayer v = i ↔ v.val + 1 = i.val := by
      constructor
      · exact fun h => congrArg Fin.val h
      · exact fun h => Fin.ext h
    change (if leftLayer v = i then 1 else 0) +
      (if rightLayer v = i then 1 else 0) =
        if v.val = i.val ∨ v.val + 1 = i.val then 1 else 0
    simp only [hl, hr]
    by_cases hleft : v.val = i.val
    · simp [hleft]
    · by_cases hright : v.val + 1 = i.val <;> simp [hleft, hright]
  · intro v hv w hw h
    apply Fin.ext
    exact congrArg (fun e : Fin n × Fin n => e.1.val) h

/-- Normal neighbors of a normal layer are in bijection with its internal
vertices having two normal incident layers. This identifies the correction
exponents in the graph-word and path-pairing formulations. -/
theorem falseNeighbors_card_eq_nnInternalEnds_card {n : ℕ}
    (τ : Fin n → Bool) (i : Fin n) (hi : τ i = false) :
    (IsolatedWeight.falseNeighbors adjacent τ i).card =
      (nnInternalEnds τ i).card := by
  classical
  apply Finset.card_bij (fun j hj =>
    (⟨min i.val j.val, by
      have hadj := (Finset.mem_filter.mp hj).2.1
      unfold adjacent at hadj
      have hin := i.isLt
      have hjn := j.isLt
      rcases hadj with h | h <;> omega⟩ : Fin (n - 1)))
  · intro j hj
    have hadj := (Finset.mem_filter.mp hj).2.1
    have hjfalse := (Finset.mem_filter.mp hj).2.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · unfold adjacent at hadj
        dsimp
        rcases hadj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    · unfold adjacent at hadj
      rcases hadj with h | h
      · have hl : leftLayer ⟨min i.val j.val, by omega⟩ = i := by
          apply Fin.ext
          dsimp [leftLayer]
          omega
        have hr : rightLayer ⟨min i.val j.val, by omega⟩ = j := by
          apply Fin.ext
          dsimp [rightLayer]
          omega
        simpa only [hl, hr] using And.intro hi hjfalse
      · have hl : leftLayer ⟨min i.val j.val, by omega⟩ = j := by
          apply Fin.ext
          dsimp [leftLayer]
          omega
        have hr : rightLayer ⟨min i.val j.val, by omega⟩ = i := by
          apply Fin.ext
          dsimp [rightLayer]
          omega
        simpa only [hl, hr] using And.intro hjfalse hi
  · intro a ha b hb hab
    have hadj := (Finset.mem_filter.mp ha).2.1
    have hbadj := (Finset.mem_filter.mp hb).2.1
    have habv := congrArg Fin.val hab
    apply Fin.ext
    unfold adjacent at hadj hbadj
    dsimp at habv
    omega
  · intro v hv
    have hends := (Finset.mem_filter.mp hv).1
    have hfalse := (Finset.mem_filter.mp hv).2
    rcases internalEnds_cases hends with hl | hr
    · refine ⟨rightLayer v, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, hfalse.2⟩
        rw [← hl]
        exact adjacent_left_right v
      · apply Fin.ext
        have hiv := congrArg Fin.val hl
        dsimp [leftLayer, rightLayer] at hiv ⊢
        omega
    · refine ⟨leftLayer v, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, hfalse.1⟩
        rw [← hr]
        exact (adjacent_left_right v).symm
      · apply Fin.ext
        have hiv := congrArg Fin.val hr
        dsimp [leftLayer, rightLayer] at hiv ⊢
        omega

/-- The complete coincidence correction in the internal-vertex formulation. -/
theorem correction_eq_nnInternalEnds_product {n : ℕ}
    (V : Finset (Fin n)) (τ : Fin n → Bool) (A x : ℝ) :
    IsolatedWeight.correction V adjacent A x τ =
      ∏ i ∈ V.filter (fun i => τ i = false),
        (1 + A * x ^ (nnInternalEnds τ i).card) := by
  classical
  unfold IsolatedWeight.correction
  apply Finset.prod_congr rfl
  intro i hi
  rw [falseNeighbors_card_eq_nnInternalEnds_card τ i (Finset.mem_filter.mp hi).2]

end Problem335.BalancedSchedule

end

end OAI
