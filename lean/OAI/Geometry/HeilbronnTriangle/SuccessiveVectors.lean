import Mathlib

namespace OAI


namespace Problem355.SuccessiveVectors

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

theorem exists_shortest_with_property (L : Submodule ℤ E) [DiscreteTopology L]
    (P : E → Prop) (hP : ∃ v ∈ L, P v) :
    ∃ v ∈ L, P v ∧ ∀ w ∈ L, P w → ‖v‖ ≤ ‖w‖ := by
  classical
  obtain ⟨x, hxL, hxP⟩ := hP
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hf : (Metric.closedBall (0 : E) ‖x‖ ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall (AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup))
  let S : Set E := {v | v ∈ L ∧ P v ∧ ‖v‖ ≤ ‖x‖}
  have hSfin : S.Finite := hf.subset (by
    intro v hv
    exact ⟨by simpa using hv.2.2, hv.1⟩)
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S norm hSfin ⟨x, hxL, hxP, le_rfl⟩
  refine ⟨v, hv.1, hv.2.1, ?_⟩
  intro w hwL hwP
  by_cases hw : ‖w‖ ≤ ‖x‖
  · exact hmin w ⟨hwL, hwP, hw⟩
  · exact hv.2.2.trans (le_of_not_ge hw)

variable [NormedSpace ℝ E]

theorem exists_shortest_outside (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (W : Submodule ℝ E) (hW : W ≠ ⊤) :
    ∃ v ∈ L, v ∉ W ∧ 0 < ‖v‖ ∧
      ∀ w ∈ L, w ∉ W → ‖v‖ ≤ ‖w‖ := by
  have hex : ∃ v ∈ L, v ∉ W := by
    by_contra h
    have hle : Submodule.span ℝ (L : Set E) ≤ W := by
      apply Submodule.span_le.mpr
      intro v hv
      by_contra hvW
      exact h ⟨v, hv, hvW⟩
    rw [IsZLattice.span_top] at hle
    exact hW (top_le_iff.mp hle)
  obtain ⟨v, hvL, hvW, hmin⟩ := exists_shortest_with_property L (fun v => v ∉ W) hex
  refine ⟨v, hvL, hvW, norm_pos_iff.mpr ?_, hmin⟩
  intro hv0
  exact hvW (hv0 ▸ W.zero_mem)

def earlier {n : ℕ} (v : Fin n → E) (i : Fin n) : Set E :=
  v '' {j | j < i}

omit [NormedAddCommGroup E] [ProperSpace E] [NormedSpace ℝ E] in
lemma earlier_snoc_castSucc {n : ℕ} (v : Fin n → E) (x : E) (i : Fin n) :
    earlier (Fin.snoc v x) i.castSucc = earlier v i := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    revert hj
    refine Fin.lastCases ?_ (fun k hj => ?_) j
    · intro hj
      exact (not_lt_of_ge (Fin.le_last _) hj).elim
    · exact ⟨k, hj, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, hj, by simp⟩

omit [NormedAddCommGroup E] [ProperSpace E] [NormedSpace ℝ E] in
lemma earlier_snoc_last {n : ℕ} (v : Fin n → E) (x : E) :
    earlier (Fin.snoc v x) (Fin.last n) = Set.range v := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    revert hj
    refine Fin.lastCases ?_ (fun k _ => ?_) j
    · intro hj
      simp at hj
    · exact ⟨k, by simp⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, Fin.castSucc_lt_last j, by simp⟩

structure IsSuccessive (L : Submodule ℤ E) {n : ℕ} (v : Fin n → E) : Prop where
  mem_lattice : ∀ i, v i ∈ L
  independent : LinearIndependent ℝ v
  minimal : ∀ i, ∀ w ∈ L, w ∉ Submodule.span ℝ (earlier v i) → ‖v i‖ ≤ ‖w‖

theorem exists_successive (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : n ≤ Module.finrank ℝ E) :
    ∃ v : Fin n → E, IsSuccessive L v := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    exact ⟨by intro i; exact i.elim0, linearIndependent_empty_type, by intro i; exact i.elim0⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih (Nat.le_of_succ_le hn)
    have hW : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
      intro htop
      have hdim := finrank_span_eq_card hv.independent
      rw [htop] at hdim
      have hdim' : Module.finrank ℝ E = n := by simpa using hdim
      omega
    obtain ⟨x, hxL, hxW, _, hxmin⟩ := exists_shortest_outside L _ hW
    refine ⟨Fin.snoc v x, ?_⟩
    refine ⟨?_, linearIndependent_finSnoc.mpr ⟨hv.independent, hxW⟩, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxL
      · simpa using hv.mem_lattice j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [earlier_snoc_last, Fin.snoc_last] using hxmin
      · simpa only [earlier_snoc_castSucc, Fin.snoc_castSucc] using hv.minimal j

theorem exists_successive_basis (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] [FiniteDimensional ℝ E] :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, IsSuccessive L b := by
  obtain ⟨v, hv⟩ := exists_successive L (Module.finrank ℝ E) le_rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv.independent (by simp), ?_⟩
  simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv

omit [ProperSpace E] in

theorem IsSuccessive.monotone_norm {L : Submodule ℤ E} {n : ℕ} {v : Fin n → E}
    (hv : IsSuccessive L v) : Monotone (fun i => ‖v i‖) := by
  intro i j hij
  apply hv.minimal i (v j) (hv.mem_lattice j)
  exact hv.independent.notMem_span_image (not_lt_of_ge hij)

omit [ProperSpace E] in

theorem IsSuccessive.norm_pos {L : Submodule ℤ E} {n : ℕ} {v : Fin n → E}
    (hv : IsSuccessive L v) (i : Fin n) : 0 < ‖v i‖ :=
  norm_pos_iff.mpr (hv.independent.ne_zero i)

end Problem355.SuccessiveVectors

end OAI
