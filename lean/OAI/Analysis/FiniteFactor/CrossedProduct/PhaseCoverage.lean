import OAI.Analysis.FiniteFactor.CrossedProduct.Phases

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
noncomputable section

def sourceFirstPhaseLower (s : ℕ) : ℝ := (sourceStageState s).G*(sourceStageState s).K

theorem sourcePhaseUpper_tendsto : Tendsto sourcePhaseUpper atTop atTop := by
  apply tendsto_atTop_mono (f := fun s => (sourceBlockSize s : ℝ)) _
    (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  intro s
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  unfold sourcePhaseUpper
  conv_lhs => rw [← Real.rpow_one (sourceBlockSize s : ℝ)]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem sourcePhaseOverlap (s : ℕ) : sourceFirstPhaseLower (s+1) < sourcePhaseUpper s :=
  (sourceStage s).next_gap

/-- The real interval coverage from the contradiction, with the first range
used only at strictly later blocks. No magnitude is silently omitted. -/
theorem sourcePhase_range_coverage (j : ℕ) (t : ℝ) (ht : sourcePhaseLower j ≤ t) :
    ∃ s : ℕ,
      (j ≤ s ∧ sourcePhaseLower s ≤ t ∧ t ≤ sourcePhaseUpper s) ∨
      (j < s ∧ sourceFirstPhaseLower s ≤ t ∧ t ≤ sourcePhaseLower s) := by
  have hex : ∃ s : ℕ, j ≤ s ∧ t ≤ sourcePhaseUpper s :=
    ((eventually_ge_atTop j).and (sourcePhaseUpper_tendsto.eventually (eventually_ge_atTop t))).exists
  let s := Nat.find hex
  have hs := Nat.find_spec hex
  change j ≤ s ∧ t ≤ sourcePhaseUpper s at hs
  by_cases he : s = j
  · exact ⟨s, Or.inl ⟨hs.1, by simpa [he] using ht, hs.2⟩⟩
  · have hj : j < s := by omega
    by_cases hmid : sourcePhaseLower s ≤ t
    · exact ⟨s, Or.inl ⟨hs.1,hmid,hs.2⟩⟩
    · obtain ⟨p,hp⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega)
      have hprev : ¬(j ≤ p ∧ t ≤ sourcePhaseUpper p) := Nat.find_min hex (by change p < s; omega)
      have htprev : sourcePhaseUpper p < t := by
        by_contra hh
        apply hprev
        exact ⟨by omega, le_of_not_gt hh⟩
      refine ⟨s, Or.inr ⟨hj, ?_, (lt_of_not_ge hmid).le⟩⟩
      rw [hp]
      exact (sourcePhaseOverlap p).le.trans htprev.le

/-- The finite deterministic qualifying list at one selected block. -/
def sourceQualifying (θ : SourceCoordinate → ℝ) (s : ℕ) (k : ℤ) (w : Fin 2) :
    Finset SourceCoordinate :=
  (sourceBlockCoordinates s).filter (fun i =>
    1-Int.fract ((k : ℝ)*θ i) ∈ Set.Icc (sourceWidth s w) (1-sourceWidth s w))

def SourceSecondPhasesFrom (θ : SourceCoordinate → ℝ) (j : ℕ) : Prop :=
  ∀ s : ℕ, j ≤ s → ∀ k : ℤ, sourcePhaseLower s ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ sourcePhaseUpper s →
    (sourceBlockSize s : ℝ)/20 ≤ ((sourceQualifying θ s k 1).card : ℝ)

theorem sourceAngleLaw_second_phases_from :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ j : ℕ, SourceSecondPhasesFrom θ j := by
  filter_upwards [sourceAngleLaw_second_phases] with θ hθ
  obtain ⟨j,hj⟩ := Filter.eventually_atTop.mp hθ
  refine ⟨j, fun s hs k hlo hhi => ?_⟩
  simpa [sourceQualifying, sourcePhaseMissSet] using hj s hs k hlo hhi

/-- For every large omitted index, this constructs a block, width, and finite
qualifying list depending only on the fixed angles and the index. -/
theorem exists_source_qualifying_assignment (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (k : ℤ)
    (hk : sourcePhaseLower j ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : Fin 2) (I : Finset SourceCoordinate),
      j ≤ s ∧ (w = 0 → j < s) ∧ I ⊆ sourceBlockCoordinates s ∧
      (sourceBlockSize s : ℝ)/20 ≤ (I.card : ℝ) ∧
      ∀ i ∈ I, 1-Int.fract ((k : ℝ)*θ i) ∈ Set.Icc (sourceWidth s w) (1-sourceWidth s w) := by
  obtain ⟨s, hs | hs⟩ := sourcePhase_range_coverage j |(k : ℝ)| hk
  · refine ⟨s, 1, sourceQualifying θ s k 1, hs.1, by simp, Finset.filter_subset _ _,
      hphase s hs.1 k hs.2.1 hs.2.2, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · refine ⟨s, 0, sourceBlockCoordinates s, hs.1.le, fun _ => hs.1, le_rfl, ?_, ?_⟩
    · rw [sourceBlockCoordinates_card]
      have hh : (0 : ℝ) ≤ sourceBlockSize s := Nat.cast_nonneg _
      linarith
    · intro i hi
      have his := mem_sourceBlockCoordinates hi
      rcases i with ⟨t,i⟩
      change t = s at his
      subst t
      exact hθ.first_phase s k hs.2.1 hs.2.2 i

end
end FiniteFactor

end OAI
