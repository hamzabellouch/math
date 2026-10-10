import OAI.Probability.SLE.Multipoint.MultipointPhaseProcess
import OAI.Probability.SLE.Multipoint.MultipointStoppedCoordinates
import OAI.Probability.SLE.FiniteRadiusStop

namespace OAI

/-! On each active interval the finite phase selects exactly the raw
radius regulator. Completion freezes the coordinate and removes its rate. -/

noncomputable section
open Set
open scoped NNReal

namespace SLEExactGauge.Multipoint

lemma phaseActive_iff_val (j : Fin 4) :
    phaseActive j ↔ 1 ≤ j.val ∧ j.val < 3 := by
  fin_cases j <;> norm_num [phaseActive]

lemma phaseAt_active_iff {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω) (i : ι)
    (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0) :
    phaseActive (phaseAt ρ t ω i) ↔ ρ (i,0) ω ≤ t ∧ t < ρ (i,2) ω := by
  rw [phaseActive_iff_val]
  have h0 := phaseAt_ge_iff ρ ω i hρ t 0
  have h2 := phaseAt_ge_iff ρ ω i hρ t 2
  simp only [Fin.val_zero] at h0 h2
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨h0.mp ha, lt_of_not_ge ?_⟩
    intro hc
    have := h2.mpr hc
    omega
  · rintro ⟨ha,hb⟩
    refine ⟨h0.mpr ha, ?_⟩
    by_contra hc
    have := h2.mp (by omega)
    exact (not_le_of_gt hb) this

lemma phaseAt_first_iff {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω) (i : ι)
    (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0) :
    phaseAt ρ t ω i = 1 ↔ ρ (i,0) ω ≤ t ∧ t < ρ (i,1) ω := by
  have h0 := phaseAt_ge_iff ρ ω i hρ t 0
  have h1 := phaseAt_ge_iff ρ ω i hρ t 1
  simp only [Fin.val_zero, Fin.val_one] at h0 h1
  constructor
  · intro h
    have hv : (phaseAt ρ t ω i).val = 1 := by rw [h]; rfl
    refine ⟨h0.mp (by omega), lt_of_not_ge ?_⟩
    intro hc
    have := h1.mpr hc
    omega
  · rintro ⟨ha,hb⟩
    have hlo := h0.mpr ha
    have hhi : ¬ 2 ≤ (phaseAt ρ t ω i).val := by
      intro hc
      exact (not_le_of_gt hb) (h1.mp hc)
    apply Fin.ext
    change (phaseAt ρ t ω i).val = 1
    omega

lemma phaseAt_second_iff {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω) (i : ι)
    (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0) :
    phaseAt ρ t ω i = 2 ↔ ρ (i,1) ω ≤ t ∧ t < ρ (i,2) ω := by
  have h1 := phaseAt_ge_iff ρ ω i hρ t 1
  have h2 := phaseAt_ge_iff ρ ω i hρ t 2
  simp only [Fin.val_one] at h1 h2
  constructor
  · intro h
    have hv : (phaseAt ρ t ω i).val = 2 := by rw [h]; rfl
    refine ⟨h1.mp (by omega), lt_of_not_ge ?_⟩
    intro hc
    have := h2.mpr hc
    omega
  · rintro ⟨ha,hb⟩
    have hlo := h1.mpr ha
    have hhi : ¬ 3 ≤ (phaseAt ρ t ω i).val := by
      intro hc
      exact (not_le_of_gt hb) (h2.mp hc)
    apply Fin.ext
    change (phaseAt ρ t ω i).val = 2
    omega

lemma phaseAt_active_stopped_state {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω) (i : ι)
    (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0)
    (hactive : phaseActive (phaseAt ρ t ω i))
    (Q : ℝ → Ω → ι → ℂ × ℝ) :
    stoppedCoordinateState Q (fun i => ρ (i,2)) t ω i = Q t ω i := by
  have ht := ((phaseAt_active_iff ρ ω i hρ t).mp hactive).2
  have hle : (t : ℝ) ≤ (ρ (i,2) ω : ℝ) := by exact_mod_cast ht.le
  simp only [stoppedCoordinateState, min_eq_left hle]

lemma phaseAt_active_stopped_velocity {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω) (i : ι)
    (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0)
    (hactive : phaseActive (phaseAt ρ t ω i))
    (V : ℝ → Ω → ι → ℂ × ℝ) :
    stoppedCoordinateVelocity V (fun i => ρ (i,2)) t ω i = V t ω i := by
  have ht := ((phaseAt_active_iff ρ ω i hρ t).mp hactive).2
  have hlt : (t : ℝ) < (ρ (i,2) ω : ℝ) := by exact_mod_cast ht
  simp only [stoppedCoordinateVelocity, ite_eq_left hlt]

/-- Agreement up to each point's own completion suffices on every active
phase; no common live endpoint for all coordinates is required. -/
lemma phaseAt_active_chart {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω) (i : ι)
    (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0)
    (hactive : phaseActive (phaseAt ρ t ω i))
    (Q : ℝ → Ω → ι → ℂ × ℝ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ)
    (hQ : EqOn (fun u => Q u ω i) (logLoewnerCoordinates G z)
      (Icc 0 (ρ (i,2) ω : ℝ))) :
    stoppedCoordinateState Q (fun i => ρ (i,2)) t ω i =
      logLoewnerCoordinates G z t := by
  rw [phaseAt_active_stopped_state ρ ω i hρ t hactive Q]
  apply hQ
  refine ⟨t.coe_nonneg, ?_⟩
  exact_mod_cast ((phaseAt_active_iff ρ ω i hρ t).mp hactive).2.le

/-- The selected active branch has the raw regulator and never exceeds one. -/
theorem phaseRegulator_eq_and_le_one (κ β a U : ℝ) (hβ : 0 ≤ β)
    (j : Fin 4) (hj : phaseActive j) (z : ℂ × ℝ)
    (hfirst : j = 1 → 0 ≤ logFactorClock κ z-a ∧ logFactorClock κ z-a ≤ U/2)
    (hsecond : j = 2 → U/2 ≤ logFactorClock κ z-a ∧ logFactorClock κ z-a ≤ U) :
    branchRegulator κ (phaseRegulatorScale β a U j) (phaseRegulatorSlope β j) z =
      regulator β U (logFactorClock κ z-a) ∧
    branchRegulator κ (phaseRegulatorScale β a U j) (phaseRegulatorSlope β j) z ≤ 1 := by
  rcases hj with rfl | rfl
  · change branchRegulator κ (Real.exp (β*a)) (-β) z = _ ∧
      branchRegulator κ (Real.exp (β*a)) (-β) z ≤ 1
    exact ⟨first_branch_regulator_eq κ β a U z (hfirst rfl).2,
      first_branch_regulator_le_one κ β a z hβ (hfirst rfl).1⟩
  · change branchRegulator κ (Real.exp (-β*(U+a))) β z = _ ∧
      branchRegulator κ (Real.exp (-β*(U+a))) β z ≤ 1
    exact ⟨second_branch_regulator_eq κ β a U z (hsecond rfl).1,
      second_branch_regulator_le_one κ β a U z hβ (hsecond rfl).2⟩

/-- Threshold status for the actual stopping-time phase supplies the branch
bounds; no separate regulator assumption is needed. -/
theorem phaseAt_regulator_eq_and_le_one {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω) (i : ι)
    (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0)
    (κ β a U : ℝ) (hβ : 0 ≤ β) (z : ℂ × ℝ)
    (hactive : phaseActive (phaseAt ρ t ω i))
    (hstart : ρ (i,0) ω ≤ t → 0 ≤ logFactorClock κ z-a)
    (hbefore : t < ρ (i,1) ω → logFactorClock κ z-a ≤ U/2)
    (hafter : ρ (i,1) ω ≤ t → U/2 ≤ logFactorClock κ z-a)
    (hend : t < ρ (i,2) ω → logFactorClock κ z-a ≤ U) :
    branchRegulator κ (phaseRegulatorScale β a U (phaseAt ρ t ω i))
      (phaseRegulatorSlope β (phaseAt ρ t ω i)) z =
      regulator β U (logFactorClock κ z-a) ∧
    branchRegulator κ (phaseRegulatorScale β a U (phaseAt ρ t ω i))
      (phaseRegulatorSlope β (phaseAt ρ t ω i)) z ≤ 1 := by
  apply phaseRegulator_eq_and_le_one κ β a U hβ _ hactive z
  · intro h
    obtain ⟨h0,h1⟩ := (phaseAt_first_iff ρ ω i hρ t).mp h
    exact ⟨hstart h0,hbefore h1⟩
  · intro h
    obtain ⟨h1,h2⟩ := (phaseAt_second_iff ρ ω i hρ t).mp h
    exact ⟨hafter h1,hend h2⟩

end SLEExactGauge.Multipoint

end

end OAI
