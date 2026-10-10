import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MaskedRates

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegreeEnvelope

open AllFieldHistory AllFieldGroupOrbitData Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

def variableDegree (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma) : ℕ :=
  ((data (K := K) (tick := tick) allocation m width sigma).orbits e).sup fun o =>
    ((data (K := K) (tick := tick) allocation m width sigma).passing e o).sup fun v =>
      ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card

def uniformDegree (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) : ℕ :=
  Finset.univ.sup fun e : Targets (K := K) (tick := tick) allocation m sigma =>
    max ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card
      (variableDegree (K := K) (tick := tick) allocation m width sigma e)

theorem eligibility_card_le (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma) :
    ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card ≤
      uniformDegree (K := K) (tick := tick) allocation m width sigma :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun e =>
    max ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card
      (variableDegree (K := K) (tick := tick) allocation m width sigma e)) (Finset.mem_univ e))

theorem competitors_card_le (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m width sigma).orbits e)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v ∈ (data (K := K) (tick := tick) allocation m width sigma).passing e o) :
    ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card ≤
      uniformDegree (K := K) (tick := tick) allocation m width sigma := by
  have hvle := Finset.le_sup (f := fun v =>
    ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card) hv
  have hole := Finset.le_sup (f := fun o =>
    ((data (K := K) (tick := tick) allocation m width sigma).passing e o).sup fun v =>
      ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card) ho
  have hel := Finset.le_sup (f := fun e =>
    max ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card
      (variableDegree (K := K) (tick := tick) allocation m width sigma e)) (Finset.mem_univ e)
  exact hvle.trans (hole.trans ((le_max_right _ _).trans hel))

private theorem cast_max_le {a b : ℕ} {R : ℝ}
    (ha : (a : ℝ) ≤ R) (hb : (b : ℝ) ≤ R) : ((max a b : ℕ) : ℝ) ≤ R := by
  rcases le_total a b with hab | hba
  · simpa only [max_eq_right hab] using hb
  · simpa only [max_eq_left hba] using ha

private theorem cast_sup_le {I : Type*} (s : Finset I) (f : I → ℕ)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ i ∈ s, (f i : ℝ) ≤ R) :
    ((s.sup f : ℕ) : ℝ) ≤ R := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using hR
  | @insert a s _ ih =>
      intro hs
      rw [Finset.sup_insert]
      exact cast_max_le (hs a (Finset.mem_insert_self a s))
        (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)))

theorem uniformDegree_real_le (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) {R : ℝ} (hR : 0 ≤ R)
    (heligibility : ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
      (((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤ R)
    (hcompetitors : ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
      ∀ o ∈ (data (K := K) (tick := tick) allocation m width sigma).orbits e,
        ∀ v ∈ (data (K := K) (tick := tick) allocation m width sigma).passing e o,
          (((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card : ℝ) ≤ R) :
    (uniformDegree (K := K) (tick := tick) allocation m width sigma : ℝ) ≤ R := by
  apply cast_sup_le _ _ hR
  intro e _
  apply cast_max_le (heligibility e)
  apply cast_sup_le _ _ hR
  intro o ho
  apply cast_sup_le _ _ hR
  exact hcompetitors e o ho

theorem eventually_log_uniformDegree_le (allocation : Allocation) (width : ℝ)
    (sigma : Placement) {D : ℝ} (hD : 0 ≤ D)
    (hcounts : ∀ᶠ m : ℕ in atTop,
      (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
        (((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
          Real.exp ((m : ℝ) * D)) ∧
      (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
        ∀ o ∈ (data (K := K) (tick := tick) allocation m width sigma).orbits e,
          ∀ v ∈ (data (K := K) (tick := tick) allocation m width sigma).passing e o,
            (((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card : ℝ) ≤
              Real.exp ((m : ℝ) * D))) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (uniformDegree (K := K) (tick := tick) allocation m width sigma : ℝ) /
        (m : ℝ) ≤ D := by
  filter_upwards [hcounts, eventually_gt_atTop (0 : ℕ)] with m hm hmp
  by_cases hz : uniformDegree (K := K) (tick := tick) allocation m width sigma = 0
  · simpa only [hz, Nat.cast_zero, Real.log_zero, zero_div] using hD
  have hd : (0 : ℝ) < uniformDegree (K := K) (tick := tick) allocation m width sigma := by
    exact_mod_cast Nat.pos_of_ne_zero hz
  have hb := uniformDegree_real_le (K := K) (tick := tick) allocation m width sigma
    (Real.exp_pos _).le hm.1 hm.2
  have hl := Real.log_le_log hd hb
  rw [Real.log_exp] at hl
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hmp
  exact (div_le_iff₀ hmpos).mpr (by simpa only [mul_comm] using hl)

end MatrixMultiplication.AllFieldGroupDegreeEnvelope

end

end OAI
