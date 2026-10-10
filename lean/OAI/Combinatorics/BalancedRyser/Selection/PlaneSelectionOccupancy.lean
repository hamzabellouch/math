import OAI.Combinatorics.BalancedRyser.Selection.Selection
import OAI.Combinatorics.BalancedRyser.Selection.SelectionOccupancy2

namespace OAI

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {q : ℕ} {P D L I V : Type*}
variable [Fintype P] [Fintype D] [Fintype L]
variable [DecidableEq P] [DecidableEq I] [DecidableEq V]

omit [DecidableEq P] in
theorem plane_line_eq_of_direction_eq_of_incident
    (A : FiniteAffine.Plane q P D L) {l m : L} {p : P}
    (hd : A.direction l = A.direction m)
    (hl : A.incident p l) (hm : A.incident p m) : l = m := by
  obtain ⟨n, hn, huniq⟩ := A.unique_line_direction p (A.direction m)
  exact (huniq l ⟨hd, hl⟩).trans (huniq m ⟨rfl, hm⟩).symm

theorem plane_common_point_eq_of_lines_ne
    (A : FiniteAffine.Plane q P D L) {l m : L} (hne : l ≠ m)
    {p r : P} (hpl : A.incident p l) (hpm : A.incident p m)
    (hrl : A.incident r l) (hrm : A.incident r m) : p = r := by
  by_contra hpr
  obtain ⟨n, hn, huniq⟩ := A.unique_join p r hpr
  exact hne ((huniq l ⟨hpl, hrl⟩).trans (huniq m ⟨hpm, hrm⟩).symm)

def afterPlaneLine (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (tracked chosen : L) : Finset P := by
  classical
  exact T.filter (fun p => ¬ (chosen ≠ tracked ∧ A.incident p chosen))

omit [DecidableEq P] in
@[simp] theorem afterPlaneLine_self (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (l : L) : afterPlaneLine A T l l = T := by
  classical
  simp [afterPlaneLine]

 theorem plane_deletion_card_le_one (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (l m : L) (hT : ∀ p ∈ T, A.incident p l) :
    (T.filter (fun p => m ≠ l ∧ A.incident p m)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp r hr
  obtain ⟨hpT, hne, hpm⟩ := Finset.mem_filter.mp hp
  obtain ⟨hrT, _, hrm⟩ := Finset.mem_filter.mp hr
  exact plane_common_point_eq_of_lines_ne A hne.symm (hT p hpT) hpm (hT r hrT) hrm

omit [DecidableEq I] [DecidableEq V] in
theorem plane_occupancy_drift (A : FiniteAffine.Plane q P D L)
    (slots : Finset I) (hslots : slots.Nonempty) (Q : I → Finset V)
    (lineOf : I → V → L) (direction : I → D)
    (hinj : ∀ i ∈ slots, Set.InjOn (lineOf i) (↑(Q i) : Set V))
    (hdir : ∀ i ∈ slots, ∀ v ∈ Q i, A.direction (lineOf i v) = direction i)
    (l : L) (T : Finset P) (hT : ∀ p ∈ T, A.incident p l)
    (B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ slots, (q : ℝ) / B ≤ ((Q i).card : ℝ)) :
    (1 - B / q) * (T.card : ℝ) ≤
      average slots Q (fun i v => ((afterPlaneLine A T l (lineOf i v)).card : ℝ)) := by
  classical
  have hu : ∀ i ∈ slots, ∀ p ∈ T, ∀ v ∈ Q i, ∀ w ∈ Q i,
      lineOf i v ≠ l ∧ A.incident p (lineOf i v) →
      lineOf i w ≠ l ∧ A.incident p (lineOf i w) → v = w := by
    intro i hi p hp v hv w hw hpv hpw
    exact hinj i hi hv hw (plane_line_eq_of_direction_eq_of_incident A
      ((hdir i hi v hv).trans (hdir i hi w hw).symm) hpv.2 hpw.2)
  have hs : ∀ i ∈ slots, ∀ v ∈ Q i,
      (T.filter (fun p => lineOf i v ≠ l ∧ A.incident p (lineOf i v))).card ≤ 1 := by
    intro i hi v hv
    exact plane_deletion_card_le_one A T l (lineOf i v) hT
  have h := average_remaining_ge_ratio slots hslots Q T
    (fun i p v => lineOf i v ≠ l ∧ A.incident p (lineOf i v)) q B
    (by exact_mod_cast hq) hB hsize hu (by
      intro i hi v hv
      convert hs i hi v hv using 1
      congr 1
      ext p
      simp)
  convert h using 1
  congr 1
  funext i v
  congr 1
  apply congrArg Finset.card
  ext p
  simp [afterPlaneLine]

theorem plane_step_abs_le_one (A : FiniteAffine.Plane q P D L)
    (T : Finset P) (l m : L) (hT : ∀ p ∈ T, A.incident p l) :
    |((afterPlaneLine A T l m).card : ℝ) - (T.card : ℝ)| ≤ 1 := by
  classical
  have hs : (T.filter (fun p => m ≠ l ∧ A.incident p m)).card ≤ 1 := by
    convert plane_deletion_card_le_one A T l m hT using 1
  have hc := Finset.card_filter_add_card_filter_not
    (s := T) (fun p => m ≠ l ∧ A.incident p m)
  have heq : afterPlaneLine A T l m =
      T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m)) := by
    ext p
    simp [afterPlaneLine]
  rw [heq]
  have hsub : (T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m))).card ≤ T.card :=
    Finset.card_filter_le _ _
  have hsubR : ((T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m))).card : ℝ) ≤ T.card := by
    exact_mod_cast hsub
  rw [abs_of_nonpos (sub_nonpos.mpr hsubR)]
  have hcR : ((T.filter (fun p => m ≠ l ∧ A.incident p m)).card : ℝ) +
      (T.filter (fun p => ¬ (m ≠ l ∧ A.incident p m))).card = T.card := by
    exact_mod_cast hc
  have hsR : ((T.filter (fun p => m ≠ l ∧ A.incident p m)).card : ℝ) ≤ 1 := by
    exact_mod_cast hs
  linarith

omit [DecidableEq I] [DecidableEq V] in
theorem selection_plane_occupancy_drift [Fintype I] [Fintype V]
    (G : Selection.Input I V) (A : FiniteAffine.Plane q P D L)
    (index : I ≃ D × Bool) (line : V → L)
    (hline : Selection.LineAssignment G A index line)
    (slots : Finset I) (hslots : slots.Nonempty) (Q : I → Finset V)
    (hQ : ∀ i ∈ slots, ∀ v ∈ Q i, G.slot v = i)
    (l : L) (T : Finset P) (hT : ∀ p ∈ T, A.incident p l)
    (B : ℝ) (hq : 0 < q) (hB : 0 < B)
    (hsize : ∀ i ∈ slots, (q : ℝ) / B ≤ ((Q i).card : ℝ)) :
    (1 - B / q) * (T.card : ℝ) ≤
      average slots Q (fun _ v => ((afterPlaneLine A T l (line v)).card : ℝ)) := by
  apply plane_occupancy_drift A slots hslots Q (fun _ => line)
    (fun i => (index i).1) _ _ l T hT B hq hB hsize
  · intro i hi v hv w hw heq
    exact hline.2 v w ((hQ i hi v hv).trans (hQ i hi w hw).symm) heq
  · intro i hi v hv
    simpa only [hQ i hi v hv] using hline.1 v

end
end Balanced.SelectionOccupancy

end OAI
