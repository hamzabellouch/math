import OAI.Combinatorics.BalancedRyser.Local.ReusePrefix

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def oldCountFin (r : Prescription F) (pre : List (Prescription F)) : Fin 5 :=
  ⟨oldCount pre r, Nat.lt_succ_of_le (oldCount_le_four pre r)⟩

def prefixScore : List (Prescription F) → ℕ
  | [] => 0
  | r :: pre => prefixScore pre + reuseSaving (oldCount pre r)

omit [Field F] [Fintype F] in
theorem oldCount_eq_generator_overlap (pre : List (Prescription F))
    (r : Prescription F) (hr : Function.Injective r.2.1) :
    oldCount pre r =
      (prescriptionGenerators r ∩ pre.toFinset.biUnion prescriptionGenerators).card := by
  exact card_oldGeneratorIndices (prescriptionTuple r) (exposedDirections pre) hr

omit [Field F] [Fintype F] in
theorem prefixScore_eq_reuseExposureScore (pre : List (Prescription F))
    (hvalid : ∀ r ∈ pre, Function.Injective r.2.1) :
    prefixScore pre = reuseExposureScore prescriptionGenerators pre := by
  induction pre with
  | nil => rfl
  | cons r pre ih =>
      have hr := hvalid r (by simp)
      have hpre : ∀ s ∈ pre, Function.Injective s.2.1 := by
        intro s hs
        exact hvalid s (by simp [hs])
      rw [prefixScore, reuseExposureScore, ih hpre,
        oldCount_eq_generator_overlap pre r hr]

omit [Fintype F] [DecidableEq F] in
theorem prefixEvent_false_of_not_injective (p : Point F)
    (pre : List (Prescription F)) (r : Prescription F) (hr : r ∈ pre)
    (hinvalid : ¬ Function.Injective r.2.1) (M : MergedPairs F) :
    ¬ prefixEvent p pre M := by
  intro h
  exact hinvalid (h r hr).1

theorem prefixWeight_eq_zero_of_not_injective (K : ℝ) (p : Point F)
    (pre : List (Prescription F))
    (hinvalid : ¬ ∀ r ∈ pre, Function.Injective r.2.1) :
    prefixWeight K p pre = 0 := by
  have hempty : ∀ M : MergedPairs F, ¬ prefixEvent p pre M := by
    intro M h
    exact hinvalid (fun r hr => (h r hr).1)
  simp [prefixWeight, Local.offsetProbability, hempty]

theorem score_cutoff_weight_eq (K : ℝ) (p : Point F)
    (pre : List (Prescription F)) (m : ℕ) :
    (if m ≤ reuseExposureScore prescriptionGenerators pre then prefixWeight K p pre else 0) =
      (if m ≤ prefixScore pre then prefixWeight K p pre else 0) := by
  by_cases hvalid : ∀ r ∈ pre, Function.Injective r.2.1
  · rw [prefixScore_eq_reuseExposureScore pre hvalid]
  · simp [prefixWeight_eq_zero_of_not_injective K p pre hvalid]

omit [Field F] [Fintype F] in
theorem prescriptionGenerators_card_le_four (r : Prescription F) :
    (prescriptionGenerators r).card ≤ 4 := by
  exact (Finset.card_image_le).trans (by simp)

theorem category_cutoff_weight_eq (K : ℝ) (p : Point F)
    (pre : List (Prescription F)) (r : Prescription F) (j : ℕ) :
    (if (prescriptionGenerators r ∩ pre.toFinset.biUnion prescriptionGenerators).card = j
      then prefixWeight K p (r :: pre) else 0) =
      (if oldCount pre r = j then prefixWeight K p (r :: pre) else 0) := by
  by_cases hr : Function.Injective r.2.1
  · rw [oldCount_eq_generator_overlap pre r hr]
  · have hz : prefixWeight K p (r :: pre) = 0 :=
      prefixWeight_eq_zero_of_not_injective K p (r :: pre)
        (fun h => hr (h r (by simp)))
    simp [hz]

omit [Fintype F] [DecidableEq F] in
theorem prefixEvent_iff (p : Point F) (pre : List (Prescription F)) (M : MergedPairs F) :
    prefixEvent p pre M ↔
      (∀ r ∈ pre, Function.Injective r.2.1 ∧ ∀ i, r.2.1 i ≠ r.1.1) ∧
      (∀ r ∈ pre, (∀ i, OnLine (tuplePoint M (prescriptionTuple r) i)
          (lineThrough r.1.1 p)) ∧
        ∀ i, tuplePoint M (prescriptionTuple r) i ≠ p) := by
  constructor
  · intro h
    exact ⟨fun r hr => ⟨(h r hr).1, (h r hr).2.1⟩,
      fun r hr => (h r hr).2.2⟩
  · rintro ⟨hstatic, hgeom⟩ r hr
    exact ⟨(hstatic r hr).1, (hstatic r hr).2, hgeom r hr⟩

end
end Balanced.ReuseTower

end OAI
