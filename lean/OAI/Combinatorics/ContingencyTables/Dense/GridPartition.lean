import OAI.Combinatorics.ContingencyTables.Dense.GridMass

namespace OAI

/-!
# Partition of cube mass by the finite bins

The union misses only grid hyperplanes. Thus a predicate and its complement
have continuous masses summing to the cube mass, which lets the conductance
argument select the smaller continuous side.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

variable {q K : ℕ}

theorem cube_ae_all_bins :
    {x : Fin q → ℝ | Cube K x} =ᵐ[volume] selectedBins K (fun _ => True) := by
  filter_upwards [ae_off_grid (I := Fin q)] with x hoff
  apply propext
  constructor
  · intro hx
    have hb (j : Fin q) : ⌊x j⌋ ∈ Set.Icc (0 : ℤ) ((K : ℤ) - 1) := by
      refine ⟨Int.floor_nonneg.mpr (hx j).1.le, ?_⟩
      have hlt : ⌊x j⌋ < (K : ℤ) := Int.floor_lt.mpr (by simpa using (hx j).2)
      omega
    refine ⟨(fun j => ⟨⌊x j⌋, hb j⟩), trivial, ?_⟩
    intro j
    exact ⟨lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hoff j _)), Int.lt_floor_add_one _⟩
  · rintro ⟨a, _, ha⟩
    exact openBin_in_cube a x ha

theorem cube_integral_bins (ρ : (Fin q → ℝ) → ℝ)
    (hi : IntegrableOn ρ (ambientBox q K)) :
    (∫ x in {x | Cube K x}, ρ x) =
      ∑ a : Grid (I := Fin q) K, ∫ x in binSet a, ρ x := by
  rw [setIntegral_congr_set cube_ae_all_bins, selectedBins_integral _ ρ hi]
  simpa only using
    (Finset.sum_subtype Finset.univ (fun _ => by simp)
      (fun a : Grid (I := Fin q) K => ∫ x in binSet a, ρ x)).symm

theorem selected_complement_integral (Q : (Fin q → ℤ) → Prop)
    (ρ : (Fin q → ℝ) → ℝ) (hi : IntegrableOn ρ (ambientBox q K)) :
    (∫ x in selectedBins K Q, ρ x) +
        (∫ x in selectedBins K (fun a => ¬ Q a), ρ x) =
      ∫ x in {x | Cube K x}, ρ x := by
  classical
  rw [selectedBins_integral Q ρ hi, selectedBins_integral (fun a => ¬ Q a) ρ hi,
    cube_integral_bins ρ hi]
  have hQ (Q : (Fin q → ℤ) → Prop) :
      (∑ a : Selected K Q, ∫ x in binSet a.val, ρ x) =
        ∑ a ∈ Finset.univ.filter (fun a : Grid (I := Fin q) K => Q (corner a)),
          ∫ x in binSet a, ρ x := by
    exact (Finset.sum_subtype (p := fun a : Grid (I := Fin q) K => Q (corner a))
      (F := instFintypeSelected Q)
      (Finset.univ.filter (fun a : Grid (I := Fin q) K => Q (corner a)))
      (fun a => by simp) (fun a => ∫ x in binSet a, ρ x)).symm
  rw [hQ Q, hQ (fun a => ¬ Q a)]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : Q (corner a) <;> simp [h]

theorem selected_mass_positive (Q : (Fin q → ℤ) → Prop)
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 < w a) (hi : IntegrableOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x)
    (hne : Nonempty (Selected K Q)) : 0 < ∫ x in selectedBins K Q, ρ x := by
  have hs : 0 < ∑ a : Selected K Q, w a.val := by
    obtain ⟨a⟩ := hne
    apply Finset.sum_pos'
    · intro b _
      exact (hw b.val).le
    · exact ⟨a, Finset.mem_univ _, hw a.val⟩
  exact (div_pos hs (by norm_num)).trans_le (selectedBins_mass_lower Q ρ w hi hbin)

end ContingencyTables.GridBoundary

end OAI
