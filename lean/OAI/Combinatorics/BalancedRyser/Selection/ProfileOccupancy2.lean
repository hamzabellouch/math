import OAI.Combinatorics.BalancedRyser.Incidence.AffineProfileIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.Profile

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.FiniteProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mem_uncoveredBy_iff (D : Finset (Line F)) (p : Point F) :
    p ∈ uncoveredBy D ↔ deletionMultiplicity D p = 0 := by
  simp [uncoveredBy, deletionMultiplicity, Finset.filter_eq_empty_iff]

theorem planeProfile_zero_row_hasSum (D C : Finset (Line F)) :
    HasSum (fun j ↦ planeProfile D C (0, j))
      (((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2) := by
  have h := (histogram_hasSum (uncoveredBy D) (deletionMultiplicity C)).div_const
    ((Fintype.card F : ℝ) ^ 2)
  have heq (j : ℕ) : (Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = j) =
      (uncoveredBy D).filter (fun p ↦ deletionMultiplicity C p = j) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_uncoveredBy_iff]
  change HasSum (fun j ↦
    (((Finset.univ.filter fun p : Point F ↦ deletionMultiplicity D p = 0 ∧
      deletionMultiplicity C p = j).card : ℝ) / (Fintype.card F : ℝ) ^ 2)) _
  simpa only [heq] using h

theorem planeProfile_zero_column_hasSum (D C : Finset (Line F)) :
    HasSum (fun i ↦ planeProfile D C (i, 0))
      (((uncoveredBy C).card : ℝ) / (Fintype.card F : ℝ) ^ 2) := by
  have h := planeProfile_zero_row_hasSum C D
  simpa only [planeProfile, and_comm] using h

theorem lineProfile_zero_row_hasSum (D C : Finset (Line F)) (l : Line F) :
    HasSum (fun j ↦ lineProfile D C l (0, j))
      ((((linePoints l) ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) := by
  have h := (histogram_hasSum (linePoints l ∩ uncoveredBy D)
    (deletionMultiplicity C)).div_const (Fintype.card F : ℝ)
  have heq (j : ℕ) : ((linePoints l).filter fun p ↦
      deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = j) =
      (linePoints l ∩ uncoveredBy D).filter (fun p ↦ deletionMultiplicity C p = j) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter, mem_uncoveredBy_iff]
    tauto
  change HasSum (fun j ↦
    ((((linePoints l).filter fun p ↦ deletionMultiplicity D p = 0 ∧
      deletionMultiplicity C p = j).card : ℝ) / (Fintype.card F : ℝ))) _
  simpa only [heq] using h

theorem planeProfile_zero_zero_of_cover (D C : Finset (Line F))
    (hcover : CoversPoints C (uncoveredBy D)) : planeProfile D C (0, 0) = 0 := by
  have hempty : (Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨hD, hC⟩
    have hpD := (mem_uncoveredBy_iff D p).mpr hD
    obtain ⟨l, hl, hpl⟩ := hcover p hpD
    have hpos : 0 < deletionMultiplicity C p :=
      Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hpl⟩⟩
    omega
  change (((Finset.univ.filter fun p : Point F ↦
    deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = 0).card : ℝ) /
      (Fintype.card F : ℝ) ^ 2) = 0
  rw [hempty]
  simp

theorem covered_points_card_le (C : Finset (Line F)) (U : Finset (Point F))
    (hcover : CoversPoints C U) : U.card ≤ C.card * Fintype.card F := by
  calc
    U.card = ∑ _p ∈ U, 1 := by simp
    _ ≤ ∑ p ∈ U, deletionMultiplicity C p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨l, hl, hpl⟩ := hcover p hp
      exact Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hpl⟩⟩
    _ = ∑ l ∈ C, (U.filter fun p ↦ OnLine p l).card := (incidence_count C U).symm
    _ ≤ ∑ _l ∈ C, Fintype.card F := by
      apply Finset.sum_le_sum
      intro l hl
      rw [← linePoints_card l]
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    _ = C.card * Fintype.card F := by simp

theorem core_cover_normalized_card_le (D C : Finset (Line F))
    (hcover : CoversPoints C (uncoveredBy D)) :
    ((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 ≤
      (C.card : ℝ) / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hR : ((uncoveredBy D).card : ℝ) ≤ (C.card : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast covered_points_card_le C (uncoveredBy D) hcover
  apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
  convert! hR using 1
  field_simp

end Balanced.FiniteProfile

end

end OAI
