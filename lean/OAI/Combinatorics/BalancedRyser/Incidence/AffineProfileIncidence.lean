import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

namespace Balanced.FiniteProfile

open scoped BigOperators

theorem histogram_hasSum {α β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → β) :
    HasSum (fun b ↦ ((U.filter fun p ↦ f p = b).card : ℝ)) (U.card : ℝ) := by
  classical
  have h := hasSum_sum (s := U)
    (fun p _ ↦ hasSum_ite_eq' (f p) (1 : ℝ))
  simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
    using h

theorem weighted_histogram_hasSum {α β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → β) (w : β → ℝ) :
    HasSum (fun b ↦ w b * ((U.filter fun p ↦ f p = b).card : ℝ))
      (∑ p ∈ U, w (f p)) := by
  classical
  have h := hasSum_sum (s := U)
    (fun p _ ↦ hasSum_ite_eq' (f p) (w (f p)))
  convert h using 1
  funext b
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  simp only [Nat.cast_one, mul_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpb : f p = b <;> simp [hpb]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem incidence_count (D : Finset (Line F)) (U : Finset (Point F)) :
    (∑ l ∈ D, (U.filter fun p ↦ OnLine p l).card) =
      ∑ p ∈ U, deletionMultiplicity D p := by
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, deletionMultiplicity]
    using Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun l p ↦ OnLine p l) (s := D) (t := U)

theorem deletion_coordinate_incidence (D C : Finset (Line F)) (i j : ℕ) :
    (∑ l ∈ D, ((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card) =
    i * (Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card := by
  classical
  let U : Finset (Point F) := Finset.univ.filter fun p ↦
    deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j
  have heq (l : Line F) : (linePoints l).filter (fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j) =
      U.filter (fun p ↦ OnLine p l) := by
    ext p
    simp only [linePoints, U, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp_rw [heq]
  rw [incidence_count]
  calc
    (∑ p ∈ U, deletionMultiplicity D p) = ∑ _p ∈ U, i := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1
    _ = i * U.card := by simp [Nat.mul_comm]

theorem cover_coordinate_incidence (D C : Finset (Line F)) (i j : ℕ) :
    (∑ l ∈ C, ((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card) =
    j * (Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card := by
  simpa only [and_comm] using deletion_coordinate_incidence C D j i

theorem deletion_coordinate_incidence_real (D C : Finset (Line F)) (i j : ℕ) :
    (∑ l ∈ D, (((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) =
    (i : ℝ) * (((Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ) ^ 2) := by
  rw [← Finset.sum_div]
  have hc := deletion_coordinate_incidence D C i j
  have hcR : (∑ l ∈ D, (((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ)) =
    (i : ℝ) * ((Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) := by
    exact_mod_cast hc
  rw [hcR]
  ring

theorem cover_coordinate_incidence_real (D C : Finset (Line F)) (i j : ℕ) :
    (∑ l ∈ C, (((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) =
    (j : ℝ) * (((Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ) ^ 2) := by
  simpa only [and_comm] using deletion_coordinate_incidence_real C D j i

theorem plane_profile_hasSum (D C : Finset (Line F)) :
    HasSum (fun ij : ℕ × ℕ ↦
      ((Finset.univ.filter fun p : Point F ↦
        deletionMultiplicity D p = ij.1 ∧ deletionMultiplicity C p = ij.2).card : ℝ) /
        (Fintype.card F : ℝ) ^ 2) 1 := by
  have h := (histogram_hasSum (Finset.univ : Finset (Point F))
    (fun p ↦ (deletionMultiplicity D p, deletionMultiplicity C p))).div_const
      ((Fintype.card F : ℝ) ^ 2)
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (Finset.univ : Finset (Point F)).card = (Fintype.card F) ^ 2 := by
    simp [Point, pow_two]
  rw [hcard, Nat.cast_pow, div_self (pow_ne_zero 2 hq)] at h
  simpa only [Prod.ext_iff] using h

theorem empirical_multiplicity_hasSum (D : Finset (Line F)) :
    HasSum (empiricalMultiplicityMass D) 1 := by
  have h := (histogram_hasSum (Finset.univ : Finset (Point F))
    (deletionMultiplicity D)).div_const ((Fintype.card F : ℝ) ^ 2)
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (Finset.univ : Finset (Point F)).card = (Fintype.card F) ^ 2 := by
    simp [Point, pow_two]
  rw [hcard, Nat.cast_pow, div_self (pow_ne_zero 2 hq)] at h
  exact h

theorem line_profile_hasSum (D C : Finset (Line F)) (l : Line F) :
    HasSum (fun ij : ℕ × ℕ ↦
      (((linePoints l).filter fun p ↦
        deletionMultiplicity D p = ij.1 ∧ deletionMultiplicity C p = ij.2).card : ℝ) /
        (Fintype.card F : ℝ)) 1 := by
  have h := (histogram_hasSum (linePoints l)
    (fun p ↦ (deletionMultiplicity D p, deletionMultiplicity C p))).div_const
      (Fintype.card F : ℝ)
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [linePoints_card, div_self hq] at h
  simpa only [Prod.ext_iff] using h

theorem sum_multiplicity (D : Finset (Line F)) :
    (∑ p : Point F, deletionMultiplicity D p) = D.card * Fintype.card F := by
  rw [← incidence_count D Finset.univ]
  change (∑ l ∈ D, (linePoints l).card) = _
  simp [linePoints_card]

omit [Field F] in

theorem deletionSet_card {k : ℕ} {D : Finset (Line F)} (hD : IsDeletionSet k D) :
    D.card = k * (Fintype.card F + 1) := by
  have h := Finset.sum_card_fiberwise_eq_card_filter D
    (Finset.univ : Finset (Direction F)) Prod.fst
  have heach (d : Direction F) : (D.filter fun l ↦ l.1 = d).card = k := hD d
  simpa [heach, Fintype.card_option, Nat.mul_comm] using h.symm

theorem plane_profile_firstMoment_hasSum (D C : Finset (Line F)) :
    HasSum (fun ij : ℕ × ℕ ↦ ((ij.1 + ij.2 : ℕ) : ℝ) *
      (((Finset.univ.filter fun p : Point F ↦
        deletionMultiplicity D p = ij.1 ∧ deletionMultiplicity C p = ij.2).card : ℝ) /
        (Fintype.card F : ℝ) ^ 2))
      (((D.card + C.card : ℕ) : ℝ) / (Fintype.card F : ℝ)) := by
  have h := (weighted_histogram_hasSum (Finset.univ : Finset (Point F))
    (fun p ↦ (deletionMultiplicity D p, deletionMultiplicity C p))
    (fun ij : ℕ × ℕ ↦ ((ij.1 + ij.2 : ℕ) : ℝ))).div_const
      ((Fintype.card F : ℝ) ^ 2)
  have hs : (∑ p : Point F,
      ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) =
      ((D.card + C.card : ℕ) : ℝ) * (Fintype.card F : ℝ) := by
    simp only [Nat.cast_add, Finset.sum_add_distrib, ← Nat.cast_sum,
      sum_multiplicity, Nat.cast_mul]
    ring
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  convert! h using 1
  · funext ij
    simp only [Prod.ext_iff]
    ring
  · change ((D.card + C.card : ℕ) : ℝ) / (Fintype.card F : ℝ) =
      (∑ p : Point F, ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) /
        (Fintype.card F : ℝ) ^ 2
    rw [hs]
    field_simp

omit [Fintype F] in

theorem multiplicity_union (D C : Finset (Line F)) (hDC : Disjoint D C) (p : Point F) :
    deletionMultiplicity (D ∪ C) p = deletionMultiplicity D p + deletionMultiplicity C p := by
  unfold deletionMultiplicity
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact hDC.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem deletion_line_zero_row (D C : Finset (Line F)) {l : Line F}
    (hl : l ∈ D) (j : ℕ) :
    (linePoints l).filter (fun p ↦
      deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpl, hzero, _⟩
  have hon : OnLine p l := (Finset.mem_filter.mp hpl).2
  have hpos : 0 < deletionMultiplicity D p :=
    Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hon⟩⟩
  omega

theorem cover_line_zero_column (D C : Finset (Line F)) {l : Line F}
    (hl : l ∈ C) (i : ℕ) :
    (linePoints l).filter (fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = 0) = ∅ := by
  simpa only [and_comm] using deletion_line_zero_row C D hl i

theorem sum_multiplicity_on_line_le (E : Finset (Line F)) {l : Line F}
    (hl : l ∈ E) :
    (∑ p ∈ linePoints l, deletionMultiplicity E p) ≤
      Fintype.card F + E.card - 1 := by
  rw [← incidence_count]
  have heq (m : Line F) : (linePoints l).filter (fun p ↦ OnLine p m) =
      linePoints l ∩ linePoints m := by
    ext p
    simp [linePoints]
  simp_rw [heq]
  let f : Line F → ℕ := fun m ↦ (linePoints l ∩ linePoints m).card
  have hsum := Finset.sum_erase_add E f hl
  have hbound : (∑ m ∈ E.erase l, f m) ≤ (E.erase l).card := by
    calc
      (∑ m ∈ E.erase l, f m) ≤ ∑ _m ∈ E.erase l, 1 := by
        apply Finset.sum_le_sum
        intro m hm
        exact linePoints_inter_card_le_one l m
          (Ne.symm (Finset.ne_of_mem_erase hm))
      _ = (E.erase l).card := by simp
  have hself : f l = Fintype.card F := by simp [f, linePoints_card]
  have hcard := Finset.card_erase_of_mem hl
  change (∑ m ∈ E, f m) ≤ _
  rw [← hsum, hself]
  calc
    (∑ m ∈ E.erase l, f m) + Fintype.card F ≤
        (E.erase l).card + Fintype.card F := Nat.add_le_add_right hbound _
    _ ≤ Fintype.card F + E.card - 1 := by
      rw [hcard]
      have hE : 0 < E.card := Finset.card_pos.mpr ⟨l, hl⟩
      omega

theorem line_profile_firstMoment_hasSum (D C : Finset (Line F)) (l : Line F) :
    HasSum (fun ij : ℕ × ℕ ↦ ((ij.1 + ij.2 : ℕ) : ℝ) *
      ((((linePoints l).filter fun p ↦
        deletionMultiplicity D p = ij.1 ∧ deletionMultiplicity C p = ij.2).card : ℝ) /
        (Fintype.card F : ℝ)))
      ((∑ p ∈ linePoints l,
        ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) /
        (Fintype.card F : ℝ)) := by
  have h := (weighted_histogram_hasSum (linePoints l)
    (fun p ↦ (deletionMultiplicity D p, deletionMultiplicity C p))
    (fun ij : ℕ × ℕ ↦ ((ij.1 + ij.2 : ℕ) : ℝ))).div_const
      (Fintype.card F : ℝ)
  convert! h using 1
  funext ij
  simp only [Prod.ext_iff]
  ring

theorem line_profile_firstMoment_le (D C : Finset (Line F)) (hDC : Disjoint D C)
    {l : Line F} (hl : l ∈ D ∪ C) :
    (∑ p ∈ linePoints l,
      ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) /
        (Fintype.card F : ℝ) ≤
      1 + (((D.card + C.card : ℕ) : ℝ) - 1) / (Fintype.card F : ℝ) := by
  have hb := sum_multiplicity_on_line_le (D ∪ C) hl
  simp_rw [multiplicity_union D C hDC] at hb
  rw [Finset.card_union_of_disjoint hDC] at hb
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast hpos
  have hR : (∑ p ∈ linePoints l,
      ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) ≤
      (Fintype.card F : ℝ) + ((D.card + C.card : ℕ) : ℝ) - 1 := by
    have hnat : 1 ≤ Fintype.card F + (D.card + C.card) := by omega
    exact_mod_cast hb
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ (Fintype.card F : ℝ) + ((D.card + C.card : ℕ) : ℝ) - 1 := hR
    _ = (1 + (((D.card + C.card : ℕ) : ℝ) - 1) /
        (Fintype.card F : ℝ)) * (Fintype.card F : ℝ) := by
      field_simp
      ring

theorem plane_firstMoment_le_source_bound {k : ℕ} {D C : Finset (Line F)}
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    ((D.card + C.card : ℕ) : ℝ) / (Fintype.card F : ℝ) ≤ 2 * k + 4 := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hqpos : (0 : ℝ) < Fintype.card F := by linarith
  have hCR : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hC
  have hDR : (D.card : ℝ) = (k : ℝ) * (Fintype.card F + 1) := by
    exact_mod_cast deletionSet_card hD
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [div_le_iff₀ hqpos, Nat.cast_add, hDR]
  nlinarith

theorem line_firstMoment_le_source_bound {k : ℕ} {D C : Finset (Line F)}
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F)
    (hDC : Disjoint D C) {l : Line F} (hl : l ∈ D ∪ C) :
    (∑ p ∈ linePoints l,
      ((deletionMultiplicity D p + deletionMultiplicity C p : ℕ) : ℝ)) /
        (Fintype.card F : ℝ) ≤ 2 * k + 4 := by
  apply (line_profile_firstMoment_le D C hDC hl).trans
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hqpos : (0 : ℝ) < Fintype.card F := by linarith
  have hCR : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hC
  have hDR : (D.card : ℝ) = (k : ℝ) * (Fintype.card F + 1) := by
    exact_mod_cast deletionSet_card hD
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← le_sub_iff_add_le', div_le_iff₀ hqpos, Nat.cast_add, hDR]
  nlinarith

end Balanced.FiniteProfile

end OAI
