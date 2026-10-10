import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.Profile

namespace OAI

noncomputable section
open Finset

namespace Balanced
open scoped _root_.Balanced

theorem hasSum_card_fibers {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    HasSum (fun b => ((s.filter (fun a => f a = b)).card : ℝ)) (s.card : ℝ) := by
  classical
  have hsum : (∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ)) = s.card := by
    exact_mod_cast (Finset.card_eq_sum_card_image f s).symm
  rw [← hsum]
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  have hempty : s.filter (fun a => f a = b) = ∅ := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨ha, hab⟩
    exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
  simp only [hempty, Finset.card_empty, Nat.cast_zero]

theorem hasSum_normalized_card_fibers {α β : Type*} [DecidableEq β]
    (s : Finset α) (hs : s.Nonempty) (f : α → β) :
    HasSum (fun b => ((s.filter (fun a => f a = b)).card : ℝ) / (s.card : ℝ)) 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  simpa only [div_self hc] using (hasSum_card_fibers s f).div_const (s.card : ℝ)

theorem hasSum_weighted_card_fibers {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (w : β → ℝ) :
    HasSum (fun b => w b * ((s.filter (fun a => f a = b)).card : ℝ))
      (∑ a ∈ s, w (f a)) := by
  classical
  have hsupport (b : β) (hb : b ∉ s.image f) :
      w b * ((s.filter (fun a => f a = b)).card : ℝ) = 0 := by
    have hempty : s.filter (fun a => f a = b) = ∅ := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨ha, hab⟩
      exact hb (Finset.mem_image.mpr ⟨a, ha, hab⟩)
    simp [hempty]
  have hsum : (∑ b ∈ s.image f, w b * ((s.filter (fun a => f a = b)).card : ℝ)) =
      ∑ a ∈ s, w (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha)
      (fun a => w (f a))]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      w b * ((s.filter (fun a => f a = b)).card : ℝ) =
          ∑ a ∈ s.filter (fun a => f a = b), w b := by simp [mul_comm]
      _ = ∑ a ∈ s.filter (fun a => f a = b), w (f a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hsupport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem planeProfile_nonneg (D C : Finset (Line F)) (ij : ℕ × ℕ) :
    0 ≤ planeProfile D C ij := by
  unfold planeProfile
  positivity

theorem planeProfile_hasSum (D C : Finset (Line F)) :
    HasSum (planeProfile D C) 1 := by
  have h := hasSum_normalized_card_fibers
    (Finset.univ : Finset (Point F)) Finset.univ_nonempty
    (fun x => (lineMultiplicity D x, lineMultiplicity C x))
  convert! h using 1
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [planeProfile, Prod.mk.injEq, Finset.card_univ, Point,
    Fintype.card_prod, Nat.cast_mul, pow_two]

theorem lineProfile_nonneg (D C : Finset (Line F)) (l : Line F) (ij : ℕ × ℕ) :
    0 ≤ lineProfile D C l ij := by
  unfold lineProfile
  positivity

theorem lineProfile_hasSum_of_card (D C : Finset (Line F)) (l : Line F)
    (hcard : (linePoints l).card = Fintype.card F) :
    HasSum (lineProfile D C l) 1 := by
  have hnonempty : (linePoints l).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    exact Fintype.card_pos
  have h := hasSum_normalized_card_fibers (linePoints l) hnonempty
    (fun x => (lineMultiplicity D x, lineMultiplicity C x))
  convert! h using 1
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [lineProfile, Prod.mk.injEq, hcard]

theorem lineProfile_hasSum (D C : Finset (Line F)) (l : Line F) :
    HasSum (lineProfile D C l) 1 :=
  lineProfile_hasSum_of_card D C l (linePoints_card l)

theorem planeProfile_weighted_hasSum (D C : Finset (Line F)) (w : ℕ × ℕ → ℝ) :
    HasSum (fun ij => w ij * planeProfile D C ij)
      ((∑ x : Point F, w (lineMultiplicity D x, lineMultiplicity C x)) /
        (Fintype.card F : ℝ) ^ 2) := by
  have h := (hasSum_weighted_card_fibers (Finset.univ : Finset (Point F))
    (fun x => (lineMultiplicity D x, lineMultiplicity C x)) w).div_const
      ((Fintype.card F : ℝ) ^ 2)
  convert! h using 1
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [planeProfile, Prod.mk.injEq]
  ring

theorem lineProfile_weighted_hasSum (D C : Finset (Line F)) (l : Line F)
    (w : ℕ × ℕ → ℝ) :
    HasSum (fun ij => w ij * lineProfile D C l ij)
      ((∑ x ∈ linePoints l, w (lineMultiplicity D x, lineMultiplicity C x)) /
        (Fintype.card F : ℝ)) := by
  have h := (hasSum_weighted_card_fibers (linePoints l)
    (fun x => (lineMultiplicity D x, lineMultiplicity C x)) w).div_const
      (Fintype.card F : ℝ)
  convert! h using 1
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [lineProfile, Prod.mk.injEq]
  ring

omit [Fintype F] in

theorem sum_lineMultiplicity (E : Finset (Line F)) (U : Finset (Point F)) :
    (∑ x ∈ U, lineMultiplicity E x) =
      ∑ l ∈ E, (U.filter (fun x => OnLine x l)).card := by
  classical
  simp only [lineMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_univ_lineMultiplicity (E : Finset (Line F)) :
    (∑ x : Point F, lineMultiplicity E x) = E.card * Fintype.card F := by
  rw [sum_lineMultiplicity]
  change (∑ l ∈ E, (linePoints l).card) = _
  simp [linePoints_card]

theorem planeProfile_firstMoment_hasSum (D C : Finset (Line F)) :
    HasSum (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ) * planeProfile D C ij)
      (((D.card : ℝ) + C.card) / (Fintype.card F : ℝ)) := by
  have h := planeProfile_weighted_hasSum D C (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ))
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  convert! h using 1
  simp only [Nat.cast_add, Finset.sum_add_distrib, ← Nat.cast_sum,
    sum_univ_lineMultiplicity, Nat.cast_mul]
  field_simp

omit [Field F] in

theorem profile_deletionSet_card (k : ℕ) (D : Finset (Line F)) (hD : IsDeletionSet k D) :
    D.card = k * (Fintype.card F + 1) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := D) (t := (Finset.univ : Finset (Direction F))) (f := Prod.fst)
    (fun _ _ => Finset.mem_univ _)
  rw [h]
  change (∑ d : Direction F, (D.filter (fun l => l.1 = d)).card) = _
  unfold IsDeletionSet at hD
  simp_rw [hD]
  simp [Fintype.card_option, mul_comm]

theorem planeProfile_isBounded (k : ℕ) (D C : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    IsBoundedProfile (2 * (k : ℝ) + 4) (planeProfile D C) := by
  have hm := planeProfile_firstMoment_hasSum D C
  refine ⟨planeProfile_nonneg D C, planeProfile_hasSum D C, hm.summable, ?_⟩
  rw [hm.tsum_eq]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hqone : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hc : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hC
  have hd : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast profile_deletionSet_card k D hD
  rw [hd]
  apply (div_le_iff₀ hq).2
  have hkq : 0 ≤ (k : ℝ) * ((Fintype.card F : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hqone)
  nlinarith

theorem sum_on_line_lineMultiplicity_le (E : Finset (Line F)) (l : Line F) :
    (∑ x ∈ linePoints l, lineMultiplicity E x) ≤ Fintype.card F + E.card := by
  classical
  rw [sum_lineMultiplicity]
  have hfilter (m : Line F) :
      (linePoints l).filter (fun x => OnLine x m) = linePoints l ∩ linePoints m := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, linePoints,
      Finset.mem_univ, true_and]
  simp_rw [hfilter]
  calc
    (∑ m ∈ E, (linePoints l ∩ linePoints m).card) ≤
        ∑ m ∈ E, ((if m = l then Fintype.card F else 0) + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases hml : m = l
      · subst m
        simp [linePoints_card]
      · simp only [ite_eq_right hml, zero_add]
        exact linePoints_inter_card_le_one l m (Ne.symm hml)
    _ = (if l ∈ E then Fintype.card F else 0) + E.card := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_const,
        Nat.smul_one_eq_cast, Nat.cast_id]
    _ ≤ Fintype.card F + E.card := by
      split_ifs <;> omega

theorem lineProfile_isBounded (k : ℕ) (D C : Finset (Line F)) (l : Line F)
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    IsBoundedProfile (2 * (k : ℝ) + 4) (lineProfile D C l) := by
  have hm := lineProfile_weighted_hasSum D C l
    (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ))
  refine ⟨lineProfile_nonneg D C l, lineProfile_hasSum D C l, hm.summable, ?_⟩
  rw [hm.tsum_eq]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hqone : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hc : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hC
  have hd : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast profile_deletionSet_card k D hD
  have hsd : (∑ x ∈ linePoints l, (lineMultiplicity D x : ℝ)) ≤
      (Fintype.card F : ℝ) + D.card := by
    exact_mod_cast sum_on_line_lineMultiplicity_le D l
  have hsc : (∑ x ∈ linePoints l, (lineMultiplicity C x : ℝ)) ≤
      (Fintype.card F : ℝ) + C.card := by
    exact_mod_cast sum_on_line_lineMultiplicity_le C l
  simp only [Nat.cast_add, Finset.sum_add_distrib]
  apply (div_le_iff₀ hq).2
  have hkq : 0 ≤ (k : ℝ) * ((Fintype.card F : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hqone)
  nlinarith

end Balanced

end

end OAI
