import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryCocycle
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyWordLength
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! # Scalar projections of normalized unitary cocycles

Positive generator energy gives a scalar function with a fixed nonzero
normalization. Its harmonic defect is bounded by the vector-valued defect.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G E : Type*} [Group G] [DecidableEq G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitaryCocycleEnergy (S : Finset G) (b : G → E) : ℝ :=
  ∑ s ∈ S, ‖b s‖ ^ 2

omit [Group G] [DecidableEq G] [InnerProductSpace ℝ E] in
theorem unitaryCocycleEnergy_nonneg (S : Finset G) (b : G → E) :
    0 ≤ unitaryCocycleEnergy S b := sum_nonneg (fun _ _ => sq_nonneg _)

omit [Group G] [DecidableEq G] [InnerProductSpace ℝ E] in
theorem unitaryCocycleEnergy_generator_bound (S : Finset G) (b : G → E)
    {s : G} (hs : s ∈ S) : ‖b s‖ ≤ Real.sqrt (unitaryCocycleEnergy S b) := by
  apply (Real.le_sqrt (norm_nonneg _) (unitaryCocycleEnergy_nonneg S b)).mpr
  exact single_le_sum (fun t _ => sq_nonneg ‖b t‖) hs

omit [DecidableEq G] in
theorem IsUnitaryCocycle.norm_word_energy_le
    {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (S : Finset G) (l : List G) (hl : ∀ s ∈ l, s ∈ S) :
    ‖b l.prod‖ ≤ l.length * Real.sqrt (unitaryCocycleEnergy S b) := by
  induction l with
  | nil => simp [hb.map_one]
  | cons s l ih =>
    rw [List.prod_cons, hb, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖b s‖ + ‖ρ s (b l.prod)‖ := norm_add_le _ _
      _ = ‖b s‖ + ‖b l.prod‖ := by rw [(ρ s).norm_map]
      _ ≤ Real.sqrt (unitaryCocycleEnergy S b) +
          l.length * Real.sqrt (unitaryCocycleEnergy S b) :=
        add_le_add (unitaryCocycleEnergy_generator_bound S b
          (hl s (List.mem_cons_self ..)))
          (ih (fun t ht => hl t (List.mem_cons_of_mem s ht)))
      _ = _ := by ring

theorem IsUnitaryCocycle.norm_wordLength_energy_le
    {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ‖b g‖ ≤ cayleyWordLength S hS hgen g * Real.sqrt (unitaryCocycleEnergy S b) := by
  obtain ⟨l, hl, hmem, he⟩ := (mem_wordBall_iff S _ g).mp
    ((cayleyWordLength_le_iff S hS hgen g _).mp le_rfl)
  calc
    _ = ‖b l.prod‖ := by rw [he]
    _ ≤ l.length * Real.sqrt (unitaryCocycleEnergy S b) := hb.norm_word_energy_le S l hmem
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hl) (Real.sqrt_nonneg _)

def unitaryCocycleProjection (S : Finset G) (b : G → E) (t g : G) : ℝ :=
  inner ℝ (b g) (b t) / unitaryCocycleEnergy S b

theorem unitaryCocycleProjection_word_bound
    {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hE : 0 < unitaryCocycleEnergy S b) {t : G} (ht : t ∈ S) (g : G) :
    |unitaryCocycleProjection S b t g| ≤ cayleyWordLength S hS hgen g := by
  rw [unitaryCocycleProjection, abs_div, abs_of_pos hE, div_le_iff₀ hE]
  calc
    _ ≤ ‖b g‖ * ‖b t‖ := abs_real_inner_le_norm _ _
    _ ≤ (cayleyWordLength S hS hgen g * Real.sqrt (unitaryCocycleEnergy S b)) *
        Real.sqrt (unitaryCocycleEnergy S b) :=
      mul_le_mul (hb.norm_wordLength_energy_le S hS hgen g)
        (unitaryCocycleEnergy_generator_bound S b ht) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hE.le]

omit [DecidableEq G] in
theorem unitaryCocycleProjection_defect
    {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (S : Finset G) (t g : G) :
    (∑ s ∈ S, (unitaryCocycleProjection S b t (g * s) -
      unitaryCocycleProjection S b t g)) =
      inner ℝ (ρ g (∑ s ∈ S, b s)) (b t) / unitaryCocycleEnergy S b := by
  simp only [unitaryCocycleProjection, hb g, inner_add_left, add_div,
    add_sub_cancel_left, ← sum_div, ← sum_inner, ← map_sum]

omit [DecidableEq G] in
theorem unitaryCocycleProjection_defect_bound
    {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (S : Finset G) (hE : 0 < unitaryCocycleEnergy S b) {t : G} (ht : t ∈ S) (g : G) :
    |∑ s ∈ S, (unitaryCocycleProjection S b t (g * s) -
      unitaryCocycleProjection S b t g)| ≤
        ‖∑ s ∈ S, b s‖ / Real.sqrt (unitaryCocycleEnergy S b) := by
  rw [unitaryCocycleProjection_defect hb, abs_div, abs_of_pos hE]
  have hsqrt : 0 < Real.sqrt (unitaryCocycleEnergy S b) := Real.sqrt_pos.mpr hE
  calc
    _ ≤ (‖∑ s ∈ S, b s‖ * Real.sqrt (unitaryCocycleEnergy S b)) /
        unitaryCocycleEnergy S b := by
      apply div_le_div_of_nonneg_right _ hE.le
      exact (abs_real_inner_le_norm _ _).trans (by
        rw [(ρ g).norm_map]
        exact mul_le_mul_of_nonneg_left (unitaryCocycleEnergy_generator_bound S b ht)
          (norm_nonneg _))
    _ = _ := by
      apply (div_eq_div_iff hE.ne' hsqrt.ne').mpr
      rw [mul_assoc, Real.mul_self_sqrt hE.le]

theorem exists_normalized_unitaryCocycleProjection
    {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hE : 0 < unitaryCocycleEnergy S b) :
    ∃ f : G → ℝ, f 1 = 0 ∧
      (∀ g, |f g| ≤ cayleyWordLength S hS hgen g) ∧
      (1 / (S.card : ℝ)) ^ 2 ≤ ∑ s ∈ S, (f s) ^ 2 ∧
      ∀ g, |∑ s ∈ S, (f (g * s) - f g)| ≤
        ‖∑ s ∈ S, b s‖ / Real.sqrt (unitaryCocycleEnergy S b) := by
  have hne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h] at hE
    simp [unitaryCocycleEnergy] at hE
  obtain ⟨t, ht, hmax⟩ := exists_max_image S (fun s => ‖b s‖ ^ 2) hne
  have hm : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hne)
  have hsum : unitaryCocycleEnergy S b ≤ S.card * ‖b t‖ ^ 2 := by
    exact (sum_le_sum (fun s hs => hmax s hs)).trans_eq (by simp)
  have htval : 1 / (S.card : ℝ) ≤ unitaryCocycleProjection S b t t := by
    rw [unitaryCocycleProjection, real_inner_self_eq_norm_sq]
    exact (div_le_div_iff₀ hm hE).mpr (by nlinarith)
  refine ⟨unitaryCocycleProjection S b t, ?_,
    unitaryCocycleProjection_word_bound hb S hS hgen hE ht, ?_,
    unitaryCocycleProjection_defect_bound hb S hE ht⟩
  · simp [unitaryCocycleProjection, hb.map_one]
  · exact (pow_le_pow_left₀ (by positivity) htval 2).trans
      (single_le_sum (fun s _ => sq_nonneg _) ht)

end PolycyclicRecognition

end

end OAI
