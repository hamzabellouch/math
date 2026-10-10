import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

theorem uniform_toOuterMeasure_equiv
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [Nonempty Ω] [Nonempty Ξ]
    (e : Ω ≃ Ξ) (A : Set Ξ) :
    (PMF.uniformOfFintype Ω).toOuterMeasure (e ⁻¹' A) =
      (PMF.uniformOfFintype Ξ).toOuterMeasure A := by
  classical
  let eA : (e ⁻¹' A) ≃ A :=
    { toFun := fun x => ⟨e x, x.2⟩
      invFun := fun y => ⟨e.symm y, by simp⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply,
    Fintype.card_congr eA, Fintype.card_congr e]

section Counting

variable {I F : Type*} [Fintype I] [Fintype F]
variable [DecidableEq I] [DecidableEq F]

theorem card_prescribed_coordinates (s : Finset I) (target : I → F) :
    (Finset.univ.filter (fun ω : I → F => ∀ i ∈ s, ω i = target i)).card =
      Fintype.card F ^ (Fintype.card I - s.card) := by
  have hset : Finset.univ.filter (fun ω : I → F => ∀ i ∈ s, ω i = target i) =
      Fintype.piFinset (fun i => if i ∈ s then {target i} else Finset.univ) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      split_ifs with hi
      · simpa using h i hi
      · simp
    · intro h i hi
      simpa [hi] using h i
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ]
  rw [Finset.prod_ite]
  simp [← Finset.compl_eq_univ_sdiff, Finset.filter_not, Finset.card_compl]

theorem card_many_coordinate_matches_le (target : I → F) (m : ℕ) :
    (Finset.univ.filter (fun ω : I → F =>
      m ≤ (Finset.univ.filter (fun i => ω i = target i)).card)).card ≤
      (Fintype.card I).choose m * Fintype.card F ^ (Fintype.card I - m) := by
  classical
  let cylinder (s : Finset I) : Finset (I → F) :=
    Finset.univ.filter (fun ω => ∀ i ∈ s, ω i = target i)
  have hcover : Finset.univ.filter (fun ω : I → F =>
      m ≤ (Finset.univ.filter (fun i => ω i = target i)).card) ⊆
      ((Finset.univ : Finset I).powersetCard m).biUnion cylinder := by
    intro ω hω
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (Finset.mem_filter.mp hω).2
    apply Finset.mem_biUnion.mpr
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hcard⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ ω, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hs hi)).2
  calc
    _ ≤ (((Finset.univ : Finset I).powersetCard m).biUnion cylinder).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ s ∈ (Finset.univ : Finset I).powersetCard m, (cylinder s).card :=
      Finset.card_biUnion_le
    _ = ∑ _s ∈ (Finset.univ : Finset I).powersetCard m,
        Fintype.card F ^ (Fintype.card I - m) := by
      apply Finset.sum_congr rfl
      intro s hs
      dsimp only [cylinder]
      rw [card_prescribed_coordinates,
        (Finset.mem_powersetCard.mp hs).2]
    _ = _ := by simp

theorem uniform_many_coordinate_matches_le [Nonempty F] (target : I → F) (m : ℕ) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {ω | m ≤ (Finset.univ.filter (fun i => ω i = target i)).card}).toReal ≤
      ((Fintype.card I).choose m : ℝ) / (Fintype.card F : ℝ) ^ m := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, Set.mem_ofPred_eq,
    Fintype.card_subtype, Fintype.card_fun, Nat.cast_pow]
  have hcard := card_many_coordinate_matches_le target m
  have hreal :
      ((Finset.univ.filter (fun ω : I → F =>
        m ≤ (Finset.univ.filter (fun i => ω i = target i)).card)).card : ℝ) ≤
      ((Fintype.card I).choose m : ℝ) *
        (Fintype.card F : ℝ) ^ (Fintype.card I - m) := by
    exact_mod_cast hcard
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  by_cases hmn : m ≤ Fintype.card I
  · calc
      _ ≤ (((Fintype.card I).choose m : ℝ) *
          (Fintype.card F : ℝ) ^ (Fintype.card I - m)) /
          (Fintype.card F : ℝ) ^ Fintype.card I :=
        div_le_div_of_nonneg_right hreal (by positivity)
      _ = _ := by
        rw [show (Fintype.card F : ℝ) ^ Fintype.card I =
          (Fintype.card F : ℝ) ^ (Fintype.card I - m) *
            (Fintype.card F : ℝ) ^ m by
          rw [← pow_add, Nat.sub_add_cancel hmn]]
        field_simp
  · have hz : (Fintype.card I).choose m = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hmn)
    simp only [hz, Nat.cast_zero, zero_mul, zero_div] at hreal ⊢
    exact div_nonpos_of_nonpos_of_nonneg hreal (by positivity)

theorem uniform_exists_many_coordinate_matches_le
    [Nonempty F] {P : Type*} [Fintype P] (target : P → I → F) (m : ℕ) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {ω | ∃ p, m ≤ (Finset.univ.filter (fun i => ω i = target p i)).card}).toReal ≤
      (Fintype.card P : ℝ) *
        (((Fintype.card I).choose m : ℝ) / (Fintype.card F : ℝ) ^ m) := by
  classical
  let bad (p : P) : Finset (I → F) := Finset.univ.filter (fun ω =>
    m ≤ (Finset.univ.filter (fun i => ω i = target p i)).card)
  have hset : Finset.univ.filter (fun ω : I → F =>
      ∃ p, m ≤ (Finset.univ.filter (fun i => ω i = target p i)).card) =
      Finset.univ.biUnion bad := by
    ext ω
    simp [bad]
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, Set.mem_ofPred_eq,
    Fintype.card_subtype, Fintype.card_fun, Nat.cast_pow]
  rw [hset]
  have hcount : ((Finset.univ.biUnion bad).card : ℝ) ≤
      ∑ p : P, ((bad p).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset P)) (t := bad))
  calc
    _ ≤ (∑ p : P, ((bad p).card : ℝ)) / (Fintype.card F : ℝ) ^ Fintype.card I :=
      div_le_div_of_nonneg_right hcount (by positivity)
    _ = ∑ p : P, ((bad p).card : ℝ) / (Fintype.card F : ℝ) ^ Fintype.card I :=
      Finset.sum_div _ _ _
    _ ≤ ∑ _p : P, (((Fintype.card I).choose m : ℝ) / (Fintype.card F : ℝ) ^ m) := by
      apply Finset.sum_le_sum
      intro p _
      have hp := uniform_many_coordinate_matches_le (target p) m
      rw [PMF.toOuterMeasure_uniformOfFintype_apply] at hp
      simpa only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, Set.mem_ofPred_eq,
        Fintype.card_subtype, Fintype.card_fun, Nat.cast_pow, bad] using hp
    _ = _ := by simp

end Counting

end Balanced

end OAI
