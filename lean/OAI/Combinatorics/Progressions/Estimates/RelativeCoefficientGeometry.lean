import OAI.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw

namespace OAI

section

namespace Erdos3

theorem integerProgressionSupport_one (c m : ℤ) : integerProgressionSupport c m 1 = {c} := by
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by decide
  simp [integerProgressionSupport, hI, translateSupport, integerStrideHom]

structure RelativeProgression (δ : ℝ) where
  parentLength : ℕ
  parent_pos : 0 < parentLength
  root : ℤ
  step : ℕ
  length : ℕ
  step_pos : 0 < step
  contained : integerProgressionSupport root (step : ℤ) length ⊆ Finset.Ico (0 : ℤ) parentLength
  relative_size : δ * parentLength ≤ (integerProgressionSupport root (step : ℤ) length).card

namespace RelativeProgression

variable {δ : ℝ} (P : RelativeProgression δ)

def canonicalStep : ℕ := if P.length = 1 then 1 else P.step

def width : ℕ := P.canonicalStep * P.length

theorem canonicalStep_pos : 0 < P.canonicalStep := by
  unfold canonicalStep
  split_ifs
  · exact Nat.zero_lt_one
  · exact P.step_pos

theorem canonical_support :
    integerProgressionSupport P.root (P.canonicalStep : ℤ) P.length =
      integerProgressionSupport P.root (P.step : ℤ) P.length := by
  by_cases h : P.length = 1
  · simp only [canonicalStep, h, ite_true, integerProgressionSupport_one]
  · simp only [canonicalStep, h, ite_false]

theorem length_pos (hδ : 0 < δ) : 0 < P.length := by
  have h := P.relative_size
  rw [card_integerProgressionSupport P.root P.step P.length P.step_pos] at h
  have hn : (0 : ℝ) < P.parentLength := by exact_mod_cast P.parent_pos
  exact_mod_cast (mul_pos hδ hn).trans_le h

theorem width_pos (hδ : 0 < δ) : 0 < P.width := Nat.mul_pos P.canonicalStep_pos (P.length_pos hδ)

theorem geometric_bounds (hδ : 0 < δ) :
    δ * P.parentLength ≤ (P.width : ℝ) ∧ (P.width : ℝ) < 2 * P.parentLength ∧
      P.canonicalStep ≤ ⌈2 / δ⌉₊ ∧ |(P.root : ℝ)| ≤ δ⁻¹ * P.width := by
  by_cases h : P.length = 1
  · have hw : P.width = 1 := by simp [width, canonicalStep, h]
    have hs : P.canonicalStep = 1 := by simp [canonicalStep, h]
    have hd : δ * P.parentLength ≤ 1 := by
      have hd := P.relative_size
      simpa only [h, integerProgressionSupport_one, Finset.card_singleton, Nat.cast_one] using hd
    have hc : P.root ∈ Finset.Ico (0 : ℤ) P.parentLength := by
      apply P.contained
      simp only [h, integerProgressionSupport_one, Finset.mem_singleton]
    have hc0 : (0 : ℝ) ≤ P.root := by exact_mod_cast (Finset.mem_Ico.mp hc).1
    have hcN : (P.root : ℝ) < P.parentLength := by exact_mod_cast (Finset.mem_Ico.mp hc).2
    have hN : (1 : ℝ) ≤ P.parentLength := by exact_mod_cast P.parent_pos
    have hδ1 : δ ≤ 1 := by nlinarith
    have hdiv : (1 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    have hNdiv : (P.parentLength : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by nlinarith only [hd])
    rw [hw, hs]
    refine ⟨by simpa only [Nat.cast_one] using hd, ?_, ?_, ?_⟩
    · norm_num only [Nat.cast_one]
      linarith
    · exact_mod_cast hdiv.trans (Nat.le_ceil (2 / δ))
    · simpa only [Nat.cast_one, mul_one, one_div, abs_of_nonneg hc0] using hcN.le.trans hNdiv
  · have hlen : 2 ≤ P.length := by have := P.length_pos hδ; omega
    have hs : P.canonicalStep = P.step := by simp only [canonicalStep, h, ite_false]
    simpa only [width, hs] using progression_slice_geometry P.root P.parent_pos P.step_pos hlen hδ
      P.contained P.relative_size

def cubeSlice (q : ℕ) : FiniteCubeSlice q := progressionCubeSlice q P.canonicalStep P.length P.root

theorem cubeSlice_nonempty (q : ℕ) (hδ : 0 < δ) : Nonempty (P.cubeSlice q).Domain := by
  have h := progressionSupportedCube_nonempty q P.canonicalStep P.length P.root
    (P.width_pos hδ) P.canonicalStep_pos
  exact h.map (progressionResidueSupportedCubeEquiv q P.canonicalStep P.length P.root P.canonicalStep_pos)

end RelativeProgression

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem relativeProgression_family_bounds {g : ℕ} {δ : ℝ} (P : Fin g → RelativeProgression δ)
    (hδ : 0 < δ) {K F D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hupper : (∏ j, ((P j).parentLength : ℝ)) ≤ F * K)
    (hlower : K ≤ D * ∏ j, ((P j).parentLength : ℝ))
    (p : ℕ) (hpower : ∀ j, K ≤ E * ((P j).parentLength : ℝ) ^ p) :
    (∀ j, (P j).canonicalStep ≤ ⌈2 / δ⌉₊) ∧
    (∀ j, |((P j).root : ℝ)| ≤ δ⁻¹ * (P j).width) ∧
    (∏ j, ((P j).width : ℝ)) ≤ ((2 : ℝ) ^ g * F) * K ∧
    K ≤ (D * (δ⁻¹) ^ g) * (∏ j, ((P j).width : ℝ)) ∧
    ∀ j, K ≤ (E * (δ⁻¹) ^ p) * ((P j).width : ℝ) ^ p := by
  have hs j := (P j).geometric_bounds hδ
  have hside (j) : ((P j).parentLength : ℝ) ≤ δ⁻¹ * (P j).width := by
    have hh : ((P j).parentLength : ℝ) ≤ ((P j).width : ℝ) / δ :=
      (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using (hs j).1)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  refine ⟨fun j => (hs j).2.2.1, fun j => (hs j).2.2.2, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∏ j, 2 * ((P j).parentLength : ℝ) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun j _ => (hs j).2.1.le)
      _ = (2 : ℝ) ^ g * ∏ j, ((P j).parentLength : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 : ℝ) ^ g * (F * K) := mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ D * ∏ j, ((P j).parentLength : ℝ) := hlower
      _ ≤ D * ∏ j, δ⁻¹ * ((P j).width : ℝ) := mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hside j)) hD
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
  · intro j
    exact side_power_after_width_loss hE (Nat.cast_nonneg _) (hpower j) (hside j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem RelativeProgression.parent_le_index_length {δ : ℝ} (P : RelativeProgression δ) (hδ : 0 < δ) :
    (P.parentLength : ℝ) ≤ δ⁻¹ * P.length := by
  have h := P.relative_size
  rw [card_integerProgressionSupport P.root P.step P.length P.step_pos] at h
  have hh : (P.parentLength : ℝ) ≤ (P.length : ℝ) / δ :=
    (le_div_iff₀ hδ).mpr (by nlinarith only [h])
  simpa only [div_eq_mul_inv, mul_comm] using hh

theorem RelativeProgression.root_bounds {δ : ℝ} (P : RelativeProgression δ) (hδ : 0 < δ) :
    (0 : ℝ) ≤ P.root ∧ (P.root : ℝ) < P.parentLength := by
  have h := P.contained (integerProgressionSupport_point P.root P.step P.length P.step_pos 0 (P.length_pos hδ))
  have hh : P.root ∈ Finset.Ico (0 : ℤ) P.parentLength := by simpa only [Nat.cast_zero, mul_zero, add_zero] using h
  exact ⟨by exact_mod_cast (Finset.mem_Ico.mp hh).1, by exact_mod_cast (Finset.mem_Ico.mp hh).2⟩

theorem RelativeProgression.coefficient_radius_bound {δ : ℝ} (P : RelativeProgression δ) (hδ : 0 < δ) :
    |(P.root : ℝ)| + (P.canonicalStep : ℝ) * P.length ≤ 3 * P.parentLength := by
  have hr := P.root_bounds hδ
  have hw := (P.geometric_bounds hδ).2.1
  rw [abs_of_nonneg hr.1]
  simp only [RelativeProgression.width, Nat.cast_mul] at hw
  linarith

theorem relativeModerate_family_bounds {g : ℕ} {δ : ℝ}
    (c : RelativeProgression δ) (P : Fin g → RelativeProgression δ) (hδ : 0 < δ)
    {K F D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hupper : (c.parentLength : ℝ) * (∏ j, ((P j).parentLength : ℝ)) ≤ F * K)
    (hlower : K ≤ D * ((c.parentLength : ℝ) * ∏ j, ((P j).parentLength : ℝ)))
    (p : ℕ) (hpower : ∀ j, K ≤ E * ((P j).parentLength : ℝ) ^ p)
    (hcpower : K ≤ E * (c.parentLength : ℝ) ^ p) :
    (|(c.root : ℝ)| + (c.canonicalStep : ℝ) * c.length) * (∏ j, ((P j).width : ℝ)) ≤
        ((3 * (2 : ℝ) ^ g) * F) * K ∧
    K ≤ (D * (δ⁻¹) ^ (g + 1)) * ((c.length : ℝ) * ∏ j, ((P j).width : ℝ)) ∧
    (∀ j, K ≤ (E * (δ⁻¹) ^ p) * ((P j).width : ℝ) ^ p) ∧
    K ≤ (E * (δ⁻¹) ^ p) * (c.length : ℝ) ^ p := by
  have hside j : ((P j).parentLength : ℝ) ≤ δ⁻¹ * (P j).width := by
    have h := ((P j).geometric_bounds hδ).1
    have hh : ((P j).parentLength : ℝ) ≤ ((P j).width : ℝ) / δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith only [h])
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hpup : (∏ j, ((P j).width : ℝ)) ≤ (2 : ℝ) ^ g * ∏ j, ((P j).parentLength : ℝ) := by
    calc
      _ ≤ ∏ j, 2 * ((P j).parentLength : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => ((P j).geometric_bounds hδ).2.1.le)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hplo : (∏ j, ((P j).parentLength : ℝ)) ≤ (δ⁻¹) ^ g * ∏ j, ((P j).width : ℝ) := by
    calc
      _ ≤ ∏ j, δ⁻¹ * ((P j).width : ℝ) := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hside j)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨?_, ?_, fun j => side_power_after_width_loss hE (Nat.cast_nonneg _) (hpower j) (hside j), ?_⟩
  · calc
      _ ≤ (3 * c.parentLength) * ((2 : ℝ) ^ g * ∏ j, ((P j).parentLength : ℝ)) :=
        mul_le_mul (c.coefficient_radius_bound hδ) hpup (by positivity) (by positivity)
      _ = (3 * (2 : ℝ) ^ g) * ((c.parentLength : ℝ) * ∏ j, ((P j).parentLength : ℝ)) := by ring
      _ ≤ (3 * (2 : ℝ) ^ g) * (F * K) := mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ D * ((c.parentLength : ℝ) * ∏ j, ((P j).parentLength : ℝ)) := hlower
      _ ≤ D * ((δ⁻¹ * c.length) * ((δ⁻¹) ^ g * ∏ j, ((P j).width : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (c.parent_le_index_length hδ) hplo
          (by positivity) (by positivity)) hD
      _ = _ := by rw [pow_succ]; ring
  · exact side_power_after_width_loss hE (Nat.cast_nonneg _) hcpower (c.parent_le_index_length hδ)

end Erdos3

end

end OAI
