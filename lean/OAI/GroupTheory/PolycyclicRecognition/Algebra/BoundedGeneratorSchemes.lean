import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorSchemes
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace OAI

/-! # Quantitative bounds for a fixed generator scheme

The fixed conjugating words give a common amplitude bound; scaling a
logarithm into the local product chart and repeating the resulting word
covers any prescribed bounded logarithmic set.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I : Type*}

/-- Amplitudes in every fixed conjugating word admit one finite bound. -/
theorem exists_fixed_word_amplitude_bound {n : ℕ} (w : Fin n → List (I × ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k, ∀ p ∈ w k, |p.2| ≤ C := by
  let S := (List.ofFn w).flatten
  let C := 1 + (S.map (fun p => |p.2|)).sum
  have hnonneg : ∀ x ∈ S.map (fun p => |p.2|), (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  refine ⟨C, by dsimp [C]; linarith [List.sum_nonneg hnonneg], ?_⟩
  intro k p hp
  have hpS : p ∈ S := by
    exact List.mem_flatten.mpr ⟨w k, List.mem_ofFn.mpr ⟨k, rfl⟩, hp⟩
  have h := List.single_le_sum hnonneg |p.2| (List.mem_map.mpr ⟨p, hpS, rfl⟩)
  dsimp [C]
  linarith

/-- Inserting unit-bounded parameters keeps every amplitude uniformly bounded. -/
theorem generatorSchemeWord_amplitude_bound {n : ℕ} (w : Fin n → List (I × ℝ))
    (i : Fin n → I) {C : ℝ} (hC : 1 ≤ C)
    (hw : ∀ k, ∀ p ∈ w k, |p.2| ≤ C) (t : Fin n → ℝ) (ht : ‖t‖ ≤ 1) :
    ∀ p ∈ generatorSchemeWord w i t, |p.2| ≤ C := by
  intro p hp
  obtain ⟨s, hs, hp⟩ := List.mem_flatten.mp hp
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hs
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hw k p hp
    · have he : p = (i k, t k) := by simpa using hp
      rw [he]
      exact ((Real.norm_eq_abs _ ▸ norm_le_pi_norm t k).trans ht).trans hC
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq' : q ∈ w k := List.mem_reverse.mp hq
    simpa only [abs_neg] using hw k q hq'

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type*} [Group G]

local instance boundedSchemeNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance boundedSchemeNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

variable (X : I → L) (Exp : L → G)

/-- The one-parameter identity identifies integer multiples with group powers. -/
theorem exp_nat_smul (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : L) (k : ℕ) : Exp ((k : ℝ) • v) = (Exp v) ^ k := by
  induction k with
  | zero => simp [hzero]
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, hadd, ih, one_smul, pow_succ]

/-- Any bounded logarithmic set is covered by words of uniformly bounded
length and uniformly bounded generator amplitudes, for a fixed local scheme. -/
theorem bounded_generation_of_local_scheme {n : ℕ}
    (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    {ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ v : L, ‖v‖ < ε → ∃ t : Fin n → ℝ, ‖t‖ < 1 ∧
      generatorGroupWord X Exp (generatorSchemeWord w i t) = Exp v)
    (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ v : L, ‖v‖ ≤ R →
      ∃ u : List (I × ℝ), u.length ≤ N ∧ (∀ p ∈ u, |p.2| ≤ C) ∧
        generatorGroupWord X Exp u = Exp v := by
  obtain ⟨C, hC, hw⟩ := exists_fixed_word_amplitude_bound w
  obtain ⟨k, hk⟩ := exists_nat_gt (max (R / ε) 0)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkR : R < (k : ℝ) * ε := by
    have h := lt_of_le_of_lt (le_max_left (R / ε) 0) hk
    exact (div_lt_iff₀ hε).mp h
  refine ⟨k * ∑ j, (2 * (w j).length + 1), C, hC, ?_⟩
  intro v hv
  have hsmall : ‖((k : ℝ)⁻¹) • v‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0)]
    have h := lt_of_le_of_lt hv hkR
    rw [← div_eq_inv_mul]
    exact (div_lt_iff₀ hk0).mpr (by simpa only [mul_comm] using h)
  obtain ⟨t, ht, he⟩ := hlocal _ hsmall
  let u := generatorSchemeWord w i t
  refine ⟨(List.replicate k u).flatten, ?_, ?_, ?_⟩
  · simp only [List.length_flatten, List.map_replicate, List.sum_replicate]
    rw [length_generatorSchemeWord]
    simp
  · intro p hp
    obtain ⟨s, hs, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hs
    exact generatorSchemeWord_amplitude_bound w i hC hw t ht.le p hp
  · have hprod : generatorGroupWord X Exp ((List.replicate k u).flatten) =
        (generatorGroupWord X Exp u) ^ k := by
      simp only [generatorGroupWord, List.map_flatten, List.map_replicate,
        List.prod_flatten, List.prod_replicate]
    rw [hprod, he, ← exp_nat_smul Exp hzero hadd]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hk0), one_smul]

end PolycyclicRecognition

end

end OAI
