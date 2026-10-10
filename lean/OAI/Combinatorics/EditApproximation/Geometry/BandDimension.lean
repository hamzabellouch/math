import OAI.Combinatorics.EditApproximation.Geometry.RepresentativeBands
import OAI.Combinatorics.EditApproximation.Geometry.ActionVectors
import OAI.Combinatorics.EditApproximation.Refinement.ComputedGroupNumerical

namespace OAI

/-! The dimension charged by entropy is the number of actual child coordinates. -/

namespace EditApproximation

open Finset

theorem wideChildStateList_length_le {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (hP : 0 < P) (i : Fin M) :
    (wideChildStateList parent r b P i).length ≤ (40 * P + 2) ^ 2 := by
  have h := gridStateBox_length_le ny (seedGridSpacing b P) (10 * b)
    (r.lo + ((sourceChild parent i).lo - parent.lo))
    (r.lo + ((sourceChild parent i).hi - parent.lo)) (by unfold seedGridSpacing; omega)
  exact h.trans (Nat.pow_le_pow_left (by
    simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hP) 2)

theorem bandCoordinates_card_le {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (hP : 0 < P) (band : List (Fin M → TargetInterval ny))
    (hband : ∀ action ∈ band, action ∈ wideActionList M parent r b P) :
    (bandCoordinates band.toFinset).card ≤ M * (40 * P + 2) ^ 2 := by
  classical
  let coordinateSet := univ.biUnion fun i : Fin M =>
    (wideChildStateList parent r b P i).toFinset.image fun s => (i, s)
  have hsub : bandCoordinates band.toFinset ⊆ coordinateSet := by
    intro coordinate hcoordinate
    obtain ⟨action, ha, hcoord⟩ := mem_biUnion.mp hcoordinate
    obtain ⟨i, _, rfl⟩ := mem_image.mp hcoord
    apply mem_biUnion.mpr
    refine ⟨i, mem_univ _, mem_image.mpr ⟨action i, ?_, rfl⟩⟩
    exact List.mem_toFinset.mpr (finiteAssignments_sound M _ action
      (hband action (List.mem_toFinset.mp ha)) i)
  have hsum : coordinateSet.card ≤ ∑ i : Fin M, (40 * P + 2) ^ 2 := by
    apply (card_biUnion_le).trans
    apply sum_le_sum
    intro i _
    exact (card_image_le).trans ((List.toFinset_card_le _).trans
      (wideChildStateList_length_le parent r hP i))
  exact (card_le_card hsub).trans (by simpa only [sum_const, card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] using hsum)

theorem computed_band_dimension_log (N : ℕ) (hN : 0 < N)
    (hell : 42 ≤ inputSmallLog N) {nx ny b : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (band : List (Fin (integerParameters N).M → TargetInterval ny))
    (hband : ∀ action ∈ band, action ∈ wideActionList (integerParameters N).M parent r b (integerParameters N).P) :
    Real.log (bandCoordinates band.toFinset).card ≤
      4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ) := by
  let ell := inputSmallLog N
  let p := coarseExponent ell
  let H := inputHeight N
  let P := (integerParameters N).P
  let M := (integerParameters N).M
  let d := (bandCoordinates band.toFinset).card
  have hellR : (42 : ℝ) ≤ ell := by exact_mod_cast hell
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hPpos : 0 < P := pow_pos (Nat.two_pow_pos (heightExponent N)) _
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast hPpos
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMexp : (M : ℝ) ≤ Real.exp ell :=
    (show (M : ℝ) ≤ H by exact_mod_cast hM).trans (computed_height_exp_upper N hN)
  have hPexp : (P : ℝ) ≤ Real.exp (((p : ℝ) + 20) * ell) := by
    change ((H ^ (p + 20) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_pow]
    have h := pow_le_pow_left₀ (Nat.cast_nonneg H) (computed_height_exp_upper N hN) (p + 20)
    rw [← Real.exp_nat_mul] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have h42 : (42 : ℝ) ≤ Real.exp ell := by linarith only [Real.add_one_le_exp (ell : ℝ), hellR]
  have hbox : (40 * P + 2 : ℝ) ≤ Real.exp (((p : ℝ) + 21) * ell) := by
    calc
      (40 * P + 2 : ℝ) ≤ 42 * P := by linarith only [hPone]
      _ ≤ Real.exp ell * Real.exp (((p : ℝ) + 20) * ell) :=
        mul_le_mul h42 hPexp (Nat.cast_nonneg P) (Real.exp_pos _).le
      _ = Real.exp (((p : ℝ) + 21) * ell) := by rw [← Real.exp_add]; congr 1; ring
  have hcount : (d : ℝ) ≤ M * (40 * P + 2 : ℝ) ^ 2 := by
    exact_mod_cast bandCoordinates_card_le parent r hPpos band hband
  have hexp : (d : ℝ) ≤ Real.exp (4 * ((p : ℝ) + 21) * ell) := by
    apply hcount.trans
    have h := mul_le_mul hMexp (pow_le_pow_left₀ (by positivity) hbox 2) (by positivity)
      (Real.exp_pos _).le
    apply h.trans
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num only [Nat.cast_ofNat]
    apply Real.exp_le_exp.mpr
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith only [mul_nonneg hp hell0, hell0]
  by_cases hd : d = 0
  · change Real.log (d : ℝ) ≤ _
    rw [hd, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · have hdR : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    have hlog := (Real.log_le_iff_le_exp hdR).2 hexp
    simpa only [p, ell, d, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hlog

end EditApproximation

end OAI
