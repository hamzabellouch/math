import OAI.Analysis.Cotype.WalshCoordinates
import OAI.Analysis.Cotype.WalshLower
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem average_norm_mul_le {n : ℕ} (f : Cube n → X) (g : Cube n → Y) :
    average (fun u => ‖f u‖ * ‖g u‖) ≤ cubeL2 X f * cubeL2 Y g := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun u => ‖f u‖) (fun u => ‖g u‖)
  have hq : 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ := by positivity
  calc
    _ ≤ (Fintype.card (Cube n) : ℝ)⁻¹ *
        (Real.sqrt (∑ u, ‖f u‖^2) * Real.sqrt (∑ u, ‖g u‖^2)) :=
      mul_le_mul_of_nonneg_left h hq
    _ = _ := by
      simp only [cubeL2, average, smul_eq_mul, Real.sqrt_mul hq]
      calc
        _ = (Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹))^2 *
            (Real.sqrt (∑ u, ‖f u‖^2) * Real.sqrt (∑ u, ‖g u‖^2)) := by
          rw [Real.sq_sqrt hq]
        _ = _ := by ring

def dualPairing {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) : ℝ :=
  average (fun u => g u (f u))

theorem dualPairing_bound {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) :
    |dualPairing f g| ≤ cubeL2 X f * cubeL2 (X →L[ℝ] ℝ) g := by
  calc
    _ ≤ average (fun u => |g u (f u)|) := by
      simpa only [dualPairing, Real.norm_eq_abs] using norm_average_le (fun u => g u (f u))
    _ ≤ average (fun u => ‖f u‖ * ‖g u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun u _ => by
        simpa only [Real.norm_eq_abs, mul_comm] using (g u).le_opNorm (f u))
    _ ≤ _ := average_norm_mul_le f g

omit [NormedSpace ℝ X] in
theorem cubeL2_norms {n : ℕ} (f : Cube n → X) :
    cubeL2 ℝ (fun u => ‖f u‖) = cubeL2 X f := by simp [cubeL2]

theorem exists_dualPairing_norming {n : ℕ} (f : Cube n → X) :
    ∃ g : Cube n → (X →L[ℝ] ℝ), cubeL2 (X →L[ℝ] ℝ) g ≤ 1 ∧
      dualPairing f g = cubeL2 X f := by
  by_cases hz : cubeL2 X f = 0
  · exact ⟨fun _ => 0, by simp [cubeL2_const], by simp [dualPairing, average, hz]⟩
  have hp : 0 < cubeL2 X f := lt_of_le_of_ne (cubeL2_nonneg f) (Ne.symm hz)
  choose g hg he0 using (fun u => exists_dual_vector'' ℝ (f u))
  have he : ∀ u, g u (f u) = ‖f u‖ := by intro u; exact_mod_cast he0 u
  let y := fun u => ((cubeL2 X f)⁻¹ * ‖f u‖) • g u
  refine ⟨y, ?_, ?_⟩
  · have h := cubeL2_mono (f := y) (g := fun u => (cubeL2 X f)⁻¹ • ‖f u‖) (fun u => by
      dsimp [y]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (hg u))
    change cubeL2 (X →L[ℝ] ℝ) y ≤
      cubeL2 ℝ (fun u => (cubeL2 X f)⁻¹ • ‖f u‖) at h
    rw [cubeL2_smul, cubeL2_norms, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz] at h
    exact h
  · calc
      dualPairing f y = (cubeL2 X f)⁻¹ * average (fun u => ‖f u‖ ^ 2) := by
        simp only [dualPairing, y, smul_apply, smul_eq_mul, he,
          average, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = cubeL2 X f := by rw [← cubeL2_sq]; field_simp

def walshBilinear {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) : ℝ :=
  average (fun u => average (fun v => character v u * g v (T (f u))))

theorem walshBilinear_eq_pairing {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) :
    walshBilinear T f g = dualPairing (operatorWalsh T f) g := by
  rw [walshBilinear, average_comm]
  simp [dualPairing, operatorWalsh, vectorWalsh, average]

theorem walshBilinear_bound {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) :
    |walshBilinear T f g| ≤ walshNorm n T * cubeL2 X f * cubeL2 (Y →L[ℝ] ℝ) g := by
  rw [walshBilinear_eq_pairing]
  exact (dualPairing_bound _ _).trans
    (mul_le_mul_of_nonneg_right (operatorWalsh_le_walshNorm T f) (cubeL2_nonneg g))

def walshBilinearOutputs (n : ℕ) (T : X →L[ℝ] Y) : Set ℝ :=
  {r | ∃ f : Cube n → X, ∃ g : Cube n → (Y →L[ℝ] ℝ),
    cubeL2 X f ≤ 1 ∧ cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 ∧ |walshBilinear T f g| = r}

theorem walshBilinearOutputs_zero (n : ℕ) (T : X →L[ℝ] Y) :
    0 ∈ walshBilinearOutputs n T := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_⟩ <;>
    simp [cubeL2_const, walshBilinear, average]

theorem walshBilinear_unit_bound {n : ℕ} (T : X →L[ℝ] Y)
    {f : Cube n → X} {g : Cube n → (Y →L[ℝ] ℝ)}
    (hf : cubeL2 X f ≤ 1) (hg : cubeL2 (Y →L[ℝ] ℝ) g ≤ 1) :
    |walshBilinear T f g| ≤ walshNorm n T := by
  have h := walshBilinear_bound T f g
  have hfg : cubeL2 X f * cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 :=
    (mul_le_mul hf hg (cubeL2_nonneg g) (by positivity)).trans_eq (one_mul 1)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hfg (walshNorm_nonneg n T)])

theorem walshNorm_eq_bilinear (n : ℕ) (T : X →L[ℝ] Y) :
    walshNorm n T = sSup (walshBilinearOutputs n T) := by
  have hb : BddAbove (walshBilinearOutputs n T) := by
    refine ⟨walshNorm n T, ?_⟩
    rintro r ⟨f, g, hf, hg, rfl⟩
    exact walshBilinear_unit_bound T hf hg
  apply le_antisymm
  · apply csSup_le ⟨0, walshOutputs_zero n T⟩
    rintro r ⟨f, hf, rfl⟩
    obtain ⟨g, hg, he⟩ := exists_dualPairing_norming (operatorWalsh T f)
    apply le_csSup hb
    exact ⟨f, g, hf, hg, by rw [walshBilinear_eq_pairing, he, abs_of_nonneg (cubeL2_nonneg _)]⟩
  · apply csSup_le ⟨0, walshBilinearOutputs_zero n T⟩
    rintro r ⟨f, g, hf, hg, rfl⟩
    exact walshBilinear_unit_bound T hf hg

theorem exists_walshBilinear_half (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ f : Cube n → X, ∃ g : Cube n → (Y →L[ℝ] ℝ),
      cubeL2 X f ≤ 1 ∧ cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 ∧
      walshNorm n T / 2 < walshBilinear T f g ∧ 0 < walshBilinear T f g := by
  have hp := walshNorm_pos n hT
  have hf : ∃ f : Cube n → X, cubeL2 X f ≤ 1 ∧
      walshNorm n T / 2 < cubeL2 Y (operatorWalsh T f) := by
    by_contra hn
    push Not at hn
    have h : walshNorm n T ≤ walshNorm n T / 2 := by
      apply csSup_le ⟨0, walshOutputs_zero n T⟩
      rintro r ⟨f, hf, rfl⟩
      exact hn f hf
    linarith
  obtain ⟨f, hf, hh⟩ := hf
  obtain ⟨g, hg, he⟩ := exists_dualPairing_norming (operatorWalsh T f)
  refine ⟨f, g, hf, hg, ?_, ?_⟩ <;> rw [walshBilinear_eq_pairing, he] <;> linarith

end Cotype

end

end OAI
