import OAI.Analysis.Cotype.FiniteRankWalsh

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def walshOutputs (n : ℕ) (T : X →L[ℝ] Y) : Set ℝ :=
  {r | ∃ f : Cube n → X, cubeL2 X f ≤ 1 ∧ cubeL2 Y (operatorWalsh T f) = r}

def walshNorm (n : ℕ) (T : X →L[ℝ] Y) : ℝ := sSup (walshOutputs n T)

theorem walshOutputs_zero (n : ℕ) (T : X →L[ℝ] Y) : 0 ∈ walshOutputs n T := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp [operatorWalsh, vectorWalsh, average, cubeL2]

theorem walshOutputs_bddAbove (n : ℕ) (T : X →L[ℝ] Y) : BddAbove (walshOutputs n T) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (operatorWalsh_L2_le T f).trans ((mul_le_mul_of_nonneg_left hf (norm_nonneg T)).trans_eq (mul_one _))

theorem walshNorm_nonneg (n : ℕ) (T : X →L[ℝ] Y) : 0 ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) (walshOutputs_zero n T)

theorem le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) {f : Cube n → X} (hf : cubeL2 X f ≤ 1) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) ⟨f, hf, rfl⟩

theorem walshNorm_le (n : ℕ) (T : X →L[ℝ] Y) : walshNorm n T ≤ ‖T‖ := by
  apply csSup_le ⟨0, walshOutputs_zero n T⟩
  rintro r ⟨f, hf, rfl⟩
  exact (operatorWalsh_L2_le T f).trans ((mul_le_mul_of_nonneg_left hf (norm_nonneg T)).trans_eq (mul_one _))

theorem vectorWalsh_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    vectorWalsh (fun u => a • f u) = fun v => a • vectorWalsh f v := by
  funext v
  simp only [vectorWalsh, average, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem operatorWalsh_smul {n : ℕ} (T : X →L[ℝ] Y) (a : ℝ) (f : Cube n → X) :
    operatorWalsh T (fun u => a • f u) = fun v => a • operatorWalsh T f v := by
  simp only [operatorWalsh, map_smul]
  exact vectorWalsh_smul a _

theorem operatorWalsh_le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T * cubeL2 X f := by
  by_cases hz : cubeL2 X f = 0
  · simpa [hz] using operatorWalsh_L2_le T f
  · have hp : 0 < cubeL2 X f := lt_of_le_of_ne (cubeL2_nonneg f) (Ne.symm hz)
    have hin : cubeL2 X (fun u => (cubeL2 X f)⁻¹ • f u) ≤ 1 := by
      rw [cubeL2_smul, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz]
    have hh := le_walshNorm T hin
    rw [operatorWalsh_smul, cubeL2_smul, abs_of_pos (inv_pos.mpr hp)] at hh
    calc
      _ = ((cubeL2 X f)⁻¹ * cubeL2 Y (operatorWalsh T f)) * cubeL2 X f := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hh hp.le

theorem walshNorm_le_of_bound {n : ℕ} (T : X →L[ℝ] Y) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ f : Cube n → X, cubeL2 Y (operatorWalsh T f) ≤ D * cubeL2 X f) :
    walshNorm n T ≤ D := by
  apply csSup_le ⟨0, walshOutputs_zero n T⟩
  rintro r ⟨f, hf, rfl⟩
  exact (h f).trans ((mul_le_mul_of_nonneg_left hf hD).trans_eq (mul_one D))

theorem walshNorm_lipschitz (n : ℕ) (A B : X →L[ℝ] Y) :
    |walshNorm n A - walshNorm n B| ≤ ‖A-B‖ := by
  have hle (A B : X →L[ℝ] Y) : walshNorm n A ≤ walshNorm n B + ‖A-B‖ := by
    apply csSup_le ⟨0, walshOutputs_zero n A⟩
    rintro r ⟨f, hf, rfl⟩
    have h := (abs_le.mp (operatorWalsh_L2_lipschitz A B f)).2
    have hb := le_walshNorm B hf
    have hmul : ‖A-B‖ * cubeL2 X f ≤ ‖A-B‖ := by
      exact (mul_le_mul_of_nonneg_left hf (norm_nonneg _)).trans_eq (mul_one _)
    linarith
  have hab := hle A B
  have hba := hle B A
  rw [norm_sub_rev] at hba
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem finiteRank_walshNorm_decay (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, walshNorm n T ≤ D * Real.sqrt ((2 : ℝ)⁻¹ ^ n) := by
  obtain ⟨D, hD, h⟩ := finiteRank_Walsh_decay T hT
  exact ⟨D, hD, fun n => walshNorm_le_of_bound T (mul_nonneg hD (Real.sqrt_nonneg _)) (h n)⟩

theorem operatorWalsh_zero_const (T : X →L[ℝ] Y) (x : X) :
    operatorWalsh (n := 0) T (fun _ => x) = fun _ => T x := by
  funext v
  simp [operatorWalsh, vectorWalsh, character, average]

theorem walshNorm_zero (T : X →L[ℝ] Y) : walshNorm 0 T = ‖T‖ := by
  apply (walshNorm_le 0 T).antisymm
  apply T.opNorm_le_bound (walshNorm_nonneg 0 T)
  intro x
  have h := operatorWalsh_le_walshNorm (n := 0) T (fun _ => x)
  simpa only [operatorWalsh_zero_const, cubeL2_const] using h

end Cotype

end

end OAI
