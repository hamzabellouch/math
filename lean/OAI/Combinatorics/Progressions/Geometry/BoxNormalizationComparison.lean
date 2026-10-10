import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem root_ratio_comparison {S C V K r : ℝ} (hS : 0 ≤ S) (hC : 0 < C) (hV : 0 < V)
    (hCV : C ≤ V) (hVC : V ≤ K * C) (hK : 1 ≤ K) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (S / V) ^ r ≤ (S / C) ^ r ∧ (S / C) ^ r ≤ K * (S / V) ^ r := by
  constructor
  · exact Real.rpow_le_rpow (div_nonneg hS hV.le)
      (div_le_div_of_nonneg_left hS hC hCV) hr
  · have hratio : S / C ≤ K * (S / V) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hC hV).mpr
      nlinarith [mul_le_mul_of_nonneg_left hVC hS]
    calc
      _ ≤ (K * (S / V)) ^ r := Real.rpow_le_rpow (div_nonneg hS hC.le) hratio hr
      _ = K ^ r * (S / V) ^ r := Real.mul_rpow (by linarith) (div_nonneg hS hV.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hK hr1)
        (Real.rpow_nonneg (div_nonneg hS hV.le) _)

variable {A : Type*} [AddCommGroup A]

noncomputable def volumeGowersNorm (j : ℕ) (Q : Finset A) (f : A → ℂ) : ℝ :=
  ((supportedCubeSum j (Q : Set A) (fun _ ↦ f)).re / (Q.card : ℝ) ^ (j + 1)) ^
    (((2 ^ j : ℕ) : ℝ)⁻¹)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem integerBox_normalization_comparison (a : ι → ℤ) (j : ℕ) (f : (ι → ℤ) → ℂ) :
    volumeGowersNorm (j + 1) (translatedIntegerBox a T) f ≤
      finiteSupportGowersNorm (j + 1) (translatedIntegerBox a T) f ∧
    finiteSupportGowersNorm (j + 1) (translatedIntegerBox a T) f ≤
      (((j + 2 : ℕ) : ℝ) ^ (Fintype.card ι * (j + 2))) *
        volumeGowersNorm (j + 1) (translatedIntegerBox a T) f := by
  let Q := translatedIntegerBox a T
  have hQ := translatedIntegerBox_nonempty T a
  have hφ := translatedIntegerBox_reflectsPairSums T a
  have hN : 0 ≤ finiteSupportGowersNorm (j + 1) Q f := by
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg j _ _
  have hS : 0 ≤ (supportedCubeSum (j + 1) (Q : Set (ι → ℤ)) (fun _ ↦ f)).re := by
    rw [← finiteSupportGowersNorm_pow_mul_count hφ hQ j f]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hN _)
  have hC : (0 : ℝ) < Nat.card (SupportedCube (j + 1) (Q : Set (ι → ℤ))) := by
    exact_mod_cast card_supportedCube_pos (j + 1) hQ
  have hV : (0 : ℝ) < (Q.card : ℝ) ^ (j + 2) :=
    pow_pos (by exact_mod_cast hQ.card_pos) _
  have hCV : (Nat.card (SupportedCube (j + 1) (Q : Set (ι → ℤ))) : ℝ) ≤
      (Q.card : ℝ) ^ (j + 2) := by exact_mod_cast card_supportedCube_le (j + 1) Q
  have hVC : (Q.card : ℝ) ^ (j + 2) ≤
      (((j + 2 : ℕ) : ℝ) ^ (Fintype.card ι * (j + 2))) *
        Nat.card (SupportedCube (j + 1) (Q : Set (ι → ℤ))) := by
    dsimp [Q, translatedIntegerBox]
    rw [card_translateSupport, card_supportedCube_translate]
    exact_mod_cast integerBoxCubeCount_lower T (j + 1)
  have hK : (1 : ℝ) ≤ (((j + 2 : ℕ) : ℝ) ^ (Fintype.card ι * (j + 2))) :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ j + 2 by omega))
  have hp : (1 : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1 ≤ 2))
  exact root_ratio_comparison hS hC hV hCV hVC hK (by positivity)
    ((inv_le_one₀ (by positivity)).mpr hp)

end Erdos3

end

end OAI
