import OAI.NumberTheory.JointDickman.Probability.CutNormTriangle

namespace OAI

/-! # Variation of the finite cut norm under parameter changes -/
namespace JointDickman
open Finset Classical

theorem kernelCutNorm_difference_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K J : ι → ι → ℝ) :
    |kernelCutNorm K-kernelCutNorm J| ≤ kernelAbsoluteMass (fun i k => K i k-J i k) := by
  have h₁ : kernelCutNorm K ≤ kernelCutNorm (fun i k => K i k-J i k)+kernelCutNorm J := by
    convert kernelCutNorm_add (fun i k => K i k-J i k) J using 1
    congr 1
    funext i k
    ring
  have h₂ : kernelCutNorm J ≤ kernelCutNorm (fun i k => J i k-K i k)+kernelCutNorm K := by
    convert kernelCutNorm_add (fun i k => J i k-K i k) K using 1
    congr 1
    funext i k
    ring
  have hb₁ := kernelCutNorm_le_absolute_mass (fun i k => K i k-J i k)
  have hb₂ := kernelCutNorm_le_absolute_mass (fun i k => J i k-K i k)
  have he : kernelAbsoluteMass (fun i k => J i k-K i k) =
      kernelAbsoluteMass (fun i k => K i k-J i k) := by
    simp only [kernelAbsoluteMass,abs_sub_comm]
  rw [he] at hb₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem kernelCutNorm_parameter_bound {M : ℕ} (hM : 0 < M)
    (K J : Fin M → Fin M → ℝ) {C : ℝ}
    (hentry : ∀ i k, |K i k-J i k| ≤ C) :
    |kernelCutNorm K-kernelCutNorm J| ≤ (M : ℝ)*C := by
  apply (kernelCutNorm_difference_bound K J).trans
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold kernelAbsoluteMass
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ hMr).mpr
  calc
    _ ≤ ∑ _i : Fin M, ∑ _k : Fin M, C :=
      sum_le_sum (fun i _ => sum_le_sum (fun k _ => hentry i k))
    _ = _ := by simp; ring

theorem kernelAbsoluteMass_entry_bound {M : ℕ} (hM : 0 < M)
    (K : Fin M → Fin M → ℝ) {C : ℝ} (hentry : ∀ i k, |K i k| ≤ C) :
    kernelAbsoluteMass K ≤ (M : ℝ)*C := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold kernelAbsoluteMass
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ hMr).mpr
  exact (sum_le_sum (fun i _ => sum_le_sum (fun k _ => hentry i k))).trans_eq (by simp; ring)

theorem kernel_error_parameter_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K K' J J' : ι → ι → ℝ) {A B : ℝ}
    (hK : kernelAbsoluteMass (fun i k => K i k-K' i k) ≤ A)
    (hJ : kernelAbsoluteMass (fun i k => J i k-J' i k) ≤ B) :
    |kernelCutNorm (fun i k => K i k-J i k)-kernelCutNorm (fun i k => K' i k-J' i k)| ≤ A+B := by
  apply (kernelCutNorm_difference_bound _ _).trans
  apply le_trans _ (add_le_add hK hJ)
  unfold kernelAbsoluteMass
  rw [← add_div,← sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro i _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  convert abs_sub (K i k-K' i k) (J i k-J' i k) using 1
  congr 1
  ring

end JointDickman

end OAI
