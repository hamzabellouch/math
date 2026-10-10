import OAI.MeasureTheory.Falconer.Geometry.IntegerSumEnergy
import OAI.MeasureTheory.Falconer.Estimates.PathDifferenceBound

namespace OAI

/-! A quantitative balanced additive-energy refinement on the integer
lattice, proved by popular sums and the four-path argument. -/
namespace Falconer
open scoped Pointwise

theorem integer_energy_refinement (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcard : A.card = B.card) {K : ℝ} (hK : 1 ≤ K)
    (henergy : (A.card : ℝ)^3 ≤ K*(Finset.addEnergy A B : ℝ)) :
    ∃ G ⊆ B, (B.card : ℝ)/(8*K) ≤ (G.card : ℝ) ∧
      ((G-G).card : ℝ) ≤ 2097152*K^9*(B.card : ℝ) := by
  let N : ℝ := A.card
  have hN : 0 < N := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hBN : (B.card : ℝ) = N := by
    change (B.card : ℝ) = (A.card : ℝ)
    exact_mod_cast hcard.symm
  have hK0 : 0 < K := by linarith
  let w := integerSumMultiplicity A B
  let θ : ℝ := N/(2*K)
  let C := (A+B).filter fun z => θ ≤ w z
  have htotal : (∑ z ∈ A+B, w z) ≤ N^2 := by
    rw [integerSumMultiplicity_total,hBN]
    exact (pow_two N).symm.le
  have hE : N^3/K ≤ ∑ z ∈ A+B, (w z)^2 := by
    rw [integerSumMultiplicity_energy]
    apply (div_le_iff₀ hK0).2
    simpa only [mul_comm] using henergy
  have h2K : 0 < 2*K := mul_pos (by norm_num) hK0
  have hθ : 0 ≤ θ := (div_pos hN h2K).le
  have hp := popular_square_mass (A+B) w hθ hN.le
    (fun z _ => ⟨integerSumMultiplicity_nonneg A B z,integerSumMultiplicity_le_left A B z⟩)
    htotal hE
  have hC : (C.card : ℝ) ≤ 2*K*N := by
    have hb := mul_le_mul_of_nonneg_left hp.1 h2K.le
    have he : (2*K)*(θ*(C.card : ℝ)) = N*(C.card : ℝ) := by
      change (2*K)*((N/(2*K))*(C.card : ℝ)) = N*(C.card : ℝ)
      rw [← mul_assoc,mul_div_cancel₀ N h2K.ne']
    change (2*K)*(θ*(C.card : ℝ)) ≤ (2*K)*N^2 at hb
    rw [he] at hb
    apply (mul_le_mul_iff_left₀ hN).1
    nlinarith
  have hsum : N^2/(2*K) ≤ ∑ z ∈ C, w z := by
    have hb := mul_le_mul_of_nonneg_left hp.2 h2K.le
    have he : (2*K)*(N^3/K-θ*N^2) = N^3 := by
      change (2*K)*(N^3/K-N/(2*K)*N^2) = N^3
      field_simp
      ring
    change (2*K)*(N^3/K-θ*N^2) ≤ (2*K)*(N*∑ z ∈ C, w z) at hb
    rw [he] at hb
    apply (div_le_iff₀ h2K).2
    apply (mul_le_mul_iff_left₀ hN).1
    nlinarith
  let ρ : ℝ := 1/(2*K)
  let L : ℝ := ρ^2*N/32
  have hρ : 0 < ρ := div_pos zero_lt_one h2K
  have hL : 0 < L := div_pos (mul_pos (sq_pos_of_pos hρ) hN) (by norm_num)
  have hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B (fun a b => a+b ∈ C) a).card : ℝ) := by
    rw [← integerSumMultiplicity_restrict,hBN]
    have he : ρ*(A.card : ℝ)*N = N^2/(2*K) := by dsimp [ρ,N]; ring
    rw [he]
    exact hsum
  obtain ⟨G,hGB,hG,hD⟩ := integer_dense_small_difference A B C (fun a b => a+b ∈ C)
    hA hB hρ hL.le (le_refl L) hdense (fun _ _ _ _ h => h)
  have hGlower : (B.card : ℝ)/(8*K) ≤ (G.card : ℝ) := by
    have he : ρ*(B.card : ℝ)/4 = (B.card : ℝ)/(8*K) := by dsimp [ρ]; ring
    rwa [he] at hG
  let k : ℝ := (ρ*N/4)*L^2
  have hk : 0 < k := mul_pos (div_pos (mul_pos hρ hN) (by norm_num)) (sq_pos_of_pos hL)
  have hD' : ((G-G).card : ℝ)*k ≤ (C.card : ℝ)^4 := by
    simpa only [hBN] using hD
  have hc4 : (C.card : ℝ)^4 ≤ (2*K*N)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hC 4
  have hDbound : ((G-G).card : ℝ) ≤ (2*K*N)^4/k :=
    (le_div_iff₀ hk).2 (hD'.trans hc4)
  have he : (2*K*N)^4/k = 2097152*K^9*N := by
    dsimp [k,L,ρ]
    field_simp
    ring
  rw [he,← hBN] at hDbound
  exact ⟨G,hGB,hGlower,hDbound⟩

end Falconer

end OAI
