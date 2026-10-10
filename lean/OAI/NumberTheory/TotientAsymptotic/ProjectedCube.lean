import OAI.NumberTheory.TotientAsymptotic.BasicCube

namespace OAI

/-! Unit-box enclosure for a projected banded simplex. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem projected_prime_box_enclosure {x : ℝ} {K : ℕ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(K : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam)
    (hL : 0 < R x K) {u v : Fin (R x K) → ℝ}
    (hu : u ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hband : ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ u i)
    (hdist : ∀ i, |u i-v i| ≤ 1) :
    v ∈ enlargedSimplex (R x K) (B x)
      (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  have hPm : K ≤ m x := by unfold R at hL; omega
  have hP : 1 ≤ K := by
    by_contra hn
    have : K=0 := by omega
    simp only [this, Nat.cast_zero, mul_zero] at hcut
    norm_num at hcut
  have hlower (i : Fin (R x K)) : 1 ≤ rho^(m x-(i.val+1))*v i := by
    apply cube_band_lower hs hcut
    · have := i.isLt; unfold R at this; omega
    · exact hband i
    · exact hdist i
  have hv (i : Fin (R x K)) : 0 ≤ v i := by
    have hp := pow_pos rho_pos (m x-(i.val+1))
    have hh := hlower i
    by_contra hn
    have : rho^(m x-(i.val+1))*v i < 0 := mul_neg_of_pos_of_neg hp (lt_of_not_ge hn)
    linarith
  have herr (i : Fin (R x K)) :
      ((R x K-i.val : ℕ) : ℝ)^2+1 ≤
        (4*((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1)))*v i := by
    have hi := i.isLt
    have hn : 1 ≤ m x-(i.val+1) := by unfold R at hi; omega
    have hnR : (1 : ℝ) ≤ (m x-(i.val+1) : ℕ) := by exact_mod_cast hn
    have hh : ((R x K-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
      exact_mod_cast (show R x K-i.val ≤ m x-(i.val+1) by unfold R; omega)
    have hsq : ((R x K-i.val : ℕ) : ℝ)^2 ≤ ((m x-(i.val+1) : ℕ) : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hh 2
    have he := mul_le_mul_of_nonneg_left (hlower i)
      (show 0 ≤ 4*((m x-(i.val+1) : ℕ) : ℝ)^2 by positivity)
    nlinarith
  have htop : (R x K : ℝ)^2 ≤ (4*(m x : ℝ)^2*rho^(m x))*B x := by
    have hmP : (K : ℝ) ≤ m x := by exact_mod_cast hPm
    have hm4 : 4 ≤ lam*(m x : ℝ) := hcut.trans (mul_le_mul_of_nonneg_left hmP lam_pos.le)
    have hx := (div_le_div_iff₀ (mul_pos hB (pow_pos rho_pos _)) lam_pos).mp hscale
    have h1 : 1 ≤ B x*rho^(m x) := by nlinarith
    have hsq : (R x K : ℝ)^2 ≤ (m x : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le (m x) (K)) 2
    have he := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4*(m x : ℝ)^2 by positivity)
    nlinarith
  have hh := enlargedSimplex_cube hu
    (fun i => xi_bounds x (i.val+1)) hv hdist herr htop
  have h0 := simplexBoxError_eq x 0 4
  simp only [Nat.sub_zero] at h0
  rw [h0]
  simp_rw [simplexBoxError_eq]
  exact hh


end TotientAsymptotic

end

end OAI
