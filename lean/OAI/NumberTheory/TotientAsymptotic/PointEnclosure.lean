import OAI.NumberTheory.TotientAsymptotic.BasicCube

namespace OAI

/-! The same box enclosure applies to completed continuous witness regions. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma point_cube_full_enclosure {x : ℝ} {N : ℕ} (hN : N < m x)
    (hBr : 1 ≤ B x*rho^(m x)) {u v : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hdist : ∀ i, |u i-v i| ≤ 1)
    (hlower : ∀ i, 1 ≤ rho^(m x-(i.val+1))*v i) :
    v ∈ enlargedSimplex N (B x) (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  have hv (i : Fin N) : 0 ≤ v i := by
    have hp := pow_pos rho_pos (m x-(i.val+1))
    by_contra hn
    have hh := mul_neg_of_pos_of_neg hp (lt_of_not_ge hn)
    linarith [hlower i]
  have herr (i : Fin N) : ((N-i.val : ℕ) : ℝ)^2+1 ≤
      (4*((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1)))*v i := by
    have hi := i.isLt
    have hn : (1 : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
      exact_mod_cast (show 1 ≤ m x-(i.val+1) by omega)
    have hh : ((N-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
      exact_mod_cast (show N-i.val ≤ m x-(i.val+1) by omega)
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (N-i.val) (α := ℝ)) hh 2
    have he := mul_le_mul_of_nonneg_left (hlower i)
      (show 0 ≤ 4*((m x-(i.val+1) : ℕ) : ℝ)^2 by positivity)
    nlinarith
  have htop : (N : ℝ)^2 ≤ (4*(m x : ℝ)^2*rho^(m x))*B x := by
    have hs : (N : ℝ)^2 ≤ (m x : ℝ)^2 := pow_le_pow_left₀
      (Nat.cast_nonneg _) (by exact_mod_cast hN.le) 2
    have he := mul_le_mul_of_nonneg_left hBr (show 0 ≤ 4*(m x : ℝ)^2 by positivity)
    nlinarith
  have hh := enlargedSimplex_cube hu (fun i => xi_bounds x (i.val+1)) hv hdist herr htop
  have h0 := simplexBoxError_eq x 0 4
  simp only [Nat.sub_zero] at h0
  rw [h0]
  simp_rw [simplexBoxError_eq]
  exact hh

end TotientAsymptotic

end

end OAI
