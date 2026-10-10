import OAI.NumberTheory.TwoPoint.Halasz.HalaszClassicalDefect
import OAI.NumberTheory.TwoPoint.Halasz.HalaszIterationConstants
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmallMoment

namespace OAI

/-! The iterated classical Vinogradov mean-value estimate, with an
explicit geometric defect and explicit constants at every finite scale. -/
namespace TwoPointCorrelations

theorem halasz_classical_mean_value : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤k → ∀ n N : ℕ, 1≤N →
    (halaszVinogradovCount ((n+1)*k) k N:ℝ) ≤
      (halaszIterationConstant R₀ k n:ℝ)*(N:ℝ)^(halaszClassicalExponent k n) := by
  obtain ⟨R₀,hstep⟩ := halasz_normalized_classical_step
  refine ⟨R₀,?_⟩
  intro k hk n
  have hk0 : 0<k := by omega
  induction n with
  | zero =>
    intro N hN
    simp only [Nat.zero_add,one_mul,halasz_classical_exponent_zero,
      Real.rpow_natCast,halasz_iteration_constant_zero]
    have hf := (halasz_iteration_base_bounds R₀ k).2.1
    have hnat : halaszVinogradovCount k k N≤halaszIterationBase R₀ k*N^k := by
      calc
        _ ≤ N^k*k.factorial := halasz_vinogradov_diagonal_bound (N := N) (le_refl k)
        _ ≤ N^k*halaszIterationBase R₀ k := Nat.mul_le_mul_left _ hf
        _ = _ := Nat.mul_comm _ _
    exact_mod_cast hnat
  | succ n ih =>
    intro N hN
    by_cases hsmall : N≤halaszIterationThreshold R₀ k
    · have hd := (halasz_classical_defect_bounds hk0 (n+1)).1
      have he : ((2*((n+1+1)*k):ℕ):ℝ)≤
          halaszClassicalExponent k (n+1)+(halaszTotalDegree k:ℝ) := by
        unfold halaszClassicalExponent
        push_cast
        linarith
      have hh := halasz_small_moment (s := (n+1+1)*k) (k := k)
        (K := halaszTotalDegree k) hN hsmall he
      have hB : (halaszIterationThreshold R₀ k)^(halaszTotalDegree k)≤
          halaszIterationConstant R₀ k (n+1) :=
        (halasz_iteration_base_bounds R₀ k).2.2.1.trans
          (halasz_iteration_constant_ge_base R₀ k (n+1))
      exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hB)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · have hlarge : halaszIterationThreshold R₀ k<N := by omega
      obtain ⟨hpow,hsize,hR0,hmany,hkR⟩ := halasz_iteration_scale hk hlarge
      have hs : 0<(n+1)*k := Nat.mul_pos (by omega) hk0
      have he0 : 0≤halaszClassicalExponent k n :=
        (show (0:ℝ)≤k from Nat.cast_nonneg _).trans
          (halasz_classical_exponent_bounds hk0 n).1
      have hh := hstep ((n+1)*k) k N (halaszIterationConstant R₀ k n:ℝ)
        (halaszClassicalExponent k n) hs hk hpow hsize hR0 hmany hkR
        (Nat.cast_nonneg _) he0 (halasz_classical_exponent_bounds hk0 n).2
        (ih (N/halaszRootScale N k+1) (Nat.le_add_left 1 _))
      rw [halasz_classical_exponent_normalization hk0 n] at hh
      rw [show k+(n+1)*k=(n+1+1)*k by ring] at hh
      have hcoef : (halaszIterationConstant R₀ k n:ℝ)*
          (2*(2*(k^2*k)+1)*(k:ℝ)^k*32^(halaszStepExponent ((n+1)*k) k)) ≤
          (halaszIterationConstant R₀ k (n+1):ℝ) := by
        exact_mod_cast halasz_iteration_constant_step R₀ k n
      exact hh.trans (mul_le_mul_of_nonneg_right hcoef
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end TwoPointCorrelations

end OAI
