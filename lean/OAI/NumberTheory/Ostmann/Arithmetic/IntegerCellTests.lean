import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellReplacement

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.IntegerCell
open scoped BigOperators
open Set

theorem sum_integerDensityMass (M : ℕ) [NeZero M] (lo hi G : ℝ) (φ : ℝ → ℝ) :
    (∑ _r : ZMod M, integerDensityMass M lo hi G φ) =
      ∫ t in lo..hi, Real.exp (t-G)*φ (t-G) := by
  simp only [integerDensityMass, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne M))

theorem integerResidueMass_nonneg (N M : ℕ) (a : ZMod M) (lo hi G : ℝ)
    (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t) :
    0 ≤ integerResidueMass N M a lo hi G φ := by
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (Real.exp_pos (-G)).le (hφ _))

theorem sum_weighted_residueTest {M : ℕ} [NeZero M] {R : Type*} [Semiring R]
    (S : Finset ℕ) (w : ℕ → R) (F : ZMod M → R) :
    (∑ n ∈ S, w n*F (n : ZMod M)) =
      ∑ r : ZMod M, (∑ n ∈ S.filter (fun n : ℕ => (n : ZMod M) = r), w n)*F r := by
  classical
  symm
  simp_rw [Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp

def cellSupport (N : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun n => 0 < n ∧ lo ≤ Real.log n ∧ Real.log n ≤ hi

theorem integerSupport_eq_filter (N M : ℕ) (a : ZMod M) (lo hi : ℝ) :
    integerSupport N M a lo hi = (cellSupport N lo hi).filter (fun n : ℕ => (n : ZMod M) = a) := by
  ext n
  simp only [integerSupport, cellSupport, Finset.mem_filter]
  tauto

def complexTestSum (N M : ℕ) [NeZero M] (lo hi G : ℝ) (φ : ℝ → ℝ)
    (F : ZMod M → ℂ) : ℂ :=
  ∑ n ∈ cellSupport N lo hi, ((Real.exp (-G)*φ (Real.log n-G) : ℝ) : ℂ)*F (n : ZMod M)

theorem complexTestSum_eq (N M : ℕ) [NeZero M] (lo hi G : ℝ) (φ : ℝ → ℝ)
    (F : ZMod M → ℂ) :
    complexTestSum N M lo hi G φ F =
      ∑ r : ZMod M, (integerResidueMass N M r lo hi G φ : ℂ)*F r := by
  unfold complexTestSum
  rw [sum_weighted_residueTest]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [integerResidueMass, integerSupport_eq_filter, Complex.ofReal_sum]

theorem complexTestSum_error (N M : ℕ) [NeZero M] (φ ψ : ℝ → ℝ)
    (G lo hi B D : ℝ) (hlohi : lo ≤ hi) (hN : ⌊Real.exp hi⌋₊ ≤ N)
    (hφ : ∀ t, HasDerivAt φ (ψ t) t) (hψ : Continuous ψ)
    (hB : ∀ t ∈ Icc lo hi, |φ (t-G)| ≤ B)
    (hD : ∀ t ∈ Icc lo hi, |ψ (t-G)| ≤ D) (F : ZMod M → ℂ) :
    ‖complexTestSum N M lo hi G φ F-
      (integerDensityMass M lo hi G φ : ℂ)*(∑ r : ZMod M, F r)‖ ≤
      Real.exp (-G)*(5*B+2*D*(hi-lo))*(∑ r : ZMod M, ‖F r‖) := by
  have he : complexTestSum N M lo hi G φ F-
      (integerDensityMass M lo hi G φ : ℂ)*(∑ r : ZMod M, F r) =
      ∑ r : ZMod M, ((integerResidueMass N M r lo hi G φ-
        integerDensityMass M lo hi G φ : ℝ) : ℂ)*F r := by
    rw [complexTestSum_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Complex.ofReal_sub, sub_mul]
  rw [he]
  calc
    _ ≤ ∑ r : ZMod M, ‖((integerResidueMass N M r lo hi G φ-
        integerDensityMass M lo hi G φ : ℝ) : ℂ)*F r‖ := norm_sum_le _ _
    _ ≤ ∑ r : ZMod M, (Real.exp (-G)*(5*B+2*D*(hi-lo)))*‖F r‖ := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (integerResidueMass_error N M r φ ψ G lo hi B D hlohi hN hφ hψ hB hD) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Ostmann.Arithmetic.IntegerCell
end

end OAI
