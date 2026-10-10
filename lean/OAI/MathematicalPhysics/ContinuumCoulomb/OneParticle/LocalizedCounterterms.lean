import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedFourIndex
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialConstantBounds

namespace OAI

/-! The manuscript's actual well-depth counterterms: direct Coulomb sums
divided by the fixed positive onsite well integral. Their diagonal action
cancels the required linear occupancy term exactly. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def localizedOffsiteSum (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) : ℝ :=
  ∑ j, if i = j then 0 else localizedCoulombCoeff freq (u i) (u j)

def localizedCounterterm (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) : ℝ :=
  localizedOffsiteSum freq u i / planarHopping 0

def localizedCountertermBound (freq : ℝ) : ℝ := localizedPotentialBound freq / planarHopping 0

theorem localizedOffsiteSum_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedOffsiteSum freq u i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact localizedCoulombCoeff_nonnegative freq _ _

theorem localizedCounterterm_nonnegative (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    0 ≤ localizedCounterterm freq u i :=
  div_nonneg (localizedOffsiteSum_nonnegative freq u i) (planarHopping_positive 0).le

theorem localizedCountertermBound_nonnegative (freq : ℝ) : 0 ≤ localizedCountertermBound freq :=
  div_nonneg (localizedPotentialBound_nonnegative freq) (planarHopping_positive 0).le

theorem localizedOffsiteSum_bound {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedOffsiteSum freq u i ≤ m * localizedPotentialBound freq := by
  calc
    _ ≤ ∑ _j : Fin m, localizedPotentialBound freq := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact localizedPotentialBound_nonnegative freq
      · exact localizedCoulombCoeff_le hfreq _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem localizedCounterterm_bound {freq : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedCounterterm freq u i ≤ m * localizedCountertermBound freq := by
  exact (div_le_div_of_nonneg_right (localizedOffsiteSum_bound hfreq u i)
    (planarHopping_positive 0).le).trans_eq (by unfold localizedCountertermBound; ring)

theorem localizedCounterterm_diagonal (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    localizedCounterterm freq u i * planarWellMatrix (u i) (u i) (u i) = -localizedOffsiteSum freq u i := by
  rw [planarWellMatrix_hopping, sub_self, norm_zero]
  unfold localizedCounterterm
  field_simp [(planarHopping_positive 0).ne']

theorem exists_uniform_counterterm_scale {freq : ℝ} (hfreq : 0 < freq) (A : ℕ) :
    ∃ E : ℕ, 0 < E ∧ ∀ N : ℝ, 2 ≤ N → ∀ (m : ℕ), (m : ℝ) ≤ N ^ A →
      ∀ (u : Fin m → PlanarPosition) (i : Fin m),
        0 ≤ localizedCounterterm freq u i / N ^ E ∧ localizedCounterterm freq u i / N ^ E ≤ 1 / 2 := by
  obtain ⟨L, hL, hbound⟩ := exists_polynomial_constant_bounds (by norm_num : (0 : ℝ) < 1)
    (localizedCountertermBound freq)
  refine ⟨A + L + 1, by omega, fun N hN m hm u i => ?_⟩
  have hNp : 0 < N := by linarith
  have hb : localizedCounterterm freq u i ≤ N ^ (A + L) := by
    calc
      _ ≤ m * localizedCountertermBound freq := localizedCounterterm_bound hfreq u i
      _ ≤ N ^ A * N ^ L := mul_le_mul hm (hbound N hN).2
        (localizedCountertermBound_nonnegative freq) (pow_nonneg hNp.le A)
      _ = _ := (pow_add _ _ _).symm
  refine ⟨div_nonneg (localizedCounterterm_nonnegative freq u i) (pow_pos hNp _).le, ?_⟩
  apply (div_le_iff₀ (pow_pos hNp _)).mpr
  rw [pow_succ]
  have h := mul_le_mul_of_nonneg_left hN (pow_nonneg hNp.le (A + L))
  nlinarith only [hb, h]

end ContinuumCoulomb

end

end OAI
