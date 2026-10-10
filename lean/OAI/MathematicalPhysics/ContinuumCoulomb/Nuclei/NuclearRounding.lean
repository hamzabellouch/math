import OAI.Analysis.CoulombRadii.FormDomain.Add

namespace OAI

/-!
# Stability under rounding a nuclear position

Translated Hardy estimates uniformly control rational rounding on arbitrary
form-domain states. The constant eight permits a pointwise kernel inequality
also at the poles, using Lean's convention `0⁻¹ = 0`, and suffices for the
polynomial precision budget.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

/-- Pointwise control valid even where an inverse distance is totalized to zero. -/
theorem coulomb_kernel_shift_bound (x a b : Coulomb.Space) :
    |Coulomb.coulombKernel (x - a) - Coulomb.coulombKernel (x - b)| ≤
      ‖a - b‖ * (Coulomb.coulombKernel (x - a) ^ 2 +
        Coulomb.coulombKernel (x - b) ^ 2) := by
  unfold Coulomb.coulombKernel
  by_cases ha : x = a
  · subst x
    by_cases hab : a = b
    · simp [hab]
    · have hn : ‖a - b‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab)
      simp only [sub_self, norm_zero, inv_zero, zero_sub, abs_neg,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), zero_pow (by decide : 2 ≠ 0),
        zero_add]
      rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  by_cases hb : x = b
  · subst x
    have hn : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr ha)
    simp only [sub_self, norm_zero, inv_zero, sub_zero,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), zero_pow (by decide : 2 ≠ 0),
      add_zero]
    rw [norm_sub_rev a b, pow_two, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  have hr : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hs : 0 < ‖x - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  have hd : |‖x - a‖ - ‖x - b‖| ≤ ‖a - b‖ := by
    have h := abs_norm_sub_norm_le (x - a) (x - b)
    have heq : (x - a) - (x - b) = b - a := by abel
    simpa only [heq, norm_sub_rev b a] using h
  have heq : ‖x - a‖⁻¹ - ‖x - b‖⁻¹ =
      (‖x - b‖ - ‖x - a‖) / (‖x - a‖ * ‖x - b‖) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hr hs), abs_sub_comm]
  calc
    |‖x - a‖ - ‖x - b‖| / (‖x - a‖ * ‖x - b‖) ≤
        ‖a - b‖ / (‖x - a‖ * ‖x - b‖) :=
      div_le_div_of_nonneg_right hd (mul_nonneg hr.le hs.le)
    _ = ‖a - b‖ * (‖x - a‖⁻¹ * ‖x - b‖⁻¹) := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ‖a - b‖ * (‖x - a‖⁻¹ ^ 2 + ‖x - b‖⁻¹ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      nlinarith [sq_nonneg (‖x - a‖⁻¹ - ‖x - b‖⁻¹), sq_nonneg ‖x - a‖⁻¹,
        sq_nonneg ‖x - b‖⁻¹]

/-- Translated Hardy as a bound for the square of the physical Coulomb kernel. -/
theorem nuclear_hardy_square {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i : Fin n) (a : Coulomb.Space) :
    Integrable (fun x => Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
      ‖state.value spin x‖ ^ 2) ∧
    (∫ x, Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
      ‖state.value spin x‖ ^ 2) ≤
      4 * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  have h := state.hardy spin i (Coulomb.nuclearHardyCoordinates i a)
  simpa only [← Coulomb.hardyCoulomb_sq,
    Coulomb.hardyCoulomb_nuclear] using h

/-- An actual form-domain estimate on every spin component, uniform in both
nuclear positions and without a separation condition. -/
theorem nuclear_position_rounding_bound {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i : Fin n) (a b : Coulomb.Space) :
    |∫ x, (Coulomb.coulombKernel (Coulomb.position x i - a) -
      Coulomb.coulombKernel (Coulomb.position x i - b)) * ‖state.value spin x‖ ^ 2| ≤
      8 * ‖a - b‖ * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  obtain ⟨hia, hba⟩ := nuclear_hardy_square state spin i a
  obtain ⟨hib, hbb⟩ := nuclear_hardy_square state spin i b
  have hI : Integrable (fun x =>
      ‖a - b‖ * (Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2 +
      Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2)) := (hia.add hib).const_mul _
  have hdiff : Integrable (fun x =>
      (Coulomb.coulombKernel (Coulomb.position x i - a) -
        Coulomb.coulombKernel (Coulomb.position x i - b)) *
          ‖state.value spin x‖ ^ 2) := by
    simp only [sub_mul]
    exact (state.nuclear_coulomb_integrable_bound spin i a (by norm_num : (0 : ℝ) < 1)).1.sub
      (state.nuclear_coulomb_integrable_bound spin i b (by norm_num : (0 : ℝ) < 1)).1
  have hp : ∀ x,
      |(Coulomb.coulombKernel (Coulomb.position x i - a) -
        Coulomb.coulombKernel (Coulomb.position x i - b)) * ‖state.value spin x‖ ^ 2| ≤
      ‖a - b‖ * (Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2 +
      Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2) := by
    intro x
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖state.value spin x‖)]
    have h := mul_le_mul_of_nonneg_right
      (coulomb_kernel_shift_bound (Coulomb.position x i) a b)
      (sq_nonneg ‖state.value spin x‖)
    simpa only [add_mul, mul_assoc] using h
  calc
    _ ≤ ∫ x, |(Coulomb.coulombKernel (Coulomb.position x i - a) -
        Coulomb.coulombKernel (Coulomb.position x i - b)) * ‖state.value spin x‖ ^ 2| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖a - b‖ * (Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2 +
      Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2) := integral_mono hdiff.abs hI hp
    _ = ‖a - b‖ * ((∫ x, Coulomb.coulombKernel (Coulomb.position x i - a) ^ 2 *
        ‖state.value spin x‖ ^ 2) +
      ∫ x, Coulomb.coulombKernel (Coulomb.position x i - b) ^ 2 *
        ‖state.value spin x‖ ^ 2) := by
      rw [integral_const_mul, integral_add hia hib]
    _ ≤ 8 * ‖a - b‖ * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hba hbb) (norm_nonneg (a - b))
      nlinarith

/-- Rounding all equal-charge nuclei is controlled on every many-electron
spinful H¹ vector. `charge = 1 / λ` gives the dilated unit-nucleus estimate.
The total mass factor is explicit, including the large slab volume. -/
theorem all_nuclei_rounding_bound {n m : ℕ} (state : Coulomb.H1Vector n)
    (oldPosition newPosition : Fin m → Coulomb.Space) {delta charge : ℝ}
    (hcharge : 0 ≤ charge)
    (hmove : ∀ a, ‖oldPosition a - newPosition a‖ ≤ delta) :
    |charge * ∑ spin : Coulomb.Spins n, ∑ i : Fin n, ∑ a : Fin m,
      ∫ x, (Coulomb.coulombKernel (Coulomb.position x i - oldPosition a) -
        Coulomb.coulombKernel (Coulomb.position x i - newPosition a)) *
          ‖state.value spin x‖ ^ 2| ≤
      16 * charge * (m : ℝ) * delta * Coulomb.kinetic state := by
  let F := fun (spin : Coulomb.Spins n) (i : Fin n) (a : Fin m) =>
    ∫ x, (Coulomb.coulombKernel (Coulomb.position x i - oldPosition a) -
      Coulomb.coulombKernel (Coulomb.position x i - newPosition a)) *
        ‖state.value spin x‖ ^ 2
  let G := fun (spin : Coulomb.Spins n) (i : Fin n) =>
    ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2
  have hG : ∀ spin i, 0 ≤ G spin i := by
    intro spin i
    exact Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hF : ∀ spin i a, |F spin i a| ≤ 8 * delta * G spin i := by
    intro spin i a
    have h := nuclear_position_rounding_bound state spin i (oldPosition a) (newPosition a)
    change |F spin i a| ≤ 8 * ‖oldPosition a - newPosition a‖ * G spin i at h
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmove a) (by norm_num)) (hG spin i)
  have hsum : |∑ spin : Coulomb.Spins n, ∑ i : Fin n, ∑ a : Fin m, F spin i a| ≤
      ∑ spin : Coulomb.Spins n, ∑ i : Fin n, ∑ _a : Fin m, 8 * delta * G spin i := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro spin _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun a _ => hF spin i a)
  have htotal : (∑ spin : Coulomb.Spins n, ∑ i : Fin n, ∑ _a : Fin m,
      8 * delta * G spin i) = 16 * (m : ℝ) * delta * Coulomb.kinetic state := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold Coulomb.kinetic G
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
    ring
  have h := mul_le_mul_of_nonneg_left (hsum.trans_eq htotal) hcharge
  change |charge * ∑ spin, ∑ i, ∑ a, F spin i a| ≤ _
  rw [abs_mul, abs_of_nonneg hcharge]
  convert h using 1
  ring

end ContinuumCoulomb

end

end OAI
