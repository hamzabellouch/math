import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model

namespace OAI

/-!
# Coulomb repulsion as a form-domain to L² multiplier

Both continuum comparisons need control of the repulsion applied to a
localized many-electron vector, including its mixed block with the continuum
complement. Translated pair Hardy and finite Cauchy--Schwarz prove a bound on
the actual full repulsion, without summing over an exponentially large spin
operator matrix.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def pairRepulsionTerm {n : ℕ} (p : Fin n × Fin n) (x : Configuration n) : ℝ :=
  if p.1 < p.2 then Coulomb.coulombKernel (Coulomb.position x p.1 - Coulomb.position x p.2)
    else 0

def repulsionPotential {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ p : Fin n × Fin n, pairRepulsionTerm p x

theorem pair_hardy_square {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) (i j : Fin n) (hne : i ≠ j) :
    Integrable (fun x => Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) ^ 2 *
      ‖state.value spin x‖ ^ 2) ∧
    (∫ x, Coulomb.coulombKernel (Coulomb.position x i - Coulomb.position x j) ^ 2 *
      ‖state.value spin x‖ ^ 2) ≤
      4 * ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  simpa only [← Coulomb.hardyCoulomb_sq, Coulomb.hardyCoulomb_pair] using
    state.hardy spin i (Coulomb.pairHardyCoordinates i j hne)

theorem repulsionPotential_measurable (n : ℕ) :
    Measurable (@repulsionPotential n) := by
  unfold repulsionPotential
  apply Finset.measurable_sum
  intro p _
  change Measurable (fun x => pairRepulsionTerm p x)
  by_cases hp : p.1 < p.2
  · have h := Coulomb.measurable_hardyCoulomb p.1
      (Coulomb.pairHardyCoordinates p.1 p.2 hp.ne)
    change Measurable (fun x =>
      Coulomb.hardyCoulomb p.1 (Coulomb.pairHardyCoordinates p.1 p.2 hp.ne) x) at h
    simpa only [pairRepulsionTerm, ite_eq_left hp, Coulomb.hardyCoulomb_pair] using h
  · simp only [pairRepulsionTerm, ite_eq_right hp]
    exact measurable_const

theorem repulsionPotential_square_bound {n : ℕ} (x : Configuration n) :
    repulsionPotential x ^ 2 ≤ (n : ℝ) ^ 2 *
      ∑ p : Fin n × Fin n, pairRepulsionTerm p x ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => pairRepulsionTerm p x) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul] at h
  change (∑ p, pairRepulsionTerm p x) ^ 2 ≤ _
  nlinarith [h]

theorem repulsionPotential_spin_L2_bound {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) :
    Integrable (fun x => repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) ∧
    (∫ x, repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) ≤
      4 * (n : ℝ) ^ 3 * ∑ i, ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 := by
  let G : Fin n → ℝ := fun i => ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2
  have hG (i : Fin n) : 0 ≤ G i :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hterm (p : Fin n × Fin n) :
      Integrable (fun x => pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2) ∧
      (∫ x, pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2) ≤ 4 * G p.1 := by
    by_cases hp : p.1 < p.2
    · simpa only [pairRepulsionTerm, ite_eq_left hp, G] using
        pair_hardy_square state spin p.1 p.2 hp.ne
    · simp only [pairRepulsionTerm, ite_eq_right hp, zero_pow (by decide : 2 ≠ 0),
        zero_mul, integral_zero]
      exact ⟨integrable_zero _ _ _, by positivity⟩
  let majorant : Configuration n → ℝ := fun x =>
    (n : ℝ) ^ 2 * ∑ p : Fin n × Fin n, pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2
  have hmajorant : Integrable majorant :=
    (integrable_finsetSum _ (fun p _ => (hterm p).1)).const_mul _
  have hdom (x : Configuration n) :
      repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2 ≤ majorant x := by
    have h := mul_le_mul_of_nonneg_right (repulsionPotential_square_bound x)
      (sq_nonneg ‖state.value spin x‖)
    simpa only [majorant, Finset.sum_mul, mul_assoc] using h
  have hmeas : AEStronglyMeasurable
      (fun x => repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) volume :=
    ((repulsionPotential_measurable n).pow_const 2).aestronglyMeasurable.mul
      ((state.value_L2 spin).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).aestronglyMeasurable
  have hI : Integrable (fun x => repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) := by
    apply hmajorant.mono' hmeas
    exact Filter.Eventually.of_forall fun x => by
      change |repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2| ≤ majorant x
      rw [abs_of_nonneg (by positivity)]
      exact hdom x
  refine ⟨hI, (integral_mono hI hmajorant hdom).trans ?_⟩
  change (∫ x, (n : ℝ) ^ 2 * ∑ p : Fin n × Fin n,
    pairRepulsionTerm p x ^ 2 * ‖state.value spin x‖ ^ 2) ≤ _
  rw [integral_const_mul, integral_finsetSum _ (fun p _ => (hterm p).1)]
  calc
    _ ≤ (n : ℝ) ^ 2 * ∑ p : Fin n × Fin n, 4 * G p.1 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => (hterm p).2) (sq_nonneg _)
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      unfold G
      ring

/-- The full spinful L² multiplication estimate with an explicit polynomial
factor in the electron count. -/
theorem repulsionPotential_L2_bound {n : ℕ} (state : Coulomb.H1Vector n) :
    (∑ spin : Coulomb.Spins n,
      ∫ x, repulsionPotential x ^ 2 * ‖state.value spin x‖ ^ 2) ≤
      8 * (n : ℝ) ^ 3 * Coulomb.kinetic state := by
  calc
    _ ≤ ∑ spin : Coulomb.Spins n, 4 * (n : ℝ) ^ 3 *
        ∑ i, ∑ k : Fin 3, ∫ x, ‖state.gradient spin (i, k) x‖ ^ 2 :=
      Finset.sum_le_sum fun spin _ => (repulsionPotential_spin_L2_bound state spin).2
    _ = _ := by
      unfold Coulomb.kinetic
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
      ring

theorem repulsion_mul_memLp {n : ℕ} (state : Coulomb.H1Vector n)
    (spin : Coulomb.Spins n) :
    MemLp (fun x => (repulsionPotential x : ℂ) * state.value spin x) 2 := by
  have hm : AEStronglyMeasurable
      (fun x => (repulsionPotential x : ℂ) * state.value spin x) volume :=
    (repulsionPotential_measurable n).complex_ofReal.aestronglyMeasurable.mul
      (state.value_L2 spin).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
    (repulsionPotential_spin_L2_bound state spin).1

/-- Equivalently, this controls the squared norm of the actual Coulomb
multiplication operator on every component of a full spinful vector. -/
theorem repulsion_mul_norm_bound {n : ℕ} (state : Coulomb.H1Vector n) :
    (∑ spin : Coulomb.Spins n,
      ∫ x, ‖(repulsionPotential x : ℂ) * state.value spin x‖ ^ 2) ≤
      8 * (n : ℝ) ^ 3 * Coulomb.kinetic state := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
    repulsionPotential_L2_bound state

end ContinuumCoulomb

end

end OAI
