import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # The physical principal potential on L²

The actual odd-power derivative acts pointwise on every ordered spatial
derivative. Its L² bound is independent of the derivative order; only the
lower commutator terms require separate compact-error estimates.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem norm_oddPowerDerivative_le (m : ℕ) (z v : ℂ) :
    ‖oddPowerDerivative m z v‖ ≤ (2 * (m : ℝ) + 1) * ‖z‖ ^ (2 * m) * ‖v‖ := by
  cases m with
  | zero => simp [oddPowerDerivative]
  | succ m =>
      have hp : ‖z‖ ^ (2 * (m + 1)) = ‖z‖ ^ m * ‖z‖ ^ m * ‖z‖ ^ 2 := by
        rw [show 2 * (m + 1) = m + m + 2 by omega, pow_add, pow_add]
      rw [oddPowerDerivative, add_apply]
      calc
        _ ≤ ‖((((m + 1 + 1 : ℕ) : ℂ) * z ^ (m + 1) * star z ^ (m + 1)) • v)‖ +
            ‖((((m + 1 : ℕ) : ℂ) * z ^ (m + 1 + 1) * star z ^ m) • star v)‖ := by
          exact norm_add_le _ _
        _ = _ := by
          rw [hp]
          simp only [norm_smul, norm_mul, norm_pow, norm_star, Complex.norm_natCast]
          simp only [Nat.cast_add, Nat.cast_one, pow_add, pow_one, pow_two]
          ring

theorem norm_schrodingerOddPowerDerivative_le (m : ℕ) (z v : ℂ) :
    ‖-Complex.I * oddPowerDerivative m z v‖ ≤
      (2 * (m : ℝ) + 1) * ‖z‖ ^ (2 * m) * ‖v‖ := by
  simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using norm_oddPowerDerivative_le m z v

private theorem principalPotential_memLp (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (_hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) :
    MemLp (fun x => -Complex.I * oddPowerDerivative m (Q x) (f x)) 2 volume := by
  have hq : AEStronglyMeasurable Q (volume : Measure E) := hQ.aestronglyMeasurable
  have hf := Lp.aestronglyMeasurable f
  have hm : AEStronglyMeasurable
      (fun x => -Complex.I * oddPowerDerivative m (Q x) (f x)) volume := by
    simpa only [oddPowerDerivative, add_apply,
      smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul,
      Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.star_apply] using
      ((((aestronglyMeasurable_const.mul (hq.pow m)).mul (hq.star.pow m)).mul hf).add
        (((aestronglyMeasurable_const.mul (hq.pow (m + 1))).mul
          (hq.star.pow (m - 1))).mul hf.star)).const_mul (-Complex.I)
  apply (((Lp.memLp f).norm.const_mul ((2 * (m : ℝ) + 1) * M))).mono' hm
  filter_upwards [] with x
  exact (norm_schrodingerOddPowerDerivative_le m (Q x) (f x)).trans
    (by gcongr; exact hQB x)

noncomputable def homogeneousPrincipalAction (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure E) :=
  (principalPotential_memLp m Q hQ M hM hQB f).toLp
    (fun x => -Complex.I * oddPowerDerivative m (Q x) (f x))

theorem homogeneousPrincipalAction_ae (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) :
    homogeneousPrincipalAction m Q hQ M hM hQB f =ᵐ[volume]
      (fun x => -Complex.I * oddPowerDerivative m (Q x) (f x)) := MemLp.coeFn_toLp _

theorem homogeneousPrincipalAction_norm_le (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) :
    ‖homogeneousPrincipalAction m Q hQ M hM hQB f‖ ≤ (2 * (m : ℝ) + 1) * M * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [homogeneousPrincipalAction_ae m Q hQ M hM hQB f] with x hx
  rw [hx]
  exact (norm_schrodingerOddPowerDerivative_le m (Q x) (f x)).trans
    (by gcongr; exact hQB x)

noncomputable def homogeneousPrincipalPotential (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M) :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  let A : Lp ℂ 2 (volume : Measure E) →ₗ[ℝ] Lp ℂ 2 (volume : Measure E) :=
    { toFun := homogeneousPrincipalAction m Q hQ M hM hQB
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [homogeneousPrincipalAction_ae m Q hQ M hM hQB (f + g),
          homogeneousPrincipalAction_ae m Q hQ M hM hQB f,
          homogeneousPrincipalAction_ae m Q hQ M hM hQB g, Lp.coeFn_add f g,
          Lp.coeFn_add (homogeneousPrincipalAction m Q hQ M hM hQB f)
            (homogeneousPrincipalAction m Q hQ M hM hQB g)] with x hfg hf hg ha hb
        rw [hfg, hb, Pi.add_apply, hf, hg, ha, Pi.add_apply, map_add, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [homogeneousPrincipalAction_ae m Q hQ M hM hQB (c • f),
          homogeneousPrincipalAction_ae m Q hQ M hM hQB f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (homogeneousPrincipalAction m Q hQ M hM hQB f)] with x hcf hf ha hb
        simp only [RingHom.id_apply]
        rw [hcf, hb, Pi.smul_apply, hf, ha, Pi.smul_apply, map_smul]
        simp only [Complex.real_smul]
        ring }
  A.mkContinuous ((2 * (m : ℝ) + 1) * M)
    (homogeneousPrincipalAction_norm_le m Q hQ M hM hQB)

theorem homogeneousPrincipalPotential_norm_le (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M) :
    ‖homogeneousPrincipalPotential m Q hQ M hM hQB‖ ≤ (2 * (m : ℝ) + 1) * M := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity)
    (homogeneousPrincipalAction_norm_le m Q hQ M hM hQB)

theorem homogeneousPrincipalPotential_energy_le (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ f (homogeneousPrincipalPotential m Q hQ M hM hQB f) ≤
      ((2 * (m : ℝ) + 1) * M) * ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖f‖ * ‖homogeneousPrincipalPotential m Q hQ M hM hQB f‖ := real_inner_le_norm _ _
    _ ≤ ‖f‖ * (((2 * (m : ℝ) + 1) * M) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (homogeneousPrincipalAction_norm_le m Q hQ M hM hQB f)
        (norm_nonneg f)
    _ = _ := by ring

/-- Every ordered derivative receives the same pointwise operator; the
constant is independent of the number of derivatives. -/
theorem homogeneousPrincipalPotential_ordered_energy_le (m N : ℕ)
    (Q : E → ℂ) (hQ : Continuous Q) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : (Fin N → Fin 12) → Lp ℂ 2 (volume : Measure E)) :
    ∑ j, inner ℝ (f j) (homogeneousPrincipalPotential m Q hQ M hM hQB (f j)) ≤
      ((2 * (m : ℝ) + 1) * M) * ∑ j, ‖f j‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => homogeneousPrincipalPotential_energy_le m Q hQ M hM hQB (f j))

end DefocusingNLS

end OAI
