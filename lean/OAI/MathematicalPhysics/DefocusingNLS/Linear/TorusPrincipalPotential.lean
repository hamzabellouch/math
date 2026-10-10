import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPrincipalPotential
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusFourierIsometry

namespace OAI

/-! # The order-independent principal energy estimate on torus L²

The actual odd-power derivative is applied to each physical derivative
component.  Its bound uses the profile supremum, independently of the
number of derivatives; commutators are treated separately.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "E" => UnitAddTorus (Fin 12)
noncomputable local instance torusPrincipalPotentialMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusPrincipalPotentialProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem torusPrincipalPotential_memLp (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
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

noncomputable def torusPrincipalAction (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure E) :=
  (torusPrincipalPotential_memLp m Q hQ M hM hQB f).toLp
    (fun x => -Complex.I * oddPowerDerivative m (Q x) (f x))

theorem torusPrincipalAction_ae (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) :
    torusPrincipalAction m Q hQ M hM hQB f =ᵐ[volume]
      (fun x => -Complex.I * oddPowerDerivative m (Q x) (f x)) := MemLp.coeFn_toLp _

theorem torusPrincipalAction_norm_le (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) :
    ‖torusPrincipalAction m Q hQ M hM hQB f‖ ≤ (2 * (m : ℝ) + 1) * M * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [torusPrincipalAction_ae m Q hQ M hM hQB f] with x hx
  rw [hx]
  exact (norm_schrodingerOddPowerDerivative_le m (Q x) (f x)).trans
    (by gcongr; exact hQB x)

noncomputable def torusPrincipalPotential (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M) :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  let A : Lp ℂ 2 (volume : Measure E) →ₗ[ℝ] Lp ℂ 2 (volume : Measure E) :=
    { toFun := torusPrincipalAction m Q hQ M hM hQB
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [torusPrincipalAction_ae m Q hQ M hM hQB (f + g),
          torusPrincipalAction_ae m Q hQ M hM hQB f,
          torusPrincipalAction_ae m Q hQ M hM hQB g, Lp.coeFn_add f g,
          Lp.coeFn_add (torusPrincipalAction m Q hQ M hM hQB f)
            (torusPrincipalAction m Q hQ M hM hQB g)] with x hfg hf hg ha hb
        rw [hfg, hb, Pi.add_apply, hf, hg, ha, Pi.add_apply, map_add, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [torusPrincipalAction_ae m Q hQ M hM hQB (c • f),
          torusPrincipalAction_ae m Q hQ M hM hQB f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (torusPrincipalAction m Q hQ M hM hQB f)] with x hcf hf ha hb
        simp only [RingHom.id_apply]
        rw [hcf, hb, Pi.smul_apply, hf, ha, Pi.smul_apply, map_smul]
        simp only [Complex.real_smul]
        ring }
  A.mkContinuous ((2 * (m : ℝ) + 1) * M)
    (torusPrincipalAction_norm_le m Q hQ M hM hQB)

theorem torusPrincipalPotential_norm_le (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M) :
    ‖torusPrincipalPotential m Q hQ M hM hQB‖ ≤ (2 * (m : ℝ) + 1) * M := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity)
    (torusPrincipalAction_norm_le m Q hQ M hM hQB)

theorem torusPrincipalPotential_energy_le (m : ℕ) (Q : E → ℂ) (hQ : Continuous Q)
    (M : ℝ) (hM : 0 ≤ M) (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ f (torusPrincipalPotential m Q hQ M hM hQB f) ≤
      ((2 * (m : ℝ) + 1) * M) * ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖f‖ * ‖torusPrincipalPotential m Q hQ M hM hQB f‖ := real_inner_le_norm _ _
    _ ≤ ‖f‖ * (((2 * (m : ℝ) + 1) * M) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (torusPrincipalAction_norm_le m Q hQ M hM hQB f)
        (norm_nonneg f)
    _ = _ := by ring

/-- Every ordered derivative receives the same pointwise operator; the
constant is independent of the number of derivatives. -/
theorem torusPrincipalPotential_ordered_energy_le (m N : ℕ)
    (Q : E → ℂ) (hQ : Continuous Q) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x, ‖Q x‖ ^ (2 * m) ≤ M)
    (f : (Fin N → Fin 12) → Lp ℂ 2 (volume : Measure E)) :
    ∑ j, inner ℝ (f j) (torusPrincipalPotential m Q hQ M hM hQB (f j)) ≤
      ((2 * (m : ℝ) + 1) * M) * ∑ j, ‖f j‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => torusPrincipalPotential_energy_le m Q hQ M hM hQB (f j))

end DefocusingNLS

end OAI
