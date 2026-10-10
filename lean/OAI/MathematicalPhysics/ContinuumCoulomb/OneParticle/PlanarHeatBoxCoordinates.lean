import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HeatKernelModulus
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatEvolution
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! Exact two-coordinate box formula for the actual heat average.
The forcing vanishes outside this fixed square, so spatial truncation
introduces no error. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarPairEquiv : PlanarPosition ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

theorem planarPairEquiv_apply (r : PlanarPosition) : planarPairEquiv r = (r 0, r 1) := rfl

theorem planarPairEquiv_symm_apply (p : ℝ × ℝ) :
    planarPairEquiv.symm p = WithLp.toLp 2 ![p.1, p.2] := by
  ext i
  fin_cases i <;> rfl

theorem planarPairEquiv_measurePreserving : MeasurePreserving planarPairEquiv :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem planarPairEquiv_symm_continuous : Continuous planarPairEquiv.symm := by
  rw [show (planarPairEquiv.symm : (ℝ × ℝ) → PlanarPosition) =
      (fun p => WithLp.toLp 2 ![p.1, p.2]) from funext planarPairEquiv_symm_apply]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (by fun_prop)

theorem planarPair_integral (f : PlanarPosition → ℝ) :
    (∫ r, f r) = ∫ p, f (planarPairEquiv.symm p) := by
  have h := planarPairEquiv_measurePreserving.integral_comp' (f ∘ planarPairEquiv.symm)
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using h

theorem planarForcing_pair_zero {p : ℝ × ℝ}
    (hp : p ∉ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :
    planarForcing (planarPairEquiv.symm p) = 0 := by
  apply planarForcing_zero_of_norm_ge_one
  have h0 : |p.1| ≤ ‖planarPairEquiv.symm p‖ := by
    simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
      Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 0
  have h1 : |p.2| ≤ ‖planarPairEquiv.symm p‖ := by
    simpa only [planarPairEquiv_symm_apply, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Real.norm_eq_abs] using PiLp.norm_apply_le (planarPairEquiv.symm p) 1
  by_contra h
  have hn : ‖planarPairEquiv.symm p‖ < 1 := lt_of_not_ge h
  apply hp
  exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
    ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩

theorem planarHeatAverage_box (t : ℝ) (r : PlanarPosition) :
    planarHeatAverage t r = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      planarHeatKernel t (r - planarPairEquiv.symm (x, y)) *
        planarForcing (planarPairEquiv.symm (x, y)) := by
  rw [planarHeatAverage_flip, planarPair_integral]
  let f := fun p : ℝ × ℝ => planarHeatKernel t (r - planarPairEquiv.symm p) *
    planarForcing (planarPairEquiv.symm p)
  have hf : Continuous f :=
    ((planarHeatKernel_continuous t).comp (continuous_const.sub planarPairEquiv_symm_continuous)).mul
      (planarForcing_C7.continuous.comp planarPairEquiv_symm_continuous)
  have hi : IntegrableOn f (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hs : (∫ p, f p) = ∫ p in Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1, f p := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp only [f, planarForcing_pair_zero hp, mul_zero]
  change (∫ p, f p) = _
  rw [hs]
  rw [Measure.volume_eq_prod, setIntegral_prod f hi]
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rfl

theorem planarHeatResolvent_box (t : ℝ) (r : PlanarPosition) :
    Real.exp (-t) * planarHeatAverage t r =
      ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
        HeatKernelModulus.kernel t (‖r - planarPairEquiv.symm (x, y)‖ ^ 2) *
          planarForcing (planarPairEquiv.symm (x, y)) := by
  rw [planarHeatAverage_box, ← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext y
  rw [HeatKernelModulus.kernel_eq_heat]
  ring

end ContinuumCoulomb

end

end OAI
