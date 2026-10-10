import OAI.Geometry.EinsteinFour.ScalarH1CompositionL2
import Mathlib.MeasureTheory.Function.LpOrder

namespace OAI

/-! A bounded scalar coefficient acts continuously and linearly on L2.
This permits passage of local coordinate gradient bounds through H1 closure. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def scalarL2BoundedMultiplier (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := scalarCompositionL2Multiply a ha hC
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [scalarCompositionL2Multiply_coe a ha hC (f + g),
          scalarCompositionL2Multiply_coe a ha hC f,
          scalarCompositionL2Multiply_coe a ha hC g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (scalarCompositionL2Multiply a ha hC f)
            (scalarCompositionL2Multiply a ha hC g)] with x hfg hf hg he hs
        simp only [Pi.add_apply] at he hs
        rw [hfg, he, hs, hf, hg]
        ring
      map_smul' := by
        intro r f
        apply Lp.ext
        filter_upwards [scalarCompositionL2Multiply_coe a ha hC (r • f),
          scalarCompositionL2Multiply_coe a ha hC f, Lp.coeFn_smul r f,
          Lp.coeFn_smul r (scalarCompositionL2Multiply a ha hC f)] with x hr hf he hs
        simp only [Pi.smul_apply, smul_eq_mul] at he hs
        simp only [RingHom.id_apply]
        rw [hr, he, hs, hf]
        ring }
    C (fun f => scalarCompositionL2Multiply_norm_le a ha hC f)

theorem scalarL2BoundedMultiplier_coe (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) :
    scalarL2BoundedMultiplier a ha hC f =ᵐ[μ] fun x => a x * f x :=
  scalarCompositionL2Multiply_coe a ha hC f

end
end PositiveEinsteinFour.Geometry

end OAI
