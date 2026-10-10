import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusL2Product

namespace OAI

/-! # Continuous dependence of physical L² multiplication on its coefficient -/

open MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure T)
noncomputable local instance torusL2CoefficientMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusL2CoefficientProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def torusL2Coefficient (f : H) : C(T, ℂ) →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun V => torusL2Product V f
      map_add' := by
        intro V W
        apply Lp.ext
        filter_upwards [torusL2Product_ae (V + W) f,
          torusL2Product_ae V f, torusL2Product_ae W f,
          Lp.coeFn_add (torusL2Product V f) (torusL2Product W f)] with x h hV hW ha
        rw [h, ha]
        simp only [Pi.add_apply, ContinuousMap.add_apply]
        rw [hV, hW, add_mul]
      map_smul' := by
        intro c V
        apply Lp.ext
        filter_upwards [torusL2Product_ae (c • V) f,
          torusL2Product_ae V f, Lp.coeFn_smul c (torusL2Product V f)] with x h hV ha
        simp only [RingHom.id_apply]
        rw [h, ha]
        simp only [Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
        rw [hV, mul_assoc] }
    ‖f‖ (by
      intro V
      change ‖torusL2ProductValue V f‖ ≤ ‖f‖ * ‖V‖
      rw [mul_comm]
      exact torusL2ProductValue_norm_le V f)

@[simp] theorem torusL2Coefficient_apply (f : H) (V : C(T, ℂ)) :
    torusL2Coefficient f V = torusL2Product V f := rfl

end DefocusingNLS

end OAI
