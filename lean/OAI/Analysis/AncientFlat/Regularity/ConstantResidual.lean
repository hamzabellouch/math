import OAI.Analysis.AncientFlat.Kernel.ClassicalBase

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction
namespace ParabolicSchauder
open ParametrixVolterra FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def unitCoefficient : V →ᵇ Icc (1:ℝ) 1 :=
  BoundedContinuousFunction.const V ⟨1,le_rfl,le_rfl⟩
def unitSlab (T : ℝ) : C(Slab T,V →ᵇ Icc (1:ℝ) 1) :=
  ⟨fun _ => unitCoefficient,continuous_const⟩
lemma unit_residual_zero {T : ℝ} (t : Time T) (s : Slab T) :
    actualResidual zero_lt_one (unitSlab (V := V) T) 0 t s=0 := by
  ext f x
  rw [actualResidual,fullResidualCLM_apply]
  simp only [ZeroAtInftyContinuousMap.add_apply,C0Multiplier.mul_apply,
    ContinuousMap.zero_apply,BoundedContinuousFunction.coe_zero,
    zero_apply,ZeroAtInftyContinuousMap.zero_apply]
  rw [principalResidual_apply_scaled]
  simp [unitSlab,unitCoefficient]
lemma unit_c0Time (q : ℝ) (hq : 0<q) (f : C₀(V,ℂ)) (x : V) :
    c0Time zero_lt_one (unitCoefficient (V := V)) q f x=
      ∫ y : V, f y*BiharmonicKernel.kernel q (x-y) := by
  rw [c0Time_apply _ _ q hq]
  simp [timeValue,unitCoefficient]
end ParabolicSchauder

end

end OAI
