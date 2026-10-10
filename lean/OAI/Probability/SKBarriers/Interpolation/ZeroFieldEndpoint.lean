import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockMassValue
import OAI.Probability.SKBarriers.Interpolation.SKHamiltonianDerivative
import OAI.Probability.SKBarriers.Gaussian.GaussianStepAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascadePressure_root (b : ℕ) (m : Fin b → ℝ) (g : E → ℝ) :
    cascadePressure b m (fun z => g (cascadeRoot (E := E) b z)) = g := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change cascadePressure b _ (gaussianStep _ (fun z => g (cascadeRoot (E := E) b z.1))) = g
    rw [gaussianStep_prefix (fun z => g (cascadeRoot (E := E) b z)) (m (Fin.last b)),ih]
end Generic

theorem coordinateProjection_append_prefix (a b : ℕ) (i : Fin a)
    (z : CascadeSpace (ParameterSpace a) b) :
    coordinateProjection (a+b) (Fin.castAdd b i) (parameterAppend a b z) =
      coordinateProjection a i (cascadeRoot (E := ParameterSpace a) b z) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change coordinateProjection ((a+b)+1) (Fin.castSucc (Fin.castAdd b i))
      (parameterAppend a b z.1,z.2) = _
    rw [coordinateProjection_castSucc,ih]
    rfl

theorem blockExponent_zeroFields_append {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (s : Config N) (z : CascadeSpace (ParameterSpace D) ((k+1)*N)) :
    blockExponent I a (fun _ : Fin (k+1) => 0) s (parameterAppend D ((k+1)*N) z) =
      spinExponent D a I s (cascadeRoot (E := ParameterSpace D) ((k+1)*N) z) := by
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,add_zero,coordinateProjection_append_prefix,
    spinExponent,coordinateLinear_apply]

theorem blockMass_at_disorder (D N k : ℕ) (i : Fin D) :
    blockMass D N k (Fin.castAdd ((k+1)*N) i) = 0 := by
  rw [blockMass_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  simp only [blockLevel_val,Fin.val_castAdd]
  omega

theorem skBlockRoot_zero_fields (N k : ℕ) (β : ℝ) :
    skBlockRoot N k β (fun _ => 0) =
      ∫ z, affineLogPartition (fun _ : Config N => 0)
        (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N)) z
        ∂fiberGaussian (Fintype.card (Edge N)) 0 := by
  unfold skBlockRoot
  rw [hierarchyPressure_split]
  have he : (fun z => affineLogPartition (fun _ : Config N => 0)
      (blockExponent (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) (fun _ : Fin (k+1) => 0))
        (parameterAppend (Fintype.card (Edge N)) ((k+1)*N) z)) =
      fun z => affineLogPartition (fun _ : Config N => 0)
        (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N))
          (cascadeRoot (E := ParameterSpace (Fintype.card (Edge N))) ((k+1)*N) z) := by
    funext z
    simp only [affineLogPartition,blockExponent_zeroFields_append]
  rw [he,cascadePressure_root]
  simp only [blockMass_at_disorder]
  apply hierarchyPressure_zero
  exact affineLogPartition_boundedDerivs _ _
end SK.Analytic

end
end

end

end OAI
