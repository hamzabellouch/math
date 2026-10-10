import Mathlib
import OAI.Probability.SKBarriers.Scalar.PrefixAlgebra
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockTrace
import OAI.Probability.SKBarriers.Hierarchy.HierarchyBlocks

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeRootMoment
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascadeMoment_root (n : ℕ) (m : Fin n → ℝ) (f : CascadeSpace E n → ℝ)
    (hf : BoundedDerivs f) (g : E → ℝ) :
    cascadeMoment n m f (fun z => g (cascadeRoot (E := E) n z)) = g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : gaussianAverage (m (Fin.last n)) f (fun z => g (cascadeRoot (E := E) (n+1) z)) =
        fun z => g (cascadeRoot (E := E) n z) := by
      exact gaussianAverage_const_prefix hf _ (fun z => g (cascadeRoot (E := E) n z))
    rw [cascadeMoment,he]
    exact ih _ _ (hf.gaussianStep _)
end CascadeRootMoment

section HierarchyBlockTrace
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchySpinWeight (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) (s : S) : ℝ :=
  hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
    (fun z => affineGibbs (fun _ => 0) U z s) j z

theorem hierarchySpinMean_after_block (a b d : ℕ) (m : Fin (a+(b+d)) → ℝ)
    (U : S → ParameterSpace (a+(b+d)) →L[ℝ] ℝ) (v : S → ℝ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) d) :
    hierarchySpinMean (a+(b+d)) m U v ⟨a+b,by omega⟩ (parameterBlocks a b d z) =
      ∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
        (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap)
        (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) d z) s*v s := by
  unfold hierarchySpinMean
  rw [hierarchyMomentLevel_after_block]
  exact cascadeMoment_affineMoment d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
    (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) v _

theorem hierarchySpinMean_before_block (a b d : ℕ) (m : Fin (a+(b+d)) → ℝ)
    (U : S → ParameterSpace (a+(b+d)) →L[ℝ] ℝ) (v : S → ℝ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) d) :
    let F := cascadePressure d (fun i => m ⟨a+b+i,by omega⟩)
      (affineLogPartition (fun _ => 0) (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    let X := fun x => ∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) x s*v s
    hierarchySpinMean (a+(b+d)) m U v ⟨a,by omega⟩ (parameterBlocks a b d z) =
      cascadeMoment b (fun i => m ⟨a+i,by omega⟩) F X
        (cascadeRoot (E := ParameterSpace a) b (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) d z)) := by
  dsimp only
  unfold hierarchySpinMean
  rw [hierarchyMomentLevel_before_block]
  congr 1
  funext x
  exact cascadeMoment_affineMoment d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
    (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) v x

theorem hierarchyMeanSquare_before_block (a b d : ℕ) (m : Fin (a+(b+d)) → ℝ)
    (U : S → ParameterSpace (a+(b+d)) →L[ℝ] ℝ) (v : S → ℝ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) d) :
    let F := cascadePressure d (fun i => m ⟨a+b+i,by omega⟩)
      (affineLogPartition (fun _ => 0) (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    let X := fun x => ∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) x s*v s
    hierarchyMomentLevel (a+(b+d)) m (affineLogPartition (fun _ => 0) U)
      (fun z => (hierarchySpinMean (a+(b+d)) m U v ⟨a+b,by omega⟩ z)^2)
      ⟨a,by omega⟩ (parameterBlocks a b d z) =
      cascadeMoment b (fun i => m ⟨a+i,by omega⟩) F (fun x => (X x)^2)
        (cascadeRoot (E := ParameterSpace a) b (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) d z)) := by
  dsimp only
  rw [hierarchyMomentLevel_before_block]
  simp only [hierarchySpinMean_after_block]
  congr 1
  exact cascadeMoment_root d (fun i => m ⟨a+b+i,by omega⟩)
    (affineLogPartition (fun _ => 0) (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    (affineLogPartition_boundedDerivs (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap))
    (fun x => (∑ s, cascadeSpinWeight d (fun i => m ⟨a+b+i,by omega⟩) (fun _ => 0)
      (fun s => (U s).comp (parameterBlocks a b d).toContinuousLinearMap) x s*v s)^2)

theorem hierarchyBlock_conditional_trace (a N d : ℕ) (m : Fin (a+(N+d)) → ℝ)
    (U : S → ParameterSpace (a+(N+d)) →L[ℝ] ℝ)
    (p scale : ℝ) (hp : 0 < p) (ha : 0 < scale) (hl : p ≤ 1)
    (hb : ∀ i : Fin N, m ⟨a+i,by omega⟩ = p)
    (hm : ∀ i : Fin d, p ≤ m ⟨a+N+i,by omega⟩)
    (hmu : ∀ i : Fin d, m ⟨a+N+i,by omega⟩ ≤ 1)
    (hmono : Monotone (fun i : Fin d => m ⟨a+N+i,by omega⟩))
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, U s (parameterBlocks a N d (cascadeLift d
      (parameterNoise (E := ParameterSpace a) N (coordinateAxis N i)))) = scale*v s i)
    (z : ParameterSpace (a+(N+d))) :
    let C := finiteCovariance (hierarchySpinWeight (a+(N+d)) m U ⟨a,by omega⟩ z) v
    (C*C).trace ≤ (N : ℝ)*(∑ i, (
      hierarchyMomentLevel (a+(N+d)) m (affineLogPartition (fun _ => 0) U)
        (fun z => (hierarchySpinMean (a+(N+d)) m U (fun s => v s i) ⟨a+N,by omega⟩ z)^2) ⟨a,by omega⟩ z-
      (hierarchySpinMean (a+(N+d)) m U (fun s => v s i) ⟨a,by omega⟩ z)^2))+
      (N : ℝ)/(scale^2*p^2) := by
  obtain ⟨w,rfl⟩ := (parameterBlocks a N d).surjective z
  let L := fun s => (U s).comp (parameterBlocks a N d).toContinuousLinearMap
  let mf := fun i : Fin d => m ⟨a+N+i,by omega⟩
  let F := cascadePressure d mf (affineLogPartition (fun _ => 0) L)
  let P := cascadeSpinWeight d mf (fun _ => 0) L
  let x := cascadeRoot (E := ParameterSpace a) N
    (cascadeRoot (E := CascadeSpace (ParameterSpace a) N) d w)
  have he : (fun i : Fin N => m ⟨a+i,by omega⟩) = fun _ => p := funext hb
  have hW : hierarchySpinWeight (a+(N+d)) m U ⟨a,by omega⟩ (parameterBlocks a N d w) =
      fun s => cascadeMoment N (fun _ => p) F (fun z => P z s) x := by
    funext s
    unfold hierarchySpinWeight
    rw [hierarchyMomentLevel_before_block,he]
    rfl
  have hX (i : Fin N) := hierarchySpinMean_before_block a N d m U (fun s => v s i) w
  have hY (i : Fin N) := hierarchyMeanSquare_before_block a N d m U (fun s => v s i) w
  simp only [he] at hX hY
  have H := cascadeBlock_trace N d mf (fun _ => 0) L p scale hp ha hl hm hmu hmono v hvb hv x
  dsimp only at H ⊢
  rw [hW]
  simpa only [hX,hY,finiteMean_apply] using H
end HierarchyBlockTrace
end SK.Analytic

end
end

end

end OAI
