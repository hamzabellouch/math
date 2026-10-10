import Mathlib
import OAI.Probability.SKBarriers.Scalar.ThermalMoments
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockLaw

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def parameterBlocks : (a b c : ℕ) →
    CascadeSpace (CascadeSpace (ParameterSpace a) b) c ≃L[ℝ] ParameterSpace (a+(b+c))
  | a,b,0 => parameterAppend a b
  | a,b,c+1 => (parameterBlocks a b c).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem parameterBlocks_succ (a b c : ℕ)
    (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) c) (y : ℝ) :
    parameterBlocks a b (c+1) (z,y) = (parameterBlocks a b c z,y) := rfl

theorem gaussianStep_blocks (a b c : ℕ) (p : ℝ) (f : ParameterSpace (a+(b+(c+1))) → ℝ) :
    gaussianStep p (fun z => f (parameterBlocks a b (c+1) z)) =
      fun z => gaussianStep p f (parameterBlocks a b c z) := rfl

theorem gaussianAverage_blocks (a b c : ℕ) (p : ℝ) (f g : ParameterSpace (a+(b+(c+1))) → ℝ) :
    gaussianAverage p (fun z => f (parameterBlocks a b (c+1) z)) (fun z => g (parameterBlocks a b (c+1) z)) =
      fun z => gaussianAverage p f g (parameterBlocks a b c z) := rfl

theorem hierarchyMomentLevel_after_block (a b c : ℕ) (m : Fin (a+(b+c)) → ℝ)
    (f g : ParameterSpace (a+(b+c)) → ℝ) (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) c) :
    hierarchyMomentLevel (a+(b+c)) m f g ⟨a+b,by omega⟩ (parameterBlocks a b c z) =
      cascadeMoment c (fun i => m ⟨a+b+i,by omega⟩)
        (fun z => f (parameterBlocks a b c z)) (fun z => g (parameterBlocks a b c z))
        (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) c z) := by
  induction c with
  | zero =>
    change hierarchyMomentLevel (a+b) m f g (Fin.last (a+b)) (parameterAppend a b z) = g (parameterAppend a b z)
    rw [hierarchyMomentLevel_last]
  | succ c ih =>
    change hierarchyMomentLevel ((a+(b+c))+1) m f g (Fin.castSucc ⟨a+b,by omega⟩)
      (parameterBlocks a b c z.1,z.2) = _
    rw [hierarchyMomentLevel,Fin.lastCases_castSucc,ih,cascadeMoment,gaussianStep_blocks,gaussianAverage_blocks]
    have he : (⟨a+b+(Fin.last c).val,by omega⟩ : Fin (a+(b+(c+1)))) = Fin.last (a+(b+c)) := by
      apply Fin.ext
      exact Nat.add_assoc a b c
    rw [he]
    rfl

theorem hierarchyMomentLevel_before_block (a b c : ℕ) (m : Fin (a+(b+c)) → ℝ)
    (f g : ParameterSpace (a+(b+c)) → ℝ) (z : CascadeSpace (CascadeSpace (ParameterSpace a) b) c) :
    hierarchyMomentLevel (a+(b+c)) m f g ⟨a,by omega⟩ (parameterBlocks a b c z) =
      cascadeMoment b (fun i => m ⟨a+i,by omega⟩)
        (cascadePressure c (fun i => m ⟨a+b+i,by omega⟩) (fun z => f (parameterBlocks a b c z)))
        (cascadeMoment c (fun i => m ⟨a+b+i,by omega⟩)
          (fun z => f (parameterBlocks a b c z)) (fun z => g (parameterBlocks a b c z)))
        (cascadeRoot (E := ParameterSpace a) b (cascadeRoot (E := CascadeSpace (ParameterSpace a) b) c z)) := by
  induction c with
  | zero =>
    exact hierarchyMomentLevel_split a b m f g z
  | succ c ih =>
    change hierarchyMomentLevel ((a+(b+c))+1) m f g (Fin.castSucc ⟨a,by omega⟩)
      (parameterBlocks a b c z.1,z.2) = _
    rw [hierarchyMomentLevel,Fin.lastCases_castSucc,ih,cascadePressure,cascadeMoment,gaussianStep_blocks,gaussianAverage_blocks]
    have he : (⟨a+b+(Fin.last c).val,by omega⟩ : Fin (a+(b+(c+1)))) = Fin.last (a+(b+c)) := by
      apply Fin.ext
      exact Nat.add_assoc a b c
    rw [he]
    rfl

section AffineComposition
variable {E F S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype S]

theorem affineLogPartition_comp (c : S → ℝ) (L : S → F →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    affineLogPartition c (fun s => (L s).comp A) = fun z => affineLogPartition c L (A z) := rfl

theorem affineGibbs_comp (c : S → ℝ) (L : S → F →L[ℝ] ℝ) (A : E →L[ℝ] F) (z : E) (s : S) :
    affineGibbs c (fun s => (L s).comp A) z s = affineGibbs c L (A z) s := rfl
end AffineComposition
end SK.Analytic

end
end

end

end OAI
