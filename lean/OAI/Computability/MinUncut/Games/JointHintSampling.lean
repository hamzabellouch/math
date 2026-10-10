import Mathlib
import OAI.Computability.MinUncut.Estimates.ListDecoding

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

def hiddenSet (H : Finset I) : I → Bool := fun i => decide (i ∈ H)
def rawPositions {d : ℕ} (w : I → JointForms.Raw d) : I → Fin 3 := fun i => (w i).1.1
def rawCoefficients {d : ℕ} (κ : Fin d → F₂) (w : I → JointForms.Raw d) :
    HintCoefficients I d := fun k => (κ k,(fun i => (w i).1.2 k,fun i => (w i).2 k))

def hintRawEquiv (d : ℕ) :
    ((I → Fin 3) × HintCoefficients I d) ≃ ((Fin d → F₂) × (I → JointForms.Raw d)) where
  toFun z := (fun k => (z.2 k).1,fun i => ((z.1 i,fun k => (z.2 k).2.1 i),
    fun k => (z.2 k).2.2 i))
  invFun z := (rawPositions z.2,rawCoefficients z.1 z.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma origin_coordinate_decomposition (E : Equation Name) (a : alphabet E) :
    a.val=directionEmbedding E ((alphabetCoordinates E).symm a)+(origin E).val := by
  exact congrArg Subtype.val ((alphabetCoordinates E).apply_symm_apply a) |>.symm

omit [Fintype I] in
lemma raw_slot_expansion (U : I → Equation Name) {d : ℕ} (H : Finset I)
    (w : I → JointForms.Raw d) (a : FirstAlphabet U) (i : I) (k : Fin d) :
    (if i ∈ H then (w i).1.2 k*(a i).val (w i).1.1 else (w i).2 k (a i).val) =
    (JointForms.output (fun i => directionEmbedding (U i)) H w i k)
      ((alphabetCoordinates (U i)).symm (a i)) +
      (if i ∈ H then (w i).1.2 k*(origin (U i)).val (w i).1.1
        else (w i).2 k (origin (U i)).val) := by
  classical
  by_cases hi : i ∈ H
  · simp only [hi,↓reduceIte,JointForms.output,JointForms.hiddenPull]
    change (w i).1.2 k*(a i).val (w i).1.1 =
      (w i).1.2 k*(directionEmbedding (U i) ((alphabetCoordinates (U i)).symm (a i))) (w i).1.1+_
    rw [origin_coordinate_decomposition (U i) (a i)]
    simp only [Pi.add_apply,mul_add]
  · simp only [hi,↓reduceIte,JointForms.output,JointForms.fullPull,
      LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.dualMap_apply]
    rw [origin_coordinate_decomposition (U i) (a i),map_add]

lemma raw_joint_identity (U : I → Equation Name) {d k : ℕ} (H : FixedSets I k)
    (κ : Fin d → F₂) (w : I → JointForms.Raw d) :
    firstHints U (hiddenSet H.val) (rawPositions w) (rawCoefficients κ w) =
    tupleCoordinateGenerator U d
      (JointForms.affineOutput (fun i => directionEmbedding (U i))
        (fun i => (origin (U i)).val) (κ,H,w)) := by
  classical
  funext l
  apply AffineMap.ext
  intro a
  change formPullback (projection U (hiddenSet H.val) (rawPositions w))
    (directHint _ (κ l) (fun i => (w i).1.2 l) (fun i => (w i).2 l)) a =
    firstFormCoordinates U (_,_) a
  rw [pulledHint_apply,firstFormCoordinates_apply]
  simp only [hiddenSet,decide_eq_true_eq,rawPositions]
  simp_rw [raw_slot_expansion U H.val w a]
  simp only [Finset.sum_add_distrib,JointForms.affineOutput,JointForms.offset,Pi.add_apply]
  ring

end MinUncut.Outer

end
end

end OAI
