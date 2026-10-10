import Mathlib
import OAI.Analysis.HardSphere.Comparison.ConditionalLikelihood
import OAI.Analysis.HardSphere.Comparison.LocalMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_updateFinset (U s : Finset I) (hs : s⊆U) (x y : ∀i,X i) (v : ∀i:s,X i) :
    freezeOutside U x (Function.updateFinset y s v)=Function.updateFinset (freezeOutside U x y) s v := by
  funext i
  by_cases hi : i∈s
  · simp [freezeOutside,Function.updateFinset,hi,hs hi]
  · simp [freezeOutside,Function.updateFinset,hi]

omit [Fintype C] in
lemma frozen_partialNormalizer (checks : C → LocalCheck X) (μ : ∀i,Measure (X i))
    (U s o : Finset I) (hs : s⊆U) (x y : ∀i,X i)
    (hx : x∈retainedEvent checks (Finset.univ\U)) :
    partialNormalizer (frozenChecks checks U x) μ s o y=
      partialNormalizer checks μ s (o∪(Finset.univ\U)) (freezeOutside U x y) := by
  apply lintegral_congr
  intro v
  rw [frozen_checkWeight checks U (s∪o) x _ hx,freezeOutside_updateFinset U s hs]
  simp only [Finset.union_assoc]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_pair {Z : I → Type*} (U : Finset I) (x y : ∀i,X i) (z u : ∀i,Z i) :
    freezeOutside U (fun i ↦ (x i,z i)) (fun i ↦ (y i,u i))=
      fun i ↦ (freezeOutside U x y i,freezeOutside U z u i) := by
  funext i
  by_cases hi : i∈U <;> simp [freezeOutside,hi]

omit [Fintype C] in
lemma frozen_conditionalDensity {Z : I → Type*} [∀i,MeasurableSpace (Z i)]
    (checks : C → LocalCheck (fun i ↦ X i×Z i))
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (U s o : Finset I) (hs : s⊆U) (x y : ∀i,X i) (z u : ∀i,Z i)
    (hx : (fun i ↦ (x i,z i))∈retainedEvent checks (Finset.univ\U)) :
    conditionalDensity (frozenChecks checks U (fun i ↦ (x i,z i))) κ s o y u=
      conditionalDensity checks κ s (o∪(Finset.univ\U)) (freezeOutside U x y) (freezeOutside U z u) := by
  unfold conditionalDensity lmarginal
  have hκ : (fun i:s ↦ κ i (freezeOutside U x y i))=(fun i:s ↦ κ i (y i)) := by
    funext i;simp only [freezeOutside,ite_eq_left (hs i.property)]
  rw [hκ]
  apply lintegral_congr
  intro v
  dsimp only
  rw [frozen_checkWeight checks U (s∪o) _ _ hx,freezeOutside_pair,freezeOutside_updateFinset U s hs]
  simp only [Finset.union_assoc]

omit [Fintype C] in
lemma frozen_conditionalLikelihood {Z : I → Type*} [∀i,MeasurableSpace (Z i)]
    {R : Type*} [Fintype R] (reference : R → LocalCheck X)
    (checks : C → LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (U s o : Finset I) (hs : s⊆U) (x y : ∀i,X i) (z u : ∀i,Z i)
    (hx : x∈retainedEvent reference (Finset.univ\U))
    (hz : (fun i ↦ (x i,z i))∈retainedEvent checks (Finset.univ\U)) :
    conditionalLikelihood (frozenChecks reference U x) (frozenChecks checks U (fun i ↦ (x i,z i))) μ κ s o y u=
      conditionalLikelihood reference checks μ κ s (o∪(Finset.univ\U)) (freezeOutside U x y) (freezeOutside U z u) := by
  unfold conditionalLikelihood
  rw [frozen_partialNormalizer reference μ U s o hs x y hx,
    frozen_partialNormalizer checks _ U s o hs _ _ hz,
    freezeOutside_pair,
    frozen_conditionalDensity checks κ U s o hs x y z u hz]

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I R C D : Type*} [Fintype I] [DecidableEq I] [Fintype R] [Fintype C] [Fintype D]
  {X Z W : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]
  [∀i,MeasurableSpace (W i)]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_self (U : Finset I) (x : ∀i,X i) : freezeOutside U x x=x := by
  funext i
  by_cases hi : i∈U <;> simp [freezeOutside,hi]

lemma local_complement (s o U : Finset I) (hso : Disjoint s o) (hU : s∪o=U) :
    o∪(Finset.univ\U)=Finset.univ\s := by
  ext i
  have hd := Finset.disjoint_left.mp hso
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
  rw [←hU]
  simp only [Finset.mem_union]
  constructor
  · rintro (ho|hnot)
    · exact fun hs ↦ hd hs ho
    · exact fun hs ↦ hnot (Or.inl hs)
  · intro hs
    by_cases ho : i∈o
    · exact Or.inl ho
    · exact Or.inr (not_or.mpr ⟨hs,ho⟩)

theorem frozen_pair_mean_integrates
    (reference : R→LocalCheck X) (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (other : D→LocalCheck (fun i ↦ X i×W i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (W i)) [∀i,IsFiniteKernel (η i)]
    (s t os ot U : Finset I) (hs : s⊆U) (ht : t⊆U)
    (hso : Disjoint s os) (hto : Disjoint t ot) (hsU : s∪os=U) (htU : t∪ot=U)
    (z : ∀i,Z i) (w : ∀i,W i)
    (hS : ∀x,x∈retainedEvent reference (Finset.univ\U) →
      (fun i ↦ (x i,z i))∈retainedEvent checks (Finset.univ\U))
    (hT : ∀x,x∈retainedEvent reference (Finset.univ\U) →
      (fun i ↦ (x i,w i))∈retainedEvent other (Finset.univ\U))
    (A : ℝ≥0∞) (hA : A≠⊤)
    (hlocal : ∀x,x∈retainedEvent reference (Finset.univ\U) →
      let Ref := frozenChecks reference U x
      let ChS := frozenChecks checks U (fun i ↦ (x i,z i))
      let ChT := frozenChecks other U (fun i ↦ (x i,w i))
      lmarginal μ U (fun y ↦ checkWeight Ref U y *
        conditionalLikelihood Ref ChS μ κ s os y z *
        conditionalLikelihood Ref ChT μ η t ot y w) x /
        checkNormalizer Ref μ U x≤A) :
    (∫⁻x,conditionalLikelihood reference checks μ κ s (Finset.univ\s) x z *
      conditionalLikelihood reference other μ η t (Finset.univ\t) x w
      ∂conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ))≤A := by
  apply local_mean_integrates reference μ U _
    ((measurable_conditionalLikelihood reference checks μ κ _ _ z).mul
      (measurable_conditionalLikelihood reference other μ η _ _ w)) A hA
  intro x hx
  rw [←frozen_local_mean reference μ U x hx]
  have h := hlocal x hx
  dsimp only at h
  convert h using 2
  apply congrArg (fun f ↦ lmarginal μ U f x)
  funext y
  rw [frozen_conditionalLikelihood reference checks μ κ U s os hs x y z z hx (hS x hx),
    frozen_conditionalLikelihood reference other μ η U t ot ht x y w w hx (hT x hx),
    freezeOutside_self,freezeOutside_self,local_complement s os U hso hsU,
    local_complement t ot U hto htU]
  exact (mul_assoc _ _ _).symm

end HardSphere.Comparison

end
end

end

end OAI
