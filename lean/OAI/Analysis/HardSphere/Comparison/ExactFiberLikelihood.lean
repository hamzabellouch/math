import Mathlib
import OAI.Analysis.HardSphere.Comparison.ConditionalLikelihood
import OAI.Analysis.HardSphere.Conditioning.ProductNormalize

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I : Type*} [DecidableEq I] {X Z : I → Type*}
  [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]
  {E R : Type*} [Fintype E] [Fintype R]
  (checks : E → LocalCheck (fun i ↦ X i×Z i))
  (reference : R → LocalCheck X)
  (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
  (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]

lemma conditionalDensity_weighted (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i)
    (F : (∀i,X i) → ℝ≥0∞) (hF : Measurable F) :
    lmarginal μ s (fun y ↦ F y * conditionalDensity checks κ s o y z) x =
      lmarginal (fun i ↦ (μ i).compProd (κ i)) s
        (fun v ↦ F (fun i ↦ (v i).1)*checkWeight checks (s∪o) v) (fun i ↦ (x i,z i)) := by
  let f (p : ∀i : s,X i×Z i) :=
    F (Function.updateFinset x s (fun i ↦ (p i).1))*
      checkWeight checks (s∪o) (Function.updateFinset (fun i ↦ (x i,z i)) s p)
  have hf : Measurable f := by
    apply Measurable.mul
    · apply hF.comp
      exact measurable_updateFinset.comp (Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i)))
    · exact (measurable_checkWeight checks (s∪o)).comp measurable_updateFinset
  have he (p : ∀i : s,X i×Z i) :
      (fun i ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)=
        Function.updateFinset x s (fun i ↦ (p i).1) := by
    funext i
    by_cases hi : i∈s <;> simp [Function.updateFinset,hi]
  change (∫⁻y,F (Function.updateFinset x s y)*conditionalDensity checks κ s o (Function.updateFinset x s y) z
    ∂Measure.pi (fun i : s ↦ μ i))= _
  change _=∫⁻p,F (fun i ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)*
    checkWeight checks (s∪o) (Function.updateFinset (fun i ↦ (x i,z i)) s p)
    ∂Measure.pi (fun i : s ↦ (μ i).compProd (κ i))
  simp_rw [he]
  rw [show (fun p ↦ F (Function.updateFinset x s (fun i ↦ (p i).1))*
    checkWeight checks (s∪o) (Function.updateFinset (fun i ↦ (x i,z i)) s p))=f from rfl,
    lintegral_pi_compProd (fun i : s ↦ κ i) (fun i : s ↦ μ i) hf]
  apply lintegral_congr
  intro y
  change F (Function.updateFinset x s y)*
    (∫⁻u,checkWeight checks (s∪o)
      (fun i ↦ (Function.updateFinset x s y i,Function.updateFinset z s u i))
      ∂Measure.pi (fun i : s ↦ κ i (Function.updateFinset x s y i)))=_
  have hμ : (fun i : s ↦ κ i (Function.updateFinset x s y i))=(fun i : s ↦ κ i (y i)) := by
    funext i
    simp [Function.updateFinset,i.property]
  rw [hμ,←lintegral_const_mul _ (by
    exact (measurable_checkWeight checks (s∪o)).comp
      (Measurable.of_eval (fun i ↦ measurable_const.prodMk
        ((measurable_pi_apply i).comp measurable_updateFinset))))]
  apply lintegral_congr
  intro u
  have hp : (fun i ↦ (Function.updateFinset x s y i,Function.updateFinset z s u i))=
      Function.updateFinset (fun i ↦ (x i,z i)) s (fun i ↦ (y i,u i)) := by
    funext i
    by_cases hi : i∈s <;> simp [Function.updateFinset,hi]
  simp only [f,hp]

omit [Fintype E] [Fintype R] [∀i,IsProbabilityMeasure (μ i)] [∀i,IsFiniteKernel (κ i)] in
lemma conditionalLikelihood_update (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i) (y : ∀i : s,X i) :
    conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s y) z=
      (partialNormalizer reference μ s o x /
        partialNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s o (fun i ↦ (x i,z i)))*
      conditionalDensity checks κ s o (Function.updateFinset x s y) z := by
  unfold conditionalLikelihood
  rw [partialNormalizer_updateFinset]
  congr 2
  apply lmarginal_congr
  intro i hi
  simp [Function.updateFinset,hi]

def proposalFiber (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i) : Measure (∀i : s,X i×Z i) :=
  conditionedMeasure (Measure.pi (fun i : s ↦ (μ i).compProd (κ i)))
    {p | Function.updateFinset (fun i ↦ (x i,z i)) s p∈retainedEvent checks (s∪o)}

def referenceFiber (s o : Finset I) (x : ∀i,X i) : Measure (∀i : s,X i) :=
  conditionedMeasure (Measure.pi (fun i : s ↦ μ i))
    {p | Function.updateFinset x s p∈retainedEvent reference (s∪o)}

lemma fiber_lintegral {V : I → Type*} [∀i,MeasurableSpace (V i)]
    {C : Type*} [Fintype C] (c : C → LocalCheck V) (ν : ∀i,Measure (V i))
    (s o : Finset I) (v : ∀i,V i) (f : (∀i : s,V i) → ℝ≥0∞) :
    (∫⁻p,f p ∂conditionedMeasure (Measure.pi (fun i : s ↦ ν i))
      {p | Function.updateFinset v s p∈retainedEvent c (s∪o)})=
    (partialNormalizer c ν s o v)⁻¹ *
      ∫⁻p,f p*checkWeight c (s∪o) (Function.updateFinset v s p)
        ∂Measure.pi (fun i : s ↦ ν i) := by
  let A : Set (∀i : s,V i) := {p | Function.updateFinset v s p∈retainedEvent c (s∪o)}
  have hA : MeasurableSet A := (measurableSet_retainedEvent c (s∪o)).preimage measurable_updateFinset
  have hmass : (Measure.pi (fun i : s ↦ ν i)) A=partialNormalizer c ν s o v := by
    change _=∫⁻p,A.indicator (fun _ ↦ (1:ℝ≥0∞)) p ∂Measure.pi (fun i : s ↦ ν i)
    rw [lintegral_indicator_const hA,one_mul]
  change (∫⁻p,f p ∂conditionedMeasure _ A)=_
  rw [conditionedMeasure,lintegral_smul_measure,hmass]
  change _⁻¹ *(∫⁻p in A,f p ∂Measure.pi (fun i : s ↦ ν i))=_
  rw [←lintegral_indicator hA]
  congr 1
  apply lintegral_congr
  intro p
  by_cases hp : p∈A
  · simp only [Set.indicator_of_mem hp]
    change f p=f p*A.indicator (fun _ ↦ (1:ℝ≥0∞)) p
    rw [Set.indicator_of_mem hp,mul_one]
  · simp only [Set.indicator_of_notMem hp]
    change 0=f p*A.indicator (fun _ ↦ (1:ℝ≥0∞)) p
    rw [Set.indicator_of_notMem hp,mul_zero]

lemma proposalFiber_primary (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i)
    (hZ : 0<partialNormalizer reference μ s o x)
    (hincl : ∀(y : ∀i,X i)(u : ∀i,Z i),
      checkWeight checks (s∪o) (fun i ↦ (y i,u i))≤checkWeight reference (s∪o) y) :
    (proposalFiber checks μ κ s o x z).map (fun p i ↦ (p i).1)=
      (referenceFiber reference μ s o x).withDensity
        (fun y ↦ conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s y) z) := by
  let Z₀ := partialNormalizer reference μ s o x
  let Y₀ := partialNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s o (fun i ↦ (x i,z i))
  have hZT : Z₀≠⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (partialNormalizer_le_one reference s o x)
  have hZm : Z₀⁻¹*Z₀=1 := ENNReal.inv_mul_cancel (ne_of_gt hZ) hZT
  apply Measure.ext_of_lintegral
  intro f hf
  let F (y : ∀i,X i) := f (fun i : s ↦ y i)
  have hF : Measurable F := hf.comp (Measurable.of_eval (fun i ↦ measurable_pi_apply (i:I)))
  have hu (p : ∀i : s,X i) : F (Function.updateFinset x s p)=f p := by
    dsimp only [F]
    congr 1
    funext i
    simp [Function.updateFinset,i.property]
  have hm : Measurable (fun y : ∀i:s,X i ↦ conditionalLikelihood reference checks μ κ s o
      (Function.updateFinset x s y) z) :=
    (measurable_conditionalLikelihood reference checks μ κ s o z).comp
      (measurable_updateFinset (x:=x) (s:=s))
  have hproj : Measurable (fun p : ∀i:s,X i×Z i ↦ fun i ↦ (p i).1) :=
    Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i))
  rw [lintegral_map hf hproj,
    lintegral_withDensity_eq_lintegral_mul _ hm hf]
  simp only [Pi.mul_apply]
  rw [proposalFiber,referenceFiber]
  rw [fiber_lintegral checks (fun i ↦ (μ i).compProd (κ i)) s o
      (fun i ↦ (x i,z i)) (fun p ↦ f (fun i ↦ (p i).1)),
    fiber_lintegral reference μ s o x
      (fun p ↦ conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s p) z*f p)]
  have hw := conditionalDensity_weighted checks μ κ s o x z F hF
  have he : (∫⁻p,f (fun i ↦ (p i).1)*checkWeight checks (s∪o)
      (Function.updateFinset (fun i ↦ (x i,z i)) s p)
      ∂Measure.pi (fun i : s ↦ (μ i).compProd (κ i)))=
      lmarginal μ s (fun y ↦ F y*conditionalDensity checks κ s o y z) x := by
    rw [hw]
    apply lintegral_congr
    intro p
    congr 1
    change f (fun i ↦ (p i).1)=f (fun i : s ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)
    congr 1
    funext i
    simp [Function.updateFinset,i.property]
  rw [he]
  have hp (p : ∀i : s,X i) :
      (conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s p) z*f p)*
        checkWeight reference (s∪o) (Function.updateFinset x s p)=
      (Z₀/Y₀)*(F (Function.updateFinset x s p)*
        conditionalDensity checks κ s o (Function.updateFinset x s p) z) := by
    rw [conditionalLikelihood_update checks reference μ κ,hu]
    have hh := conditionalDensity_reference_support reference checks κ s o hincl
      (Function.updateFinset x s p) z
    calc
      _ = (Z₀/Y₀)*(f p*(checkWeight reference (s∪o) (Function.updateFinset x s p)*
        conditionalDensity checks κ s o (Function.updateFinset x s p) z)) := by ac_rfl
      _ = _ := by rw [hh]
  simp only [hp]
  have hprod : Measurable (fun p : ∀i:s,X i ↦
      F (Function.updateFinset x s p)*conditionalDensity checks κ s o (Function.updateFinset x s p) z) :=
    (hF.mul (measurable_conditionalDensity checks κ s o z)).comp
      (measurable_updateFinset (x:=x) (s:=s))
  rw [lintegral_const_mul _ hprod]
  change Y₀⁻¹ * _ = Z₀⁻¹ *((Z₀/Y₀)*_)
  rw [ENNReal.div_eq_inv_mul]
  calc
    _ = (Z₀⁻¹*Z₀)*(Y₀⁻¹*lmarginal μ s (fun y ↦ F y*conditionalDensity checks κ s o y z) x) := by rw [hZm,one_mul]
    _ = _ := by ac_rfl

end HardSphere.Comparison

end
end

end

end OAI
