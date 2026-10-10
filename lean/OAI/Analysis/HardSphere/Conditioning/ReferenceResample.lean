import Mathlib
import OAI.Analysis.HardSphere.Collisions.PartialPhysicalLaw
import OAI.Analysis.HardSphere.Comparison.ExactFiberLikelihood
import OAI.Analysis.HardSphere.Comparison.IntegratedFiber
import OAI.Analysis.HardSphere.Comparison.LocalMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
instance conditioned_finite {A : Type*} [MeasurableSpace A] (μ : Measure A) (S : Set A) :
    IsFiniteMeasure (conditionedMeasure μ S) := by
  constructor
  simp only [conditionedMeasure,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) (by norm_num)

variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma lmarginal_updateFinset (μ : ∀i,Measure (X i)) (s : Finset I)
    (f : (∀i,X i)→ℝ≥0∞) (x : ∀i,X i) (u : ∀i:s,X i) :
    lmarginal μ s f (Function.updateFinset x s u)=lmarginal μ s f x := by
  apply lmarginal_congr
  intro i hi
  simp [Function.updateFinset,hi]

lemma reference_resample (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] (s : Finset I) :
    (insertedLaw checks μ s (Finset.univ\s)
      (conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))).map
      (fun p ↦ Function.updateFinset p.1 s p.2)=
      conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ) := by
  let w := checkWeight checks Finset.univ
  have hw : Measurable w := measurable_checkWeight checks _
  have hs : s∪(Finset.univ\s)=Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ s)
  let Z := (Measure.pi μ) (retainedEvent checks Finset.univ)
  have integral_ref (F : (∀i,X i)→ℝ≥0∞) :
      (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))=
        Z⁻¹*∫⁻x,w x*F x ∂Measure.pi μ := by
    rw [conditionedMeasure,lintegral_smul_measure,←lintegral_indicator (measurableSet_retainedEvent checks _)]
    congr 1
    apply lintegral_congr
    intro x
    by_cases hx : x∈retainedEvent checks Finset.univ <;> simp [w,checkWeight,hx]
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_updateFinset',insertedLaw,
    Measure.lintegral_compProd (show Measurable (fun p : (∀i,X i)×(∀i:s,X i) ↦ F (Function.updateFinset p.1 s p.2)) from hF.comp (measurable_updateFinset' (s:=s)))]
  have hkernel (x : ∀i,X i) :
      (∫⁻u,F (Function.updateFinset x s u) ∂fiberNormalize
        (Kernel.const _ (Measure.pi fun i:s ↦ μ i))
        (insertionFiberEvent checks s (Finset.univ\s)) x)=
      (lmarginal μ s w x)⁻¹*lmarginal μ s (fun y ↦ w y*F y) x := by
    have he : fiberNormalize (Kernel.const _ (Measure.pi fun i:s ↦ μ i))
        (insertionFiberEvent checks s (Finset.univ\s)) x=
      referenceFiber checks μ s (Finset.univ\s) x := by
      change (fiberRestrict _ _ x univ)⁻¹ • fiberRestrict _ _ x=_
      rw [fiberRestrict_apply _ (insertionFiberEvent_measurable checks s (Finset.univ\s))]
      simp only [Kernel.const_apply,Measure.restrict_apply_univ,referenceFiber,conditionedMeasure]
      rfl
    rw [he,referenceFiber,fiber_lintegral]
    simp only [hs,partialNormalizer]
    congr 1
    apply lintegral_congr
    intro u
    exact mul_comm _ _
  simp_rw [hkernel]
  rw [integral_ref,integral_ref]
  congr 1
  have hA : Measurable (lmarginal μ s w) := hw.lmarginal μ
  have hB : Measurable (lmarginal μ s (fun y ↦ w y*F y)) := (hw.mul hF).lmarginal μ
  apply lintegral_eq_of_lmarginal_eq s (hw.mul (hA.inv.mul hB)) (hw.mul hF)
  funext x
  change lmarginal μ s (fun y ↦ w y*((lmarginal μ s w y)⁻¹*lmarginal μ s (fun z ↦ w z*F z) y)) x = lmarginal μ s (fun y ↦ w y*F y) x
  have hfin : lmarginal μ s w x≠⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (lmarginal_mono (checkWeight_le_one checks _) x).trans_eq (by simp [lmarginal])
  have he : (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)*
      ((lmarginal μ s w (Function.updateFinset x s u))⁻¹*
        lmarginal μ s (fun y ↦ w y*F y) (Function.updateFinset x s u)))=
      (fun u ↦ w (Function.updateFinset x s u)*((lmarginal μ s w x)⁻¹*
        lmarginal μ s (fun y ↦ w y*F y) x)) := by
    funext u
    simp only [lmarginal_updateFinset]
  change (∫⁻u,w (Function.updateFinset x s u)*
      ((lmarginal μ s w (Function.updateFinset x s u))⁻¹*
        lmarginal μ s (fun y ↦ w y*F y) (Function.updateFinset x s u))
      ∂Measure.pi (fun i:s ↦ μ i))=_
  rw [he,lintegral_mul_const _ ((show Measurable (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)) from hw.comp (measurable_updateFinset (s:=s) (x:=x))))]
  change lmarginal μ s w x*((lmarginal μ s w x)⁻¹*lmarginal μ s (fun y ↦ w y*F y) x)=_
  by_cases hz : lmarginal μ s w x=0
  · have hwz : ∀ᵐu ∂Measure.pi (fun i:s ↦ μ i), w (Function.updateFinset x s u)=0 :=
      (lintegral_eq_zero_iff' ((show Measurable (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)) from hw.comp (measurable_updateFinset (s:=s) (x:=x)))).aemeasurable).mp hz
    have hb : lmarginal μ s (fun y ↦ w y*F y) x=0 :=
      lintegral_eq_zero_of_ae_eq_zero (hwz.mono fun u hu ↦ by simp [hu])
    rw [hz,hb,mul_zero,mul_zero]
  · rw [←mul_assoc,ENNReal.mul_inv_cancel hz hfin,one_mul]

lemma reference_fiber_positive (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] (s : Finset I) :
    ∀ᵐx ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ),
      0<partialNormalizer checks μ s (Finset.univ\s) x := by
  let w := checkWeight checks Finset.univ
  have hw : Measurable w := measurable_checkWeight checks _
  let A : Set (∀i,X i) := {x | lmarginal μ s w x=0}
  have hA : MeasurableSet A := measurableSet_eq_fun (hw.lmarginal μ) measurable_const
  let F : (∀i,X i)→ℝ≥0∞ := A.indicator (fun _ ↦ 1)
  have hF : Measurable F := measurable_const.indicator hA
  have he (x : ∀i,X i) (u : ∀i:s,X i) : F (Function.updateFinset x s u)=F x := by
    simp only [F,A,indicator_apply,mem_ofPred_eq,lmarginal_updateFinset]
  have hbound := local_mean_integrates checks μ s F hF 0 (by norm_num) (by
    intro x hx
    have hnum : lmarginal μ s (fun y ↦ w y*F y) x=0 := by
      change (∫⁻u,w (Function.updateFinset x s u)*F (Function.updateFinset x s u)
        ∂Measure.pi (fun i:s ↦ μ i))=0
      simp_rw [he]
      rw [lintegral_mul_const _ ((show Measurable (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)) from hw.comp (measurable_updateFinset (s:=s) (x:=x))))]
      change lmarginal μ s w x*F x=0
      by_cases ha : x∈A
      · rw [show lmarginal μ s w x=0 from ha,zero_mul]
      · rw [show F x=0 from indicator_of_notMem ha _,mul_zero]
    change lmarginal μ s (fun y ↦ w y*F y) x/lmarginal μ s w x≤0
    rw [hnum,ENNReal.zero_div])
  have hz : (conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ)) A=0 := by
    have h : (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))=0 :=
      le_antisymm hbound bot_le
    simpa only [F,lintegral_indicator_const hA,one_mul] using h
  have hae : ∀ᵐx ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ),x∉A := by
    exact measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hae] with x hx
  have hs : s∪(Finset.univ\s)=Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ s)
  simpa only [partialNormalizer,checkNormalizer,hs,pos_iff_ne_zero] using (show lmarginal μ s w x≠0 from hx)

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C R : Type*} [Fintype I] [DecidableEq I] [Fintype C] [Fintype R]
  {X Z : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]

def proposalEvent (checks : C→LocalCheck (fun i ↦ X i×Z i)) (s o : Finset I)
    (z : ∀i,Z i) : Set ((∀i,X i)×(∀i:s,X i×Z i)) :=
  {p | Function.updateFinset (fun i ↦ (p.1 i,z i)) s p.2∈retainedEvent checks (s∪o)}

omit [Fintype I] in
lemma measurable_proposalEvent (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (s o : Finset I) (z : ∀i,Z i) : MeasurableSet (proposalEvent checks s o z) := by
  apply (measurableSet_retainedEvent checks (s∪o)).preimage
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈s
  · simpa only [Function.updateFinset,dite_eq_left hi,Function.comp_def] using
      (measurable_pi_apply (⟨i,hi⟩:s)).comp (measurable_snd : Measurable (Prod.snd : (∀i,X i)×(∀i:s,X i×Z i)→_))
  · simpa only [Function.updateFinset,dite_eq_right hi,Function.comp_def] using
      (((measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst : (∀i,X i)×(∀i:s,X i×Z i)→_))).prodMk measurable_const)

def proposalKernel (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) : Kernel (∀i,X i) (∀i:s,X i×Z i) :=
  fiberNormalize (Kernel.const _ (Measure.pi fun i:s ↦ (μ i).compProd (κ i)))
    (proposalEvent checks s o z)

instance proposalKernel_finite (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) : IsFiniteKernel (proposalKernel checks μ κ s o z) :=
  inferInstanceAs (IsFiniteKernel (fiberNormalize _ _))

omit [Fintype I] in
lemma proposalKernel_apply (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) (x : ∀i,X i) :
    proposalKernel checks μ κ s o z x=proposalFiber checks μ κ s o x z := by
  change (fiberRestrict _ _ x univ)⁻¹ • fiberRestrict _ _ x=_
  rw [fiberRestrict_apply _ (measurable_proposalEvent checks s o z)]
  simp only [Kernel.const_apply,Measure.restrict_apply_univ,proposalFiber,conditionedMeasure]
  rfl

lemma full_primary_law (reference : R→LocalCheck X)
    (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s : Finset I) (z : ∀i,Z i)
    (hincl : ∀(y : ∀i,X i)(u : ∀i,Z i),
      checkWeight checks Finset.univ (fun i ↦ (y i,u i))≤checkWeight reference Finset.univ y) :
    ((conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ)).compProd
      (proposalKernel checks μ κ s (Finset.univ\s) z)).map
      (fun p ↦ Function.updateFinset p.1 s (fun i ↦ (p.2 i).1))=
    (conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ)).withDensity
      (fun x ↦ conditionalLikelihood reference checks μ κ s (Finset.univ\s) x z) := by
  let ξ := conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ)
  let η := fiberNormalize (Kernel.const _ (Measure.pi fun i:s ↦ μ i))
    (insertionFiberEvent reference s (Finset.univ\s))
  let π : (∀i:s,X i×Z i)→(∀i:s,X i) := fun p i ↦ (p i).1
  have hπ : Measurable π := Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i))
  let upd : (∀i,X i)×(∀i:s,X i)→(∀i,X i) := fun p ↦ Function.updateFinset p.1 s p.2
  have hu : Measurable upd := measurable_updateFinset'
  let L : (∀i,X i)→ℝ≥0∞ := fun x ↦ conditionalLikelihood reference checks μ κ s (Finset.univ\s) x z
  have hL : Measurable L := measurable_conditionalLikelihood reference checks μ κ s _ z
  have he : (ξ.compProd (proposalKernel checks μ κ s (Finset.univ\s) z)).map
      (fun p ↦ (p.1,π p.2))=(ξ.compProd η).withDensity (L∘upd) := by
    apply integrated_primary_density ξ _ η π hπ (L∘upd) (hL.comp hu)
    filter_upwards [reference_fiber_positive reference μ s] with x hx
    rw [proposalKernel_apply]
    have heq : η x=referenceFiber reference μ s (Finset.univ\s) x := by
      change (fiberRestrict _ _ x univ)⁻¹ • fiberRestrict _ _ x=_
      rw [fiberRestrict_apply _ (insertionFiberEvent_measurable reference s (Finset.univ\s))]
      simp only [Kernel.const_apply,Measure.restrict_apply_univ,referenceFiber,conditionedMeasure]
      rfl
    rw [heq]
    apply proposalFiber_primary checks reference μ κ s _ x z hx
    simpa only [Finset.union_sdiff_of_subset (Finset.subset_univ s)] using hincl
  have he' := congrArg (fun ν ↦ ν.map upd) he
  rw [Measure.map_map hu (show Measurable (fun p : (∀i,X i)×(∀i:s,X i×Z i) ↦ (p.1,π p.2)) from measurable_fst.prodMk (hπ.comp measurable_snd)),map_density_comp _ upd hu L hL] at he'
  change _=((insertedLaw reference μ s (Finset.univ\s) ξ).map upd).withDensity L at he'
  rw [reference_resample reference μ s] at he'
  exact he'

end HardSphere.Comparison

end
end

end

end OAI
