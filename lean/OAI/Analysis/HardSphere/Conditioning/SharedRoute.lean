import Mathlib
import OAI.Analysis.HardSphere.Bridges.PrimaryObserved

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge
attribute [local instance] Classical.propDecidable

lemma fiberNormalize_apply_measure {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]
    (κ : Kernel E X) [IsSFiniteKernel κ] (A : Set (E×X)) (hA : MeasurableSet A) (e : E) :
    fiberNormalize κ A e=conditionedMeasure (κ e) (Prod.mk e ⁻¹' A) := by
  change (fiberRestrict _ _ e univ)⁻¹ • fiberRestrict _ _ e=_
  rw [fiberRestrict_apply _ hA]
  simp only [Measure.restrict_apply_univ,conditionedMeasure]
  rfl

variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

def ambientFirst (s : Finset I) (σ : Equiv.Perm I)
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) : ∀i,X i :=
  Function.updateFinset p.1 s (fun i ↦ (p.2 i).1)

def ambientSecond (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) : ∀i,X i :=
  Function.updateFinset p.1 s (fun i ↦ (reverseSelected σ s hf p.2 i).1)

omit [Fintype I] in
lemma ambientFirst_measurable (s : Finset I) (σ : Equiv.Perm I) :
    Measurable (ambientFirst (X:=X) s σ) :=
  measurable_updateFinset'.comp (measurable_fst.prodMk
    (Measurable.of_eval (fun i ↦ measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))))

omit [Fintype I] in
lemma ambientSecond_measurable (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i) :
    Measurable (ambientSecond (X:=X) s σ hf) :=
  measurable_updateFinset'.comp (measurable_fst.prodMk
    (Measurable.of_eval (fun i ↦ measurable_fst.comp ((measurable_pi_apply i).comp
      ((reverseSelected σ s hf).measurable.comp measurable_snd)))))

def ambientRefreshEvent (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (A : Set (E×(∀i,X i))) : Set ((E×(∀i,X i))×(∀i:s,X i×X (σ.symm i))) :=
  {p | (p.1.1,ambientFirst s σ (p.1.2,p.2))∈A ∧
       (p.1.1,ambientSecond s σ hf (p.1.2,p.2))∈A}

omit [Fintype I] in
lemma ambientRefreshEvent_measurable (s : Finset I) (σ : Equiv.Perm I)
    (hf : ∀i,i∉s→σ i=i) (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) :
    MeasurableSet (ambientRefreshEvent s σ hf A) := by
  exact (hA.preimage (measurable_fst.fst.prodMk ((ambientFirst_measurable s σ).comp
    (measurable_fst.snd.prodMk measurable_snd)))).inter
    (hA.preimage (measurable_fst.fst.prodMk ((ambientSecond_measurable s σ hf).comp
      (measurable_fst.snd.prodMk measurable_snd))))

def ambientRefreshKernel (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : Kernel (E×(∀i,X i)) (∀i:s,X i×X (σ.symm i)) :=
  fiberNormalize ((finiteKernelPi ρ).comap Prod.fst measurable_fst) (ambientRefreshEvent s σ hf A)

instance ambientRefreshKernel_finite (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : IsFiniteKernel (ambientRefreshKernel s σ hf ρ A) := by
  unfold ambientRefreshKernel
  infer_instance

omit [Fintype I] in
lemma ambientRefreshKernel_apply (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E) (x : ∀i,X i) :
    ambientRefreshKernel s σ hf ρ A (e,x)=
      conditionedMeasure (Measure.pi fun i ↦ ρ i e)
        {p | (e,ambientFirst s σ (x,p))∈A ∧ (e,ambientSecond s σ hf (x,p))∈A} := by
  rw [ambientRefreshKernel,fiberNormalize_apply_measure _ _ (ambientRefreshEvent_measurable s σ hf A hA),
    Kernel.comap_apply,finiteKernelPi_apply]
  rfl

def ambientSharedKernel (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : Kernel E ((∀i,X i)×(∀i:s,X i×X (σ.symm i))) :=
  ξ ⊗ₖ ambientRefreshKernel s σ hf ρ A

instance ambientSharedKernel_finite (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) : IsFiniteKernel (ambientSharedKernel s σ hf ξ ρ A) := by
  unfold ambientSharedKernel
  infer_instance

omit [Fintype I] in
lemma ambientSharedKernel_mass (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E)
    (hp : ∀ᵐx ∂ξ e,0<(Measure.pi fun i ↦ ρ i e)
      {p | (e,ambientFirst s σ (x,p))∈A ∧ (e,ambientSecond s σ hf (x,p))∈A}) :
    ambientSharedKernel s σ hf ξ ρ A e univ=ξ e univ := by
  rw [ambientSharedKernel,Kernel.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  calc
    _ = ∫⁻_x,1 ∂ξ e := by
      apply lintegral_congr_ae
      filter_upwards [hp] with x hx
      apply fiberNormalize_mass _ (ambientRefreshEvent_measurable s σ hf A hA)
      simpa only [Kernel.comap_apply,finiteKernelPi_apply,ambientRefreshEvent,mem_ofPred_eq] using hx
    _ = _ := by simp

lemma ambientSharedKernel_support (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E)
    (B : ∀i:s,Set (X i×X (σ.symm i))) (hB : ∀i,MeasurableSet (B i))
    (hρ : ∀i,∀ᵐp ∂ρ i e,p∈B i) :
    ∀ᵐp ∂ambientSharedKernel s σ hf ξ ρ A e,∀i,p.2 i∈B i := by
  have hm : ∀ᵐp ∂Measure.pi (fun i ↦ ρ i e),∀i,p i∈B i := by
    rw [ae_all_iff]
    exact fun i ↦ (Measure.quasiMeasurePreserving_eval (fun j ↦ ρ j e) i).ae (hρ i)
  have hS : MeasurableSet {p : (∀i,X i)×(∀i:s,X i×X (σ.symm i)) | ∀i,p.2 i∈B i} := by
    convert MeasurableSet.iInter (fun i ↦ (hB i).preimage ((measurable_pi_apply i).comp
      (measurable_snd : Measurable (Prod.snd : (∀i,X i)×(∀i:s,X i×X (σ.symm i))→_)))) using 1
    ext p
    simp only [mem_ofPred_eq,mem_iInter,mem_preimage,Function.comp_apply]
  apply Kernel.ae_compProd_of_ae_ae hS
  apply ae_of_all
  intro x
  apply (fiberNormalize_ac _ (ambientRefreshEvent_measurable s σ hf A hA) (e,x)).ae_le
  simp only [Kernel.comap_apply,finiteKernelPi_apply]
  simp only [Filter.Eventually] at hm ⊢
  convert hm using 1

theorem ambient_common_observation {Y : Type*} [MeasurableSpace Y] [MeasurableEq Y]
    (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E)
    (mid : ∀i,X i→Y) (hmid : ∀i,Measurable (mid i))
    (hp : ∀i:s,∀ᵐp ∂ρ i e,mid i p.1=mid (σ.symm i) p.2)
    (star a b : I) (hsa : σ star=a) (hbs : σ b=star) :
    (ambientSharedKernel s σ hf ξ ρ A e).map
      (primaryFirstObservation σ star a b mid ∘ ambientFirst s σ)=
    (ambientSharedKernel s σ hf ξ ρ A e).map
      (primarySecondObservation star b mid ∘ ambientSecond s σ hf) := by
  apply Measure.map_congr
  have h := ambientSharedKernel_support s σ hf ξ ρ A hA e
    (fun i ↦ {p | mid i p.1=mid (σ.symm i) p.2})
    (fun i ↦ measurableSet_eq_fun ((hmid i).comp measurable_fst) ((hmid _).comp measurable_snd)) hp
  filter_upwards [h] with p hp
  exact primary_observations_eq σ s hf mid p.1 p.2 hp star a b hsa hbs

end HardSphere.Comparison
end
end

end OAI
