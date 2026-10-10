import Mathlib
import OAI.Analysis.HardSphere.Conditioning.SymmetricTag

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {D X Y : Type*} [MeasurableSpace D] [MeasurableSpace X] [MeasurableSpace Y]

def retainedObserver (κ : Kernel (D×X) Y) : Kernel (D×X) (D×Y) :=
  (Kernel.deterministic Prod.fst measurable_fst) ×ₖ κ
instance retainedObserver_markov (κ : Kernel (D×X) Y) [IsMarkovKernel κ] :
    IsMarkovKernel (retainedObserver κ) := by unfold retainedObserver; infer_instance

lemma retainedObserver_apply (κ : Kernel (D×X) Y) [IsSFiniteKernel κ] (z : D×X) :
    retainedObserver κ z=(κ z).map (Prod.mk z.1) := by
  rw [retainedObserver,Kernel.prod_apply,Kernel.deterministic_apply,Measure.dirac_prod]

theorem retainedObserver_compProd (μ : Measure D) [SFinite μ]
    (χ : Kernel D X) [IsSFiniteKernel χ] (κ : Kernel (D×X) Y) [IsSFiniteKernel κ] :
    retainedObserver κ ∘ₘ (μ.compProd χ)=μ.compProd (χ⊗ₖκ).snd := by
  ext A hA
  rw [Measure.bind_apply hA (retainedObserver κ).aemeasurable,
    Measure.lintegral_compProd ((retainedObserver κ).measurable_coe hA),Measure.compProd_apply hA]
  apply lintegral_congr
  intro d
  rw [Kernel.snd_apply' _ _ (hA.preimage measurable_prodMk_left),Kernel.compProd_apply]
  · apply lintegral_congr
    intro w
    rw [retainedObserver_apply,Measure.map_apply measurable_prodMk_left hA]
    rfl
  · exact (hA.preimage measurable_prodMk_left).preimage measurable_snd

variable {Q I W : Type*} [MeasurableSpace Q] [MeasurableSpace I] [MeasurableSpace W]

lemma conditional_tag_observation (μ : Measure D) [SFinite μ]
    (σ : Kernel D Q) [IsSFiniteKernel σ] (χ : Kernel (D×Q) X) [IsSFiniteKernel χ]
    (tag : Q→I) (ht : Measurable tag) (obs : Kernel (I×(D×X)) Y) [IsSFiniteKernel obs] :
    ((Kernel.deterministic (fun z : I×(D×X) ↦ z.2.1) measurable_snd.fst) ×ₖ obs) ∘ₘ
      (((μ.compProd (σ⊗ₖχ)).map (fun z ↦ (tag z.2.1,(z.1,z.2.2))))) =
    μ.compProd (((σ⊗ₖχ)⊗ₖ(obs.comap (fun z ↦ (tag z.2.1,(z.1,z.2.2)))
      ((ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk measurable_snd.snd)))).snd) := by
  have hm : Measurable (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2))) :=
    (ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk measurable_snd.snd)
  rw [←comp_comap_map _ _ hm]
  have he : (((Kernel.deterministic (fun z : I×(D×X) ↦ z.2.1) measurable_snd.fst) ×ₖ obs).comap
      (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2))) hm)=
      retainedObserver (obs.comap (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2))) hm) := by
    ext z A hA
    simp only [Kernel.comap_apply, retainedObserver, Kernel.prod_apply, Kernel.deterministic_apply]
  rw [he,retainedObserver_compProd]

lemma conditional_observation_map (σ : Kernel D Q) [IsSFiniteKernel σ]
    (ψ : Kernel (D×Q) W) [IsSFiniteKernel ψ] (v : W→X) (hv : Measurable v)
    (tag : Q→I) (ht : Measurable tag) (obs : Kernel (I×(D×X)) Y) [IsSFiniteKernel obs] :
    (((σ⊗ₖψ.map v)⊗ₖobs.comap (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2)))
      ((ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk measurable_snd.snd))).snd)=
    (((σ⊗ₖψ)⊗ₖobs.comap (fun z : D×(Q×W) ↦ (tag z.2.1,(z.1,v z.2.2)))
      ((ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk (hv.comp measurable_snd.snd)))).snd) := by
  ext d A hA
  rw [Kernel.snd_apply' _ _ hA,Kernel.snd_apply' _ _ hA,
    Kernel.compProd_apply (measurable_snd hA),Kernel.compProd_apply (measurable_snd hA)]
  have hleft : Measurable (fun z : Q×X ↦ obs (tag z.1,(d,z.2)) A) :=
    (obs.measurable_coe hA).comp ((ht.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have hright : Measurable (fun z : Q×W ↦ obs (tag z.1,(d,v z.2)) A) :=
    (obs.measurable_coe hA).comp ((ht.comp measurable_fst).prodMk (measurable_const.prodMk (hv.comp measurable_snd)))
  change (∫⁻z,obs (tag z.1,(d,z.2)) A ∂(σ⊗ₖψ.map v) d)=
    ∫⁻z,obs (tag z.1,(d,v z.2)) A ∂(σ⊗ₖψ) d
  rw [Kernel.lintegral_compProd σ (ψ.map v) d hleft,Kernel.lintegral_compProd σ ψ d hright]
  apply lintegral_congr
  intro q
  rw [Kernel.map_apply _ hv]
  change (∫⁻ c, obs (tag q,(d,c)) A ∂Measure.map v (ψ (d,q))) =
    ∫⁻ c, obs (tag q,(d,v c)) A ∂ψ (d,q)
  exact lintegral_map (hleft.comp (measurable_prodMk_left (x:=q))) hv

end HardSphere.Comparison
end
end

end OAI
