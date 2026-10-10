import Mathlib
import OAI.Analysis.HardSphere.Comparison.TaggedObserved

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {D Q X I : Type*} [MeasurableSpace D] [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def conditionalTagLikelihood (σ : Kernel D Q) (tag : Q→I)
    (L : (D×Q)×X→ℝ≥0∞) (E : Set D) (i : I) (z : D×X) : ℝ≥0∞ :=
  if z.1∈E then ∫⁻q,if tag q=i then L ((z.1,q),z.2) else 0 ∂σ z.1 else 0

lemma conditionalTagLikelihood_measurable (σ : Kernel D Q) [IsSFiniteKernel σ]
    (tag : Q→I) (ht : Measurable tag) (L : (D×Q)×X→ℝ≥0∞) (hL : Measurable L)
    (E : Set D) (hE : MeasurableSet E) (i : I) :
    Measurable (conditionalTagLikelihood σ tag L E i) := by
  apply Measurable.ite (hE.preimage measurable_fst) _ measurable_const
  exact (((hL.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).ite
    (measurableSet_eq_fun (ht.comp measurable_snd) measurable_const) measurable_const)).lintegral_kernel_prod_right'
      (κ:=σ.comap Prod.fst measurable_fst)

lemma conditionalTagLikelihood_sum (σ : Kernel D Q) (tag : Q→I) (ht : Measurable tag)
    (L : (D×Q)×X→ℝ≥0∞) (hL : Measurable L) (E : Set D) (z : D×X) :
    (∑i,conditionalTagLikelihood σ tag L E i z)=
      if z.1∈E then ∫⁻q,L ((z.1,q),z.2) ∂σ z.1 else 0 := by
  by_cases hz : z.1∈E
  · simp only [conditionalTagLikelihood,ite_eq_left hz]
    exact sum_tagLikelihood (σ z.1) tag ht _
      (hL.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) z.2
  · simp [conditionalTagLikelihood,hz]

lemma tagLikelihood_lintegral (σ : Measure Q) [SFinite σ] (P : Measure X) [SFinite P]
    (tag : Q→I) (ht : Measurable tag) (L : Q×X→ℝ≥0∞) (hL : Measurable L)
    (F : I×X→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻q,∫⁻x,L (q,x)*F (tag q,x) ∂P ∂σ)=
      ∑i,∫⁻x,tagLikelihood σ tag L i x*F (i,x) ∂P := by
  have H := congrArg (fun η : Measure (I×X) ↦ ∫⁻z,F z ∂η)
    (tagged_mixture_density σ P tag ht L hL)
  have hm : Measurable (fun p : Q×X ↦ (tag p.1,p.2)) := (ht.comp measurable_fst).prodMk measurable_snd
  rw [lintegral_map hF hm,
    lintegral_withDensity_eq_lintegral_mul _ hL
      (show Measurable (fun a : Q×X ↦ F (tag a.1,a.2)) from hF.comp hm),
    lintegral_withDensity_eq_lintegral_mul _
      (taggedFunction_measurable _ (tagLikelihood_measurable σ tag ht L hL)) hF] at H
  rw [lintegral_prod _ ((taggedFunction_measurable _ (tagLikelihood_measurable σ tag ht L hL)).mul hF).aemeasurable,
    lintegral_count,tsum_fintype] at H
  simp only [Pi.mul_apply] at H
  rw [lintegral_prod _ (show Measurable (fun a : Q×X ↦ L a*F (tag a.1,a.2)) from hL.mul (hF.comp hm)).aemeasurable] at H
  exact H

theorem conditionalTagged_density (μ : Measure D) [SFinite μ]
    (σ : Kernel D Q) [IsSFiniteKernel σ] (P : Kernel D X) [IsSFiniteKernel P]
    (χ : Kernel (D×Q) X) [IsSFiniteKernel χ]
    (tag : Q→I) (ht : Measurable tag) (L : (D×Q)×X→ℝ≥0∞) (hL : Measurable L)
    (E : Set D) (hE : MeasurableSet E)
    (hd : ∀ᵐd ∂μ.restrict E,∀ᵐq ∂σ d,χ (d,q)=(P d).withDensity (fun x ↦ L ((d,q),x))) :
    (((μ.restrict E).compProd (σ⊗ₖχ)).map (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2))))=
      (Measure.count.prod (μ.compProd P)).withDensity (fun z ↦ conditionalTagLikelihood σ tag L E z.1 z.2) := by
  let T : D×(Q×X)→I×(D×X) := fun z ↦ (tag z.2.1,(z.1,z.2.2))
  have hT : Measurable T := (ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk measurable_snd.snd)
  have hf := taggedFunction_measurable _ (conditionalTagLikelihood_measurable σ tag ht L hL E hE)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hT,
    lintegral_withDensity_eq_lintegral_mul _ hf hF,
    lintegral_prod _ (hf.mul hF).aemeasurable,lintegral_count,tsum_fintype,
    Measure.lintegral_compProd (show Measurable (fun a ↦ F (T a)) from hF.comp hT)]
  have hleft : (∫⁻d in E,∫⁻z,F (tag z.1,(d,z.2)) ∂(σ⊗ₖχ) d ∂μ)=
      ∫⁻d in E,∫⁻q,∫⁻x,L ((d,q),x)*F (tag q,(d,x)) ∂P d ∂σ d ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hd] with d hd'
    rw [Kernel.lintegral_compProd σ χ d (show Measurable (fun z : Q×X ↦ F (tag z.1,(d,z.2))) from hF.comp ((ht.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)))]
    apply lintegral_congr_ae
    filter_upwards [hd'] with q hq
    rw [hq,lintegral_withDensity_eq_lintegral_mul _ (show Measurable (fun x ↦ L ((d,q),x)) from hL.comp measurable_prodMk_left)
      (show Measurable (fun x ↦ F (tag q,(d,x))) from hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))]
    rfl
  change (∫⁻d in E,∫⁻z,F (tag z.1,(d,z.2)) ∂(σ⊗ₖχ) d ∂μ)=_
  rw [hleft]
  have hright (i : I) :
      (∫⁻z,conditionalTagLikelihood σ tag L E i z*F (i,z) ∂μ.compProd P)=
        ∫⁻d in E,∫⁻x,tagLikelihood (σ d) tag (fun qx ↦ L ((d,qx.1),qx.2)) i x*F (i,(d,x)) ∂P d ∂μ := by
    rw [Measure.lintegral_compProd (show Measurable (fun z : D×X ↦ conditionalTagLikelihood σ tag L E i z*F (i,z)) from
      (conditionalTagLikelihood_measurable σ tag ht L hL E hE i).mul (hF.comp measurable_prodMk_left))]
    rw [←lintegral_indicator hE]
    apply lintegral_congr
    intro d
    by_cases hd : d∈E <;> simp [conditionalTagLikelihood,hd,tagLikelihood]
  change _ = ∑i,∫⁻z,conditionalTagLikelihood σ tag L E i z*F (i,z) ∂μ.compProd P
  simp_rw [hright]
  rw [←lintegral_finsetSum]
  · apply lintegral_congr
    intro d
    exact tagLikelihood_lintegral (σ d) (P d) tag ht _
      (hL.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) _
      (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  · intro i _
    have hm : Measurable (fun z : D×X ↦
        tagLikelihood (σ z.1) tag (fun qx ↦ L ((z.1,qx.1),qx.2)) i z.2) := by
      exact (((hL.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).ite
        (measurableSet_eq_fun (ht.comp measurable_snd) measurable_const) measurable_const)).lintegral_kernel_prod_right'
          (κ:=σ.comap Prod.fst measurable_fst)
    exact (hm.mul (hF.comp measurable_prodMk_left)).lintegral_kernel_prod_right

end HardSphere.Comparison
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {D Q X I Y : Type*} [MeasurableSpace D] [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Y]

lemma tagged_density_of_ae_support (P : Measure X) (ν : Measure (I×X))
    (S : I→Set X) (hS : ∀i,MeasurableSet (S i)) (f : I→X→ℝ≥0∞)
    (hd : ν=(Measure.count.prod P).withDensity (fun p ↦ f p.1 p.2))
    (hs : ∀ᵐp ∂ν,p.2∈S p.1) :
    ν=(taggedReference P S).withDensity (fun p ↦ f p.1 p.2) := by
  rw [taggedReference,←restrict_withDensity (taggedEvent_measurable S hS),←hd]
  exact (Measure.restrict_eq_self_of_ae_mem hs).symm

lemma conditionalTagged_support (μ : Measure D) [SFinite μ]
    (σ : Kernel D Q) [IsSFiniteKernel σ] (χ : Kernel (D×Q) X) [IsSFiniteKernel χ]
    (tag : Q→I) (ht : Measurable tag) (E : Set D)
    (S : I→Set (D×X)) (hS : ∀i,MeasurableSet (S i))
    (hs : ∀ᵐd ∂μ.restrict E,∀ᵐq ∂σ d,∀ᵐw ∂χ (d,q),(d,w)∈S (tag q)) :
    ∀ᵐp ∂(((μ.restrict E).compProd (σ⊗ₖχ)).map (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2)))),p.2∈S p.1 := by
  have hm : Measurable (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2))) :=
    (ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk measurable_snd.snd)
  rw [ae_map_iff hm.aemeasurable (taggedEvent_measurable S hS)]
  apply Measure.ae_compProd_of_ae_ae ((taggedEvent_measurable S hS).preimage hm)
  filter_upwards [hs] with d hd
  exact Kernel.ae_compProd_of_ae_ae ((taggedEvent_measurable S hS).preimage
    ((ht.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))) hd

theorem tagged_observed_of_density (P : Measure X) [IsFiniteMeasure P]
    (ν : Measure (I×X)) (S : I→Set X) (hS : ∀i,MeasurableSet (S i))
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i))
    (hd : ν=(Measure.count.prod P).withDensity (fun p ↦ f p.1 p.2))
    (hs : ∀ᵐp ∂ν,p.2∈S p.1) (κ : Kernel (I×X) Y) [IsMarkovKernel κ]
    (C : ℝ) (hC : 0≤C) (hb : (∫⁻x,(∑i,f i x)^2 ∂P)≤ENNReal.ofReal C) :
    Integrable (fun y ↦ (((ν.compProd κ).map Prod.snd).rnDeriv
      (((taggedReference P S).compProd κ).map Prod.snd) y).toReal^2)
        (((taggedReference P S).compProd κ).map Prod.snd) ∧
    (∫y,(((ν.compProd κ).map Prod.snd).rnDeriv
      (((taggedReference P S).compProd κ).map Prod.snd) y).toReal^2
        ∂((taggedReference P S).compProd κ).map Prod.snd)≤C := by
  have he := tagged_density_of_ae_support P ν S hS f hd hs
  rw [he]
  let R := taggedReference P S
  let F : I×X→ℝ≥0∞ := fun p ↦ f p.1 p.2
  have hF : Measurable F := taggedFunction_measurable f hf
  let _ : IsFiniteMeasure R := by dsimp [R,taggedReference]; infer_instance
  have hm := tagged_density_moment P S f hf C hC hb
  have hsq : (∫⁻p,(F p)^2 ∂ R)≤ENNReal.ofReal C := (tagged_density_square P S f hf).trans hb
  let _ : IsFiniteMeasure (R.withDensity F) :=
    finite_density_of_square R F hF (ne_of_lt (hsq.trans_lt ENNReal.ofReal_lt_top))
  have hae : (fun p ↦ ((R.withDensity F).rnDeriv R p).toReal^2)=ᵐ[R]
      (fun p ↦ (F p).toReal^2) :=
    (Measure.rnDeriv_withDensity R hF).fun_comp (fun x : ℝ≥0∞ ↦ x.toReal^2)
  have h := observed_kernel_second_moment R (R.withDensity F)
    (withDensity_absolutelyContinuous _ _) κ (hm.1.congr hae.symm)
  refine ⟨h.1,h.2.trans ?_⟩
  rw [integral_congr_ae hae]
  exact hm.2

end HardSphere.Comparison
end
end

end OAI
