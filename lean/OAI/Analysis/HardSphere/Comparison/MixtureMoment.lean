import Mathlib
import OAI.Analysis.HardSphere.Bridges.PairSubtype

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {Q X : Type*} [MeasurableSpace Q] [MeasurableSpace X]

lemma mixed_likelihood_square (σ : Measure Q) (P : Measure X) [SFinite σ] [SFinite P]
    (L : Q×X→ℝ≥0∞) (hL : Measurable L) :
    (∫⁻x,(∫⁻q,L (q,x) ∂σ)^2 ∂P)=
      ∫⁻q,∫⁻q',∫⁻x,L (q,x)*L (q',x) ∂P ∂σ ∂σ := by
  have hslice (x : X) : Measurable (fun q ↦ L (q,x)) := hL.comp measurable_prodMk_right
  have hs (x : X) : (∫⁻q,L (q,x) ∂σ)^2=
      ∫⁻q,∫⁻q',L (q,x)*L (q',x) ∂σ ∂σ := by
    simp_rw [lintegral_const_mul _ (hslice x)]
    rw [lintegral_mul_const _ (hslice x),pow_two]
  simp_rw [hs]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro q
    exact lintegral_lintegral_swap
      (show Measurable (Function.uncurry (fun x q' ↦ L (q,x)*L (q',x))) from
        ((hL.comp measurable_prodMk_left).comp measurable_fst).mul
          (hL.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
  · apply Measurable.aemeasurable
    change Measurable (fun p : X×Q ↦ ∫⁻q',L (p.2,p.1)*L (q',p.1) ∂σ)
    exact (show Measurable (fun p : (X×Q)×Q ↦ L (p.1.2,p.1.1)*L (p.2,p.1.1)) from
      (hL.comp (measurable_fst.snd.prodMk measurable_fst.fst)).mul
        (hL.comp (measurable_snd.prodMk measurable_fst.fst))).lintegral_prod_right'

lemma tag_likelihood_square {I : Type*} [Fintype I] (P : Measure X)
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) :
    (∑i,∫⁻x,(f i x)^2 ∂P)≤∫⁻x,(∑i,f i x)^2 ∂P := by
  rw [←lintegral_finsetSum _ (fun i _ ↦ (hf i).pow_const 2)]
  apply lintegral_mono
  intro x
  dsimp only
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [pow_two]
  exact mul_le_mul' (le_refl _) ((show f i x ≤ ∑j,f j x from Finset.single_le_sum (f:=fun j ↦ f j x) (fun j _ ↦ bot_le) (Finset.mem_univ i)))

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma observed_second_moment (P ν : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure ν]
    (hac : ν≪P) (f : X→Y) (hf : Measurable f)
    (hi : Integrable (fun x ↦ (ν.rnDeriv P x).toReal^2) P) :
    Integrable (fun y ↦ ((ν.map f).rnDeriv (P.map f) y).toReal^2) (P.map f) ∧
    (∫y,((ν.map f).rnDeriv (P.map f) y).toReal^2 ∂P.map f)≤
      ∫x,(ν.rnDeriv P x).toReal^2 ∂P := by
  let g : X→ℝ := fun x ↦ (ν.rnDeriv P x).toReal
  let h : Y→ℝ := fun y ↦ ((ν.map f).rnDeriv (P.map f) y).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hh : Measurable h := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have he : h∘f=ᵐ[P] P[g|MeasurableSpace.comap f inferInstance] := toReal_rnDeriv_map hac hf
  have hl2 : MemLp g 2 P := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hi
  have hc : MemLp (P[g|MeasurableSpace.comap f inferInstance]) 2 P := hl2.condExp (by norm_num)
  have hci : Integrable (fun x ↦ (P[g|MeasurableSpace.comap f inferInstance] x)^2) P :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mp hc
  have hcomp : Integrable (fun x ↦ h (f x)^2) P := hci.congr (he.symm.fun_comp (fun x : ℝ ↦ x^2))
  constructor
  · exact (integrable_map_measure (hh.pow_const 2).aestronglyMeasurable hf.aemeasurable).mpr hcomp
  · change (∫y,h y^2 ∂P.map f)≤_
    rw [integral_map hf.aemeasurable (hh.pow_const 2).aestronglyMeasurable]
    calc
      _ = ∫x,(P[g|MeasurableSpace.comap f inferInstance] x)^2 ∂P :=
        integral_congr_ae (he.fun_comp (fun x : ℝ ↦ x^2))
      _ ≤ ∫x,g x^2 ∂P := by
        have hni : Integrable (fun x ↦ ‖g x‖^(2:ℝ)) P := by
          simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hi
        have hineq := integral_norm_condExp_rpow_le (m:=MeasurableSpace.comap f inferInstance)
          (by norm_num : (1:ℝ)≤2) hni
        simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hineq

lemma observed_kernel_second_moment (P ν : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure ν]
    (hac : ν≪P) (κ : Kernel X Y) [IsMarkovKernel κ]
    (hi : Integrable (fun x ↦ (ν.rnDeriv P x).toReal^2) P) :
    Integrable (fun y ↦ (((ν.compProd κ).map Prod.snd).rnDeriv
      ((P.compProd κ).map Prod.snd) y).toReal^2) ((P.compProd κ).map Prod.snd) ∧
    (∫y,(((ν.compProd κ).map Prod.snd).rnDeriv
      ((P.compProd κ).map Prod.snd) y).toReal^2 ∂(P.compProd κ).map Prod.snd)≤
      ∫x,(ν.rnDeriv P x).toReal^2 ∂P := by
  have hf : (P.compProd κ).map Prod.fst=P := Measure.fst_compProd P κ
  have hm : Measurable (fun x ↦ (ν.rnDeriv P x).toReal^2) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.pow_const _
  have hi' : Integrable (fun p : X×Y ↦ (ν.rnDeriv P p.1).toReal^2) (P.compProd κ) := by
    apply (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [hf]
  have he : (fun p : X×Y ↦ ((ν.compProd κ).rnDeriv (P.compProd κ) p).toReal^2)=ᵐ[P.compProd κ]
      (fun p ↦ (ν.rnDeriv P p.1).toReal^2) :=
    (rnDeriv_measure_compProd_left ν P κ).fun_comp (fun t : ℝ≥0∞ ↦ t.toReal^2)
  have h := observed_second_moment (P.compProd κ) (ν.compProd κ) (hac.compProd_left κ)
    Prod.snd measurable_snd (hi'.congr he.symm)
  refine ⟨h.1,h.2.trans_eq ?_⟩
  rw [integral_congr_ae he,←integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable,hf]

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]

lemma pairedFactor_swap (μ : Measure U) [SFinite μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (pairedFactor μ κ η S T hS hT).map (Prod.map id Prod.swap)=
      pairedFactor μ η κ T S hT hS := by
  unfold pairedFactor
  rw [←Measure.compProd_map measurable_swap]
  congr 1
  ext u B hB
  rw [Kernel.map_apply _ measurable_swap u,Kernel.prod_apply,Kernel.prod_apply]
  exact congrArg (fun m : Measure (Y×X) ↦ m B) Measure.prod_swap

lemma supportedPair_swap (ρ : Measure (X×Y)) {S : Set X} {T : Set Y}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hρ : ∀ᵐp ∂ρ,p.1∈S ∧ p.2∈T) :
    (supportedPair ρ S T).map Prod.swap=supportedPair (ρ.map Prod.swap) T S := by
  apply ((MeasurableEmbedding.subtype_coe hT).prodMap (MeasurableEmbedding.subtype_coe hS)).map_injective
  have hr : ∀ᵐp ∂ρ.map Prod.swap,p.1∈T ∧ p.2∈S := by
    apply (ae_map_iff measurable_swap.aemeasurable (by measurability)).mpr
    exact hρ.mono (fun _ hp ↦ hp.symm)
  rw [supportedPair_map _ hT hS hr,Measure.map_map (by fun_prop) measurable_swap]
  have he := congrArg (fun μ : Measure (X×Y) ↦ μ.map Prod.swap) (supportedPair_map ρ hS hT hρ)
  rw [Measure.map_map measurable_swap (by fun_prop)] at he
  exact he
end HardSphere.Comparison
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

instance targetUniform_finite (A : Set Point) : IsFiniteMeasure (targetUniform A) := by
  constructor
  change ((volume A)⁻¹ • volume.restrict A) univ<⊤
  rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact (ENNReal.inv_mul_le_one _).trans_lt (by simp)

lemma pairedPathsRaw_eq (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    pairedPathsRaw t y z y' z' A S T hS hT=
      (pairedFactor (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT).map Prod.snd := by
  unfold pairedPathsRaw pairedTrialLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma pairedPathsRaw_support (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐp ∂pairedPathsRaw t y z y' z' A S T hS hT,p.1∈S ∧ p.2∈T := by
  rw [pairedPathsRaw_eq]
  apply (ae_map_iff measurable_snd.aemeasurable (by measurability)).mpr
  exact pairedFactor_support _ _ _ _ _ _ _

lemma pairedPathsRaw_swap (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (pairedPathsRaw t y z y' z' A S T hS hT).map Prod.swap=
      pairedPathsRaw t y' z' y z A T S hT hS := by
  rw [pairedPathsRaw_eq,pairedPathsRaw_eq]
  rw [←pairedFactor_swap (targetUniform A) (trialKernel t y z) (trialKernel t y' z') S T hS hT,
    Measure.map_map measurable_snd (by fun_prop),Measure.map_map measurable_swap measurable_snd]
  rfl

lemma pairedPathsOn_swap (t : ℝ) (y z y' z' : Point) (A : Set Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (pairedPathsOn t y z y' z' A S T hS hT).map Prod.swap=
      pairedPathsOn t y' z' y z A T S hT hS := by
  unfold pairedPathsOn
  rw [supportedPair_swap _ hS hT (pairedPathsRaw_support t y z y' z' A S T hS hT),
    pairedPathsRaw_swap]

end HardSphere.Bridge

end
end

end

end OAI
