import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {U X Y : Type*} [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]

def successKernel (κ : Kernel U X) (S : Set X) (hS : MeasurableSet S) : Kernel U X where
  toFun u := (κ u S)⁻¹ • (κ u).restrict S
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    simp only [Measure.smul_apply,Measure.restrict_apply hB,smul_eq_mul]
    exact (κ.measurable_coe hS).inv.mul (κ.measurable_coe (hB.inter hS))

lemma successKernel_apply (κ : Kernel U X) (S : Set X) (hS : MeasurableSet S) (u : U) :
    successKernel κ S hS u=(κ u S)⁻¹ • (κ u).restrict S := rfl

lemma successKernel_mass_le (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S) (u : U) :
    successKernel κ S hS u univ ≤ 1 := by
  simp only [successKernel_apply,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

instance successKernel_finite (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S) :
    IsFiniteKernel (successKernel κ S hS) := ⟨1,by simp,successKernel_mass_le κ S hS⟩

lemma successKernel_mass (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {u : U} (h : 0<κ u S) : successKernel κ S hS u univ=1 := by
  simp only [successKernel_apply,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.ne' (measure_ne_top _ _)

lemma successKernel_le (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {u : U} {c : ℝ≥0∞} (hc : c ≤ κ u S) :
    successKernel κ S hS u ≤ c⁻¹ • κ u := by
  rw [successKernel_apply]
  intro B
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hc) (Measure.restrict_le_self B)

lemma successKernel_support (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S) (u : U) :
    ∀ᵐ x ∂successKernel κ S hS u,x∈S := by
  rw [ae_iff]
  change successKernel κ S hS u Sᶜ=0
  simp [successKernel_apply,Measure.restrict_apply hS.compl]

def pairedFactor (μ : Measure U) (κ : Kernel U X) (η : Kernel U Y)
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    [IsFiniteKernel κ] [IsFiniteKernel η] : Measure (U×(X×Y)) :=
  μ.compProd ((successKernel κ S hS).prod (successKernel η T hT))

lemma pairedFactor_mass (μ : Measure U) [IsProbabilityMeasure μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐ u ∂μ,0<κ u S) (hη : ∀ᵐ u ∂μ,0<η u T) :
    pairedFactor μ κ η S T hS hT univ=1 := by
  rw [pairedFactor,Measure.compProd_apply MeasurableSet.univ]
  have hea : (fun u ↦ ((successKernel κ S hS).prod (successKernel η T hT)) u
      ((fun p : X×Y ↦ (u,p))⁻¹' univ))=ᵐ[μ] fun _ ↦ 1 := by
    filter_upwards [hκ,hη] with u hu hv
    simp only [preimage_univ,Kernel.prod_apply]
    rw [show (Set.univ : Set (X×Y))=(Set.univ:Set X)×ˢ(Set.univ:Set Y) from Set.univ_prod_univ.symm,
      Measure.prod_prod,successKernel_mass κ S hS hu,successKernel_mass η T hT hv,one_mul]
  rw [lintegral_congr_ae hea]
  simp

lemma pairedFactor_fst (μ : Measure U) [SFinite μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hη : ∀ᵐ u ∂μ,0<η u T) :
    (pairedFactor μ κ η S T hS hT).map (fun p ↦ (p.1,p.2.1))=
      μ.compProd (successKernel κ S hS) := by
  have hm : Measurable (fun p : U×(X×Y) ↦ (p.1,p.2.1)) := by fun_prop
  ext B hB
  rw [Measure.map_apply hm hB,
    pairedFactor,Measure.compProd_apply (hB.preimage hm),
    Measure.compProd_apply hB]
  apply lintegral_congr_ae
  filter_upwards [hη] with u hu
  rw [Kernel.prod_apply]
  have he : (fun p : X×Y ↦ (u,p))⁻¹' ((fun p : U×(X×Y) ↦ (p.1,p.2.1))⁻¹' B)=
      ((fun x : X ↦ (u,x))⁻¹' B)×ˢ(univ : Set Y) := by ext p; simp
  rw [he,Measure.prod_prod,successKernel_mass η T hT hu,mul_one]

lemma pairedFactor_snd (μ : Measure U) [SFinite μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐ u ∂μ,0<κ u S) :
    (pairedFactor μ κ η S T hS hT).map (fun p ↦ (p.1,p.2.2))=
      μ.compProd (successKernel η T hT) := by
  have hm : Measurable (fun p : U×(X×Y) ↦ (p.1,p.2.2)) := by fun_prop
  ext B hB
  rw [Measure.map_apply hm hB,
    pairedFactor,Measure.compProd_apply (hB.preimage hm),
    Measure.compProd_apply hB]
  apply lintegral_congr_ae
  filter_upwards [hκ] with u hu
  rw [Kernel.prod_apply]
  have he : (fun p : X×Y ↦ (u,p))⁻¹' ((fun p : U×(X×Y) ↦ (p.1,p.2.2))⁻¹' B)=
      (univ : Set X)×ˢ((fun y : Y ↦ (u,y))⁻¹' B) := by ext p; simp
  rw [he,Measure.prod_prod,successKernel_mass κ S hS hu,one_mul]

lemma pairedFactor_support (μ : Measure U) [SFinite μ]
    (κ : Kernel U X) (η : Kernel U Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐ p ∂pairedFactor μ κ η S T hS hT,p.2.1∈S ∧ p.2.2∈T := by
  rw [pairedFactor,Measure.ae_compProd_iff (by measurability)]
  exact ae_of_all _ (fun u ↦ by
    rw [Kernel.prod_apply]
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [successKernel_support κ S hS u] with x hx
    filter_upwards [successKernel_support η T hT u] with y hy
    exact ⟨hx,hy⟩)

lemma successKernel_absolutelyContinuous (κ : Kernel U X) (S : Set X)
    (hS : MeasurableSet S) (u : U) : successKernel κ S hS u ≪ κ u := by
  rw [successKernel_apply]
  exact Measure.smul_absolutelyContinuous.trans (Measure.restrict_le_self.absolutelyContinuous)

lemma pairedFactor_midpoint {E : Type*} [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure U) [SFinite μ] (κ : Kernel U X) (η : Kernel U Y)
    [IsFiniteKernel κ] [IsFiniteKernel η] (π : X→E) (σ : Y→E) (uval : U→E)
    (hπ : Measurable π) (hσ : Measurable σ) (huval : Measurable uval)
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀ᵐ u ∂μ,∀ᵐ x ∂κ u,π x=uval u)
    (hη : ∀ᵐ u ∂μ,∀ᵐ y ∂η u,σ y=uval u) :
    ∀ᵐ p ∂pairedFactor μ κ η S T hS hT,π p.2.1=uval p.1 ∧ σ p.2.2=uval p.1 := by
  rw [pairedFactor,Measure.ae_compProd_iff (by measurability)]
  filter_upwards [hκ,hη] with u hu hv
  rw [Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [(successKernel_absolutelyContinuous κ S hS u).ae_le hu] with x hx
  filter_upwards [(successKernel_absolutelyContinuous η T hT u).ae_le hv] with y hy
  exact ⟨hx,hy⟩

end HardSphere.Comparison

end
end

end

end OAI
