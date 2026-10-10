import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]

def parameterSuccessKernel (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) : Kernel E X where
  toFun e := (κ e (Prod.mk e ⁻¹' S))⁻¹ • (κ e).restrict (Prod.mk e ⁻¹' S)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    simp only [Measure.smul_apply,Measure.restrict_apply hB,smul_eq_mul]
    have hm := Kernel.measurable_kernel_prodMk_left (κ:=κ) hS
    have hi := Kernel.measurable_kernel_prodMk_left (κ:=κ)
      ((MeasurableSet.univ.prod hB).inter hS)
    apply hm.inv.mul
    convert hi using 1
    ext e
    congr 1
    ext x
    simp

lemma parameterSuccessKernel_apply (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) (e : E) :
    parameterSuccessKernel κ S hS e=
      (κ e (Prod.mk e ⁻¹' S))⁻¹ • (κ e).restrict (Prod.mk e ⁻¹' S) := rfl

lemma parameterSuccessKernel_mass_le (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) (e : E) :
    parameterSuccessKernel κ S hS e univ ≤ 1 := by
  simp only [parameterSuccessKernel_apply,Measure.smul_apply,
    Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

instance parameterSuccessKernel_finite (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) : IsFiniteKernel (parameterSuccessKernel κ S hS) :=
  ⟨1,by simp,parameterSuccessKernel_mass_le κ S hS⟩

lemma parameterSuccessKernel_mass (κ : Kernel E X) [IsFiniteKernel κ]
    (S : Set (E×X)) (hS : MeasurableSet S) {e : E}
    (h : 0 < κ e (Prod.mk e ⁻¹' S)) :
    parameterSuccessKernel κ S hS e univ=1 := by
  simp only [parameterSuccessKernel_apply,Measure.smul_apply,
    Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.ne' (measure_ne_top _ _)

lemma parameterSuccessKernel_markov (κ : Kernel E X) [IsFiniteKernel κ]
    (S : Set (E×X)) (hS : MeasurableSet S)
    (h : ∀e,0 < κ e (Prod.mk e ⁻¹' S)) :
    IsMarkovKernel (parameterSuccessKernel κ S hS) :=
  ⟨fun e ↦ ⟨parameterSuccessKernel_mass κ S hS (h e)⟩⟩

lemma parameterSuccessKernel_le (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) {e : E} {c : ℝ≥0∞}
    (hc : c ≤ κ e (Prod.mk e ⁻¹' S)) :
    parameterSuccessKernel κ S hS e ≤ c⁻¹ • κ e := by
  rw [parameterSuccessKernel_apply]
  intro B
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hc) (Measure.restrict_le_self B)

lemma parameterSuccessKernel_ac (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) (e : E) :
    parameterSuccessKernel κ S hS e ≪ κ e := by
  rw [parameterSuccessKernel_apply]
  exact Measure.smul_absolutelyContinuous.trans (Measure.restrict_le_self.absolutelyContinuous)

lemma parameterSuccessKernel_support (κ : Kernel E X) [IsFiniteKernel κ] (S : Set (E×X))
    (hS : MeasurableSet S) (e : E) :
    ∀ᵐx ∂parameterSuccessKernel κ S hS e,(e,x)∈S := by
  have hs : MeasurableSet (Prod.mk e ⁻¹' S) := hS.preimage measurable_prodMk_left
  rw [ae_iff]
  change parameterSuccessKernel κ S hS e (Prod.mk e ⁻¹' S)ᶜ=0
  simp [parameterSuccessKernel_apply,Measure.restrict_apply hs.compl]

end HardSphere.Comparison

namespace HardSphere.Comparison

lemma exists_bounded_auxiliary_kernel {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] (P : Measure X) [IsProbabilityMeasure P]
    (ρ : Measure (X×Z)) [IsProbabilityMeasure ρ] {G : ℝ≥0∞} (hG : G≠⊤)
    (hρ : ρ.fst≤G • P) :
    ∃ κ : Kernel X Z,IsFiniteKernel κ ∧ P.compProd κ=ρ ∧
      (∀x,κ x univ≤G) ∧ (∫⁻x,κ x univ ∂P)=1 := by
  have hac : ρ.fst ≪ P := (Measure.absolutelyContinuous_of_le hρ).trans Measure.smul_absolutelyContinuous
  have hbd : ∀ᵐx ∂P,ρ.fst.rnDeriv P x≤G := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (ρ.fst.measurable_rnDeriv P)
    intro S hS hSf
    simpa only [lintegral_const,Measure.restrict_apply_univ,smul_eq_mul,Measure.smul_apply]
      using (Measure.setLIntegral_rnDeriv_le (μ:=ρ.fst) (ν:=P) S).trans (hρ S)
  let f : X→ℝ≥0∞ := fun x ↦ min (ρ.fst.rnDeriv P x) G
  have hfm : Measurable f := (ρ.fst.measurable_rnDeriv P).min measurable_const
  have hfe : f=ᵐ[P]ρ.fst.rnDeriv P := hbd.mono (fun x hx ↦ min_eq_left hx)
  have hw : P.withDensity f=ρ.fst := (withDensity_congr_ae hfe).trans (Measure.withDensity_rnDeriv_eq _ _ hac)
  let κ := ρ.condKernel.withDensity (fun x _ ↦ f x)
  have hκ : IsFiniteKernel κ := Kernel.isFiniteKernel_withDensity_of_bounded _ hG (fun x _ ↦ min_le_right _ _)
  let _ := hκ
  have hκeq (x : X) : κ x=f x • ρ.condKernel x := by
    change ρ.condKernel.withDensity (fun (x : X) (_ : Z) ↦ f x) x = _
    rw [Kernel.withDensity_apply _ (show Measurable (Function.uncurry (fun (x : X) (_ : Z) ↦ f x)) from hfm.comp measurable_fst)]
    exact withDensity_const _
  have hmass (x : X) : κ x univ=f x := by rw [hκeq]; simp
  have hjoint : P.compProd κ=ρ := by
    rw [←ρ.disintegrate ρ.condKernel,←hw]
    ext S hS
    rw [Measure.compProd_apply hS,Measure.compProd_apply hS,
      lintegral_withDensity_eq_lintegral_mul _ hfm (Kernel.measurable_kernel_prodMk_left hS)]
    apply lintegral_congr
    intro x
    rw [hκeq,Measure.smul_apply,smul_eq_mul]
    rfl
  refine ⟨κ,hκ,hjoint,fun x ↦ ?_,?_⟩
  · rw [hmass]; exact min_le_right _ _
  · have hu := congrArg (fun μ : Measure (X×Z) ↦ μ univ) hjoint
    simpa only [Measure.compProd_apply MeasurableSet.univ,preimage_univ,measure_univ] using hu

lemma exists_parameter_auxiliary {E X Z : Type*} [MeasurableSpace E]
    [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace.CountableOrCountablyGenerated E X]
    [StandardBorelSpace Z] [Nonempty Z]
    (P : Kernel E X) [IsMarkovKernel P]
    (ρ : Kernel E (X×Z)) [IsMarkovKernel ρ]
    {G : ℝ≥0∞} (hG : G ≠ ⊤) (hρ : ∀e,ρ.fst e ≤ G • P e) :
    ∃ κ : Kernel (E×X) Z, IsFiniteKernel κ ∧ P.compProd κ=ρ ∧
      (∀e x,κ (e,x) univ ≤ G) ∧ (∀e,∫⁻x,κ (e,x) univ ∂P e=1) := by
  have hac (e : E) : ρ.fst e ≪ P e :=
    (Measure.absolutelyContinuous_of_le (hρ e)).trans Measure.smul_absolutelyContinuous
  have hbd (e : E) : ∀ᵐx ∂P e,ρ.fst.rnDeriv P e x ≤ G := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (ρ.fst.measurable_rnDeriv_right P e)
    intro S hS hSf
    simpa only [lintegral_const,Measure.restrict_apply_univ,smul_eq_mul,Measure.smul_apply]
      using (Kernel.setLIntegral_rnDeriv_le (κ:=ρ.fst) (η:=P) (a:=e) hS).trans (hρ e S)
  let f : E×X → ℝ≥0∞ := fun p ↦ min (ρ.fst.rnDeriv P p.1 p.2) G
  have hfm : Measurable f := (ρ.fst.measurable_rnDeriv P).min measurable_const
  have hw (e : E) : (P e).withDensity (fun x ↦ f (e,x))=ρ.fst e := by
    have hfe : (fun x ↦ f (e,x))=ᵐ[P e]ρ.fst.rnDeriv P e :=
      (hbd e).mono (fun x hx ↦ min_eq_left hx)
    rw [withDensity_congr_ae hfe]
    rw [←Kernel.withDensity_apply P (ρ.fst.measurable_rnDeriv P)]
    exact Kernel.withDensity_rnDeriv_eq (hac e)
  let κ := ρ.condKernel.withDensity (fun p (_ : Z) ↦ f p)
  have hκ : IsFiniteKernel κ := Kernel.isFiniteKernel_withDensity_of_bounded _ hG
    (fun p _ ↦ min_le_right _ _)
  let _ := hκ
  have hκeq (p : E×X) : κ p=f p • ρ.condKernel p := by
    change ρ.condKernel.withDensity (fun (p : E×X) (_ : Z) ↦ f p) p=_
    rw [Kernel.withDensity_apply _ (show Measurable (Function.uncurry (fun (p : E×X) (_ : Z) ↦ f p)) from hfm.comp measurable_fst)]
    exact withDensity_const _
  have hmass (p : E×X) : κ p univ=f p := by rw [hκeq];simp
  have hjoint : P.compProd κ=ρ := by
    rw [←ρ.disintegrate ρ.condKernel]
    apply Kernel.ext
    intro e
    ext S hS
    rw [Kernel.compProd_apply hS,Kernel.compProd_apply hS,←hw e]
    have hg : Measurable (fun x : X ↦ ρ.condKernel (e,x) (Prod.mk x ⁻¹' S)) :=
      Kernel.measurable_kernel_prodMk_left (κ:=ρ.condKernel.comap (fun x : X ↦ (e,x)) measurable_prodMk_left) hS
    rw [lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun x : X ↦ f (e,x)) from hfm.comp measurable_prodMk_left) hg]
    apply lintegral_congr
    intro x
    rw [hκeq,Measure.smul_apply,smul_eq_mul]
    rfl
  refine ⟨κ,hκ,hjoint,fun e x ↦ ?_,fun e ↦ ?_⟩
  · rw [hmass];exact min_le_right _ _
  · have hu := congrArg (fun η : Kernel E (X×Z) ↦ η e univ) hjoint
    simpa only [Kernel.compProd_apply MeasurableSet.univ,preimage_univ,measure_univ] using hu

end HardSphere.Comparison

end

end OAI
