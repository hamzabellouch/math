import OAI.NumberTheory.DukePrimeDegree.Entropy.SelfConditionalKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformation

namespace OAI

/-! # Conditioning a stationary kernel on its actual fiber labels -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y S : Type*} [mY : MeasurableSpace Y] [MeasurableSpace S]

theorem fiberConstant_kernel_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hκF : @Measurable Y (Measure Y) (MeasurableSpace.comap F inferInstance)
      inferInstance κ)
    (hstat : μ.bind κ=μ)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap F inferInstance] := by
  have hm := hF.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) hm
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hA)
  · exact fun _ _ _ => (integrable_kernel_real μ κ hA).integrableOn
  · intro U hU _
    have hUm : MeasurableSet U := hm U hU
    obtain ⟨B,hB,rfl⟩ := hU
    have he : ∀ᵐ x ∂μ, (κ x).real (A ∩ (F ⁻¹' B)) =
        (F ⁻¹' B).indicator (fun x => (κ x).real A) x := by
      filter_upwards [hconst] with x hx
      by_cases hb : F x ∈ B
      · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' B from hb)]
        apply congrArg ENNReal.toReal
        apply measure_congr
        filter_upwards [hx] with y hy
        simp only [mem_inter_iff,mem_preimage,hy,hb,and_true]
      · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' B from hb)]
        have hz : (κ x) (A ∩ (F ⁻¹' B))=0 := by
          rw [←measure_empty (μ := κ x)]
          apply measure_congr
          filter_upwards [hx] with y hy
          simp only [mem_inter_iff,mem_preimage,hy,hb,and_false,mem_empty_iff_false]
        rw [Measure.real,hz,ENNReal.toReal_zero]
    calc
      (∫ x in F ⁻¹' B, (κ x).real A ∂μ) =
          ∫ x, (F ⁻¹' B).indicator (fun x => (κ x).real A) x ∂μ :=
        (integral_indicator hUm).symm
      _ = ∫ x, (κ x).real (A ∩ (F ⁻¹' B)) ∂μ :=
        integral_congr_ae (by
          filter_upwards [he] with x hx
          exact hx.symm)
      _ = (μ.bind κ).real (A ∩ (F ⁻¹' B)) :=
        (bind_kernel_real κ μ _ (hA.inter hUm)).symm
      _ = ∫ x in F ⁻¹' B, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [hstat,integral_indicator_const (1 : ℝ) hA]
        simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply hA]
  · exact ((Measure.measurable_coe hA).ennreal_toReal.comp hκF).stronglyMeasurable.aestronglyMeasurable

theorem selfConstant_kernel_with_label_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance] := by
  apply fiberConstant_kernel_ae_eq_condExp μ κ (fun x => (κ x,F x))
    (κ.measurable.prodMk hF) (measurable_fst.comp (comap_measurable _)) hstat
  · filter_upwards [hself,hconst] with x hs hc
    filter_upwards [hs,hc] with y hy hc
    exact Prod.ext hy hc
  · exact hA

theorem selfConstant_kernel_with_label_information
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    (Q : Y → ℕ) (hQ : Measurable Q) :
    conditionalInformation μ Q
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =ᵐ[μ]
      conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) := by
  have h (a : ℕ) :=
    (selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF hstat hself hconst
      (hQ (measurableSet_singleton a))).symm.trans
    (selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hQ (measurableSet_singleton a)))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact congrArg (-Real.log ·) (hx (Q x))

end DukePrimeDegree

end

end OAI
