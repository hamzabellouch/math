import OAI.NumberTheory.DukePrimeDegree.Entropy.BilateralConditionalSupport
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalMapEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.StationaryFiberConditioning

namespace OAI

/-! # Conditional measurability from constancy on conull future fibers

Disintegration supplies the almost-everywhere factorization; no Borel
choice of a representative of every future fiber is needed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem condExp_eq_of_conull_fiber_constant
    {Y S : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F) (g : Y → ℝ) (hg : Integrable g μ)
    (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E, F x=F y → g x=g y) :
    μ[g | MeasurableSpace.comap F inferInstance] =ᵐ[μ] g := by
  let ν := condDistrib id F μ
  have hcomp : ν ∘ₘ (μ.map F)=μ := by
    simpa only [ν,Measure.map_id] using
      condDistrib_comp_map hF.aemeasurable aemeasurable_id
  have hgood : ∀ᵐ s ∂μ.map F, ∀ᵐ y ∂ν s, y ∈ E := by
    apply Measure.ae_ae_of_ae_comp
    rwa [hcomp]
  have hgx : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν (F x), y ∈ E :=
    ae_of_ae_map hF.aemeasurable hgood
  have hfx : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν (F x), F y=F x :=
    ae_of_ae_map hF.aemeasurable (ae_condDistrib_self_fiber μ F hF)
  have hc := condExp_ae_eq_integral_condDistrib_id hF hg
  filter_upwards [hc,hE,hgx,hfx] with x hx hxE hyE hyF
  rw [hx]
  calc
    (∫ y, g y ∂ν (F x)) = ∫ _, g x ∂ν (F x) := by
      apply integral_congr_ae
      filter_upwards [hyE,hyF] with y hy hyF
      exact (hconst x hxE y hy hyF.symm).symm
    _ = g x := by simp

/-- Once the actual kernel is constant on the complete future fibers,
the additional kernel label carries no conditional information. -/
theorem fiberConstant_kernel_information
    {Y S : Type*} [mY : MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hsupport : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E, F x=F y → κ x=κ y)
    (Q : Y → ℕ) (hQ : Measurable Q) :
    conditionalInformation μ Q (MeasurableSpace.comap F inferInstance) =ᵐ[μ]
      conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) := by
  let N := MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance
  have hN : N ≤ mY := (κ.measurable.prodMk hF).comap_le
  have hFN : MeasurableSpace.comap F inferInstance ≤ N :=
    (measurable_snd.comp (comap_measurable (fun x => (κ x,F x)))).comap_le
  let : MeasurableSpace Y := mY
  have hprob (a : ℕ) :
      μ[({x | Q x=a}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap F inferInstance] =ᵐ[μ]
      μ[({x | Q x=a}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap κ inferInstance] := by
    let A := {x | Q x=a}
    have hA : MeasurableSet A := hQ (measurableSet_singleton a)
    let g := fun x => (κ x).real A
    have hfix := condExp_eq_of_conull_fiber_constant μ F hF g
      (integrable_kernel_real μ κ hA) E hE
      (fun x hx y hy hxy => congrArg (fun ν : Measure Y => ν.real A)
        (hconst x hx y hy hxy))
    have hlabel := selfConstant_kernel_with_label_ae_eq_condExp
      μ κ F hF hstat hself hsupport hA
    have hroot := selfConstant_kernel_ae_eq_condExp μ κ hstat hself hA
    have htower := condExp_condExp_of_le (μ := μ)
      (f := A.indicator (fun _ => (1:ℝ))) hFN hN
    have hfuture : g =ᵐ[μ]
        μ[A.indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap F inferInstance] :=
      hfix.symm.trans ((condExp_congr_ae hlabel).trans htower)
    exact hfuture.symm.trans hroot
  filter_upwards [ae_all_iff.mpr hprob] with x hx
  exact congrArg (-Real.log ·) (hx (Q x))

end DukePrimeDegree

end

end OAI
