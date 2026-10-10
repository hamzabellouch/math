import OAI.InformationTheory.Entanglement.PhysicalProductStep

namespace OAI

noncomputable section
open scoped TensorProduct InnerProductSpace MeasureTheory
open ContinuousLinearMap UniformSpace MeasureTheory Filter
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*} [MeasurableSpace X]

omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTensor_weak_measurable (F : X→HilbertTensor H K→L[ℂ]HilbertTensor H K)
    (hF : ∀ x y : H, ∀ u v : K,
      Measurable (fun z => inner ℂ (hilbertTmul x u) (F z (hilbertTmul y v)))) :
    ∀ x y : HilbertTensor H K, Measurable (fun z => inner ℂ x (F z y)) := by
  have hc (y : HilbertTensor H K) :
      IsClosed {x : HilbertTensor H K | Measurable (fun z => inner ℂ x (F z y))} := by
    apply IsSeqClosed.isClosed
    intro f x hf hlim
    apply measurable_of_tendsto_metrizable (fun n => hf n)
    apply tendsto_pi_nhds.mpr
    intro z
    exact hlim.inner tendsto_const_nhds
  have hr (x : HilbertTensor H K) :
      IsClosed {y : HilbertTensor H K | Measurable (fun z => inner ℂ x (F z y))} := by
    apply IsSeqClosed.isClosed
    intro f y hf hlim
    apply measurable_of_tendsto_metrizable (fun n => hf n)
    apply tendsto_pi_nhds.mpr
    intro z
    exact tendsto_const_nhds.inner ((F z).continuous.continuousAt.tendsto.comp hlim)
  have hleft (y : H) (v : K) (x : HilbertTensor H K) :
      Measurable (fun z => inner ℂ x (F z (hilbertTmul y v))) := by
    refine Completion.induction_on x (hc _) ?_
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => exact hF a y b v
    | add a b ha hb =>
      convert ha.add hb using 1
      ext z
      simp only [Pi.add_apply,Completion.coe_add,inner_add_left]
  intro x y
  refine Completion.induction_on y (hr x) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact hleft a b x
  | add a b ha hb =>
    convert ha.add hb using 1
    ext z
    simp only [Pi.add_apply,Completion.coe_add,map_add,inner_add_right]
lemma densityTensor_coefficient_measurable {ι κ : Type*}
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (ρ : X→DensityOperator b) (σ : X→DensityOperator c)
    (hρ : ∀ x y, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
    (hσ : ∀ u v, Measurable (fun z => inner ℂ u ((σ z).val.val v)))
    (x y : HilbertTensor H K) :
    Measurable (fun z => inner ℂ x ((densityTensor b c (ρ z) (σ z)).val.val y)) := by
  apply hilbertTensor_weak_measurable _ _ x y
  intro a a' u u'
  change Measurable (fun z => inner ℂ (hilbertTmul a u)
    (hilbertTensorMap (ρ z).val.val (σ z).val.val (hilbertTmul a' u')))
  simp only [hilbertTensorMap_tmul,hilbertTmul_inner]
  exact (hρ a a').mul (hσ u u')

end SecretKey

end

end OAI
