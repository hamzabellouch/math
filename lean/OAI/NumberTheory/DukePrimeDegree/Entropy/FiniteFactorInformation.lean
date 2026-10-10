import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformation

namespace OAI

/-! # Finite conditional entropy under a countable recoding -/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalInformation_fintype_integrable_integral
    {Y α : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [Nonempty α]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (P : Y → α) (hP : Measurable P) (hm : m ≤ mY) :
    Integrable (conditionalInformation μ P m) μ ∧
      (∫ x, conditionalInformation μ P m x ∂μ)=conditionalSigmaEntropy μ P m := by
  let e := Fintype.equivFin α
  let : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  have he : Measurable e := measurable_of_countable e
  have H := conditionalInformation_integrable_integral m μ (e ∘ P) (he.comp hP) hm
  have hi : conditionalInformation μ (e ∘ P) m=conditionalInformation μ P m := by
    funext x
    unfold conditionalInformation
    have hs : {z | (e ∘ P) z=(e ∘ P) x}={z | P z=P x} := by
      ext z
      exact e.injective.eq_iff
    rw [hs]
  have hs : conditionalSigmaEntropy μ (e ∘ P) m=conditionalSigmaEntropy μ P m := by
    unfold conditionalSigmaEntropy
    apply integral_congr_ae
    apply ae_of_all
    intro x
    unfold finiteShannon
    symm
    apply Fintype.sum_equiv e
    intro a
    have ha : {z | (e ∘ P) z=e a}={z | P z=a} := by
      ext z
      exact e.injective.eq_iff
    dsimp only
    rw [ha]
  rw [hi,hs] at H
  exact H

theorem conditionalInformation_factor_le
    {Y α β : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (hP : Measurable P)
    (f : α → β) (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ, 0 < (μ[({z | P z=P x}.indicator
      (fun _ => (1 : ℝ))) | m]) x) :
    conditionalInformation μ (f ∘ P) m ≤ᵐ[μ] conditionalInformation μ P m := by
  have hmono (a : α) :
      μ[({z | P z=a}.indicator (fun _ => (1 : ℝ))) | m] ≤ᵐ[μ]
      μ[({z | (f ∘ P) z=f a}.indicator (fun _ => (1 : ℝ))) | m] := by
    apply condExp_mono
      ((integrable_const (1 : ℝ)).indicator (hP (measurableSet_singleton a)))
      ((integrable_const (1 : ℝ)).indicator ((hf.comp hP) (measurableSet_singleton (f a))))
    apply ae_of_all
    intro z
    change ({z | P z=a}.indicator (fun _ => (1 : ℝ))) z ≤
      ({z | (f ∘ P) z=f a}.indicator (fun _ => (1 : ℝ))) z
    by_cases hz : P z=a
    · simp [hz,Function.comp_apply]
    · rw [Set.indicator_of_notMem (show z ∉ {z | P z=a} from hz)]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
  filter_upwards [ae_all_iff.mpr hmono,hpos] with x hx hp
  exact neg_le_neg (Real.log_le_log hp (hx (P x)))

theorem finiteFactor_conditionalEntropy_le_information
    {Y α β : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β] [Nonempty β]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (hP : Measurable P)
    (f : α → β) (hf : Measurable f) (hm : m ≤ mY)
    (hpos : ∀ᵐ x ∂μ, 0 < (μ[({z | P z=P x}.indicator
      (fun _ => (1 : ℝ))) | m]) x)
    (hint : Integrable (conditionalInformation μ P m) μ) :
    conditionalSigmaEntropy μ (f ∘ P) m ≤ ∫ x, conditionalInformation μ P m x ∂μ := by
  have H := conditionalInformation_fintype_integrable_integral m μ (f ∘ P) (hf.comp hP) hm
  rw [←H.2]
  exact integral_mono_ae H.1 hint (conditionalInformation_factor_le m μ P hP f hf hpos)

end DukePrimeDegree

end

end OAI
