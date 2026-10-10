import Mathlib.Probability.Kernel.Deterministic
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace OAI

/-! # A conditionally diagonal self-product is a measurable Dirac family -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace RegularPointCoordinates

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem probability_zeroOne_of_prod_diagonal (ν : Measure B) [IsProbabilityMeasure ν]
    (h : ∀ᵐ z ∂ν.prod ν, z.1=z.2) : IsZeroOneMeasure ν := by
  refine ⟨fun s hs => ?_⟩
  have hsub : s ×ˢ sᶜ ⊆ {z : B×B | ¬ z.1=z.2} := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ he
    exact hy (he ▸ hx)
  have hz : (ν.prod ν) (s ×ˢ sᶜ)=0 := measure_mono_null hsub (ae_iff.mp h)
  rw [Measure.prod_prod] at hz
  rcases mul_eq_zero.mp hz with hzero | hzero
  · exact Or.inl hzero
  · right
    have hsum := measure_add_measure_compl hs (μ:=ν)
    simpa only [hzero,add_zero,measure_univ] using hsum

theorem kernel_dirac_of_diagonal_self_product [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) (κ : Kernel A B) [IsMarkovKernel κ]
    (h : ∀ᵐ z ∂((κ ×ₖ κ) ∘ₘ μ), z.1=z.2) :
    ∃ f : A → B, Measurable f ∧ ∀ᵐ a ∂μ, κ a=Measure.dirac (f a) := by
  classical
  have hz : ∀ᵐ a ∂μ, IsZeroOneMeasure (κ a) := by
    filter_upwards [Measure.ae_ae_of_ae_comp h] with a ha
    apply probability_zeroOne_of_prod_diagonal (κ a)
    simpa only [Kernel.prod_apply] using ha
  obtain ⟨N,hbadN,hN,hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hz)
  let b : B := Classical.choice inferInstance
  let κ' := Kernel.piecewise hN (Kernel.deterministic (fun _ : A => b) measurable_const) κ
  have hκ' (a : A) : IsZeroOneMeasure (κ' a) := by
    by_cases ha : a ∈ N
    · simpa only [κ',Kernel.piecewise_apply,ite_eq_left ha,Kernel.deterministic_apply] using
        (show IsZeroOneMeasure (Measure.dirac b) from
          ⟨fun s hs => by by_cases hb : b ∈ s <;> simp [Measure.dirac_apply' _ hs,hb]⟩)
    · have hh : IsZeroOneMeasure (κ a) := by
        by_contra hn
        exact ha (hbadN hn)
      simpa only [κ',Kernel.piecewise_apply,ite_eq_right ha] using hh
  let : IsDeterministic κ' := (Kernel.isDeterministic_iff_isZeroOneMeasure κ').mpr hκ'
  obtain ⟨f,hf,he⟩ := Kernel.IsDeterministic.exists_eq_deterministic κ'
  refine ⟨f,hf,?_⟩
  have hgood : ∀ᵐ a ∂μ, a ∉ N := by
    apply ae_iff.mpr
    have he : {a : A | ¬a ∉ N}=N := by ext a; simp
    rwa [he]
  filter_upwards [hgood] with a ha
  have hh : κ' a=κ a := by simp only [κ',Kernel.piecewise_apply,ite_eq_right ha]
  rw [←hh,he,Kernel.deterministic_apply]

end RegularPointCoordinates

end

end OAI
