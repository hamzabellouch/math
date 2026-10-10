import OAI.Probability.DilutedSpin.RealEncoding

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma integrate_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g E : X → ℝ} (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hE : Integrable E μ) (h : ∀ᵐ x ∂μ,|f x-g x|≤E x) :
    Integrable f μ ∧ |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)|≤∫ x,E x ∂μ := by
  have hd : Integrable (fun x => f x-g x) μ := hE.mono' (hf.sub hg.aestronglyMeasurable) (by simpa only [Real.norm_eq_abs] using h)
  have hfi : Integrable f μ := by simpa only [Pi.add_def,sub_add_cancel] using hd.add hg
  refine ⟨hfi,?_⟩
  rw [← integral_sub hfi hg]
  calc
    _ ≤ ∫ x,|f x-g x| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x-g x)
    _ ≤ _ := integral_mono_ae hd.abs hE h

lemma integrable_pi_sum {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ) :
    Integrable (fun x : ι → X => ∑ i,g (x i)) (Measure.pi (fun _ : ι => μ)) :=
  integrable_finsetSum _ (fun _ _ => integrable_comp_eval (μ := fun _ : ι => μ) hg)

lemma integral_pi_sum {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ) :
    (∫ x : ι → X,∑ i,g (x i) ∂Measure.pi (fun _ : ι => μ))=(Fintype.card ι:ℝ)*(∫ x,g x ∂μ) := by
  rw [integral_finsetSum _ (fun i _ => integrable_comp_eval (μ := fun _ : ι => μ) hg)]
  simp only [integral_comp_eval (μ := fun _ : ι => μ) hg.aestronglyMeasurable,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma indexAverage_stability {p N k : ℕ} (hN : 0<N) (θ θ' : Fin k → InteractionSample p)
    (h h' : Fin N → ℝ) :
    |indexAverage θ h-indexAverage θ' h'|≤∑ j,‖(θ j).1-(θ' j).1‖+∑ i,|h i-h' i| := by
  let : NeZero N := ⟨ne_of_gt hN⟩
  unfold indexAverage
  rw [← FiniteLaw.uniform_expect,← FiniteLaw.uniform_expect]
  apply FiniteLaw.abs_expect_sub_le
  intro i
  exact logPartition_stability θ θ' h h' i

end DilutedSpinGlass

end

end OAI
