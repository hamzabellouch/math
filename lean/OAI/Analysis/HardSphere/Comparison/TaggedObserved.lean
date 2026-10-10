import Mathlib
import OAI.Analysis.HardSphere.Comparison.TaggedMoment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {Q X I Y : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Y]
attribute [local instance] Classical.propDecidable

omit [MeasurableSpace X] [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma tagLikelihood_support (σ : Measure Q) (tag : Q→I) (L : Q×X→ℝ≥0∞)
    (E : I→Set X) (hzero : ∀q x,x∉E (tag q)→L (q,x)=0) (i : I) (x : X)
    (hx : x∉E i) : tagLikelihood σ tag L i x=0 := by
  unfold tagLikelihood
  have he : (fun q ↦ if tag q=i then L (q,x) else 0)=fun _ ↦ (0:ℝ≥0∞) := by
    funext q
    exact (by
    by_cases hq : tag q=i
    · simp [hq,hzero q x (hq.symm ▸ hx)]
    · simp [hq])
  rw [he]
  simp

lemma finite_density_of_square {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsFiniteMeasure P] (f : Z→ℝ≥0∞) (_hf : Measurable f)
    (hf2 : (∫⁻x,(f x)^2 ∂ P)≠⊤) : IsFiniteMeasure (P.withDensity f) := by
  apply isFiniteMeasure_withDensity
  have hp (x : Z) : f x≤1+(f x)^2 := by
    by_cases h : f x≤1
    · exact h.trans (le_add_right le_rfl)
    · have h' : 1≤f x := le_of_not_ge h
      calc
        f x = f x*1 := (mul_one _).symm
        _ ≤ f x*f x := mul_le_mul' le_rfl h'
        _ ≤ 1+(f x)^2 := by rw [pow_two]; exact le_add_left le_rfl
  apply ne_of_lt ((lintegral_mono hp).trans_lt _)
  rw [lintegral_add_left measurable_const,lintegral_const]
  exact ENNReal.add_lt_top.mpr ⟨by simp [measure_lt_top],lt_top_iff_ne_top.mpr hf2⟩

lemma tagged_observed_moment (σ : Measure Q) (P : Measure X)
    [SFinite σ] [IsFiniteMeasure P] (tag : Q→I) (ht : Measurable tag)
    (L : Q×X→ℝ≥0∞) (hL : Measurable L) (E : I→Set X)
    (hE : ∀i,MeasurableSet (E i)) (hz : ∀q x,x∉E (tag q)→L (q,x)=0)
    (κ : Kernel (I×X) Y) [IsMarkovKernel κ]
    (C : ℝ) (hC : 0≤C)
    (hbound : (∫⁻q,∫⁻q',∫⁻x,L (q,x)*L (q',x) ∂ P ∂ σ ∂ σ)≤ENNReal.ofReal C) :
    let ν := ((σ.prod P).withDensity L).map (fun p ↦ (tag p.1,p.2))
    let R := taggedReference P E
    Integrable (fun y ↦ (((ν.compProd κ).map Prod.snd).rnDeriv
      ((R.compProd κ).map Prod.snd) y).toReal^2) ((R.compProd κ).map Prod.snd) ∧
    (∫y,(((ν.compProd κ).map Prod.snd).rnDeriv
      ((R.compProd κ).map Prod.snd) y).toReal^2 ∂(R.compProd κ).map Prod.snd)≤C := by
  let R := taggedReference P E
  let f : I×X→ℝ≥0∞ := fun p ↦ tagLikelihood σ tag L p.1 p.2
  have hf : Measurable f := taggedFunction_measurable _ (tagLikelihood_measurable σ tag ht L hL)
  have hsum : (∫⁻x,(∑i,tagLikelihood σ tag L i x)^2 ∂ P)≤ENNReal.ofReal C := by
    simp_rw [sum_tagLikelihood σ tag ht L hL]
    rwa [mixed_likelihood_square σ P L hL]
  have hmoment := tagged_density_moment P E (tagLikelihood σ tag L)
    (tagLikelihood_measurable σ tag ht L hL) C hC hsum
  have hsquare : (∫⁻p,(f p)^2 ∂ R)≤ENNReal.ofReal C :=
    (tagged_density_square P E (tagLikelihood σ tag L) (tagLikelihood_measurable σ tag ht L hL)).trans hsum
  let _ : IsFiniteMeasure R := by dsimp [R,taggedReference]; infer_instance
  let _ : IsFiniteMeasure (R.withDensity f) :=
    finite_density_of_square R f hf (ne_of_lt (hsquare.trans_lt ENNReal.ofReal_lt_top))
  have hd : (fun p ↦ ((R.withDensity f).rnDeriv R p).toReal^2)=ᵐ[R]
      (fun p ↦ (f p).toReal^2) :=
    (Measure.rnDeriv_withDensity R hf).fun_comp (fun x : ℝ≥0∞ ↦ x.toReal^2)
  have hm := observed_kernel_second_moment R (R.withDensity f)
    (withDensity_absolutelyContinuous _ _) κ (hmoment.1.congr hd.symm)
  have he : ((σ.prod P).withDensity L).map (fun p ↦ (tag p.1,p.2))=R.withDensity f := by
    rw [tagged_mixture_density σ P tag ht L hL]
    exact tagged_full_density P E hE _ (tagLikelihood_support σ tag L E hz)
  dsimp only
  rw [he]
  refine ⟨hm.1,hm.2.trans ?_⟩
  rw [integral_congr_ae hd]
  exact hmoment.2

end HardSphere.Comparison

end
end

end

end OAI
