import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingCompactIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierObservable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedWindowTest

namespace OAI

/-! Entire compact incoming corrections after the actual integral Mobius action.
This permits residue observations at every positive height. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCompactIncomingTransform_differentiable
    (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (f : CubicThetaPoint → ℂ)
    (hf : IntegrableOn f K cubicThetaPointMeasure) :
    Differentiable ℂ (fun s : ℂ => ∫ p in K,f p*
      cubicThetaIncomingEisenstein (δ • p).val s ∂cubicThetaPointMeasure) := by
  have hmap : Continuous (fun p : CubicThetaPoint => (δ • p).val) :=
    continuous_subtype_val.comp (continuous_const_smul δ)
  have hKC := hK.image hmap
  obtain ⟨S,hS⟩ := cubicThetaIncomingEisenstein_compact_sum hKC
    (by rintro _ ⟨p,_,rfl⟩; exact (δ • p).property)
  have hterm (r : CubicThetaBottomRow) : Differentiable ℂ (fun s : ℂ => ∫ p in K,
      f p*cubicThetaIncomingTerm r (δ • p).val s ∂cubicThetaPointMeasure) := by
    have hi := hf.mul_continuousOn
      ((cubicThetaIncomingTerm_point_continuous r 0).comp (continuous_const_smul δ)).continuousOn hK
    have hd := cubicThetaCompactExponential_differentiable hK _ hi
      (fun p => Real.log (r.height (δ • p).val))
      ((cubicThetaRowLogHeight_point_continuous r).comp (continuous_const_smul δ)).continuousOn
    convert hd using 1
    funext s
    apply setIntegral_congr_fun hK.measurableSet
    intro p _
    change f p*cubicThetaIncomingTerm r (δ • p).val s=
      f p*cubicThetaIncomingTerm r (δ • p).val 0*
        Complex.exp (s*(Real.log (r.height (δ • p).val):ℂ))
    rw [cubicThetaIncomingTerm_exponential r (δ • p) s]
    ring
  have he (s : ℂ) : (∫ p in K,f p*
      cubicThetaIncomingEisenstein (δ • p).val s ∂cubicThetaPointMeasure)=
      ∑ r∈S,∫ p in K,f p*cubicThetaIncomingTerm r (δ • p).val s ∂cubicThetaPointMeasure := by
    calc
      _ = ∫ p in K,∑ r∈S,f p*cubicThetaIncomingTerm r (δ • p).val s
          ∂cubicThetaPointMeasure := by
        apply setIntegral_congr_fun hK.measurableSet
        intro p hp
        change f p*cubicThetaIncomingEisenstein (δ • p).val s=
          ∑ r∈S,f p*cubicThetaIncomingTerm r (δ • p).val s
        rw [hS (δ • p).val ⟨p,hp,rfl⟩ s,Finset.mul_sum]
      _ = _ := integral_finsetSum S (fun r _ => hf.mul_continuousOn
        ((cubicThetaIncomingTerm_point_continuous r s).comp (continuous_const_smul δ)).continuousOn hK)
  rw [show (fun s : ℂ => ∫ p in K,f p*cubicThetaIncomingEisenstein (δ • p).val s
      ∂cubicThetaPointMeasure)=(fun s => ∑ r∈S,∫ p in K,
      f p*cubicThetaIncomingTerm r (δ • p).val s ∂cubicThetaPointMeasure) from funext he]
  exact Differentiable.fun_sum (fun r _ => hterm r)

lemma cubicThetaShiftedIncomingWindow_differentiable (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) :
    Differentiable ℂ (fun s : ℂ => ∫ p in cubicThetaShiftedWindow a d,
      star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s
        ∂cubicThetaPointMeasure) := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container ha d
  let : IsFiniteMeasure (cubicThetaPointMeasure.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let f := (cubicThetaShiftedWindow a d).indicator
    (fun p => star (cubicThetaShiftedFourierWeight h W p))
  have hf : IntegrableOn f K cubicThetaPointMeasure := by
    have hm := (cubicThetaShiftedWindowWeight_memLp h W a d hK).star.integrable (by norm_num)
    apply hm.congr
    filter_upwards with p
    change star ((cubicThetaShiftedWindow a d).indicator
      (cubicThetaShiftedFourierWeight h W) p)=f p
    dsimp only [f]
    by_cases hp : p∈cubicThetaShiftedWindow a d
    · simp only [indicator_of_mem hp]
    · simp only [indicator_of_notMem hp,star_zero]
  have hd := cubicThetaCompactIncomingTransform_differentiable
    (cubicThetaShiftedInversion b) hK f hf
  convert hd using 1
  funext s
  calc
    _ = ∫ p in K,(cubicThetaShiftedWindow a d).indicator
        (fun p => star (cubicThetaShiftedFourierWeight h W p)*
          cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s) p
          ∂cubicThetaPointMeasure := by
      rw [setIntegral_indicator (cubicThetaShiftedWindow_measurable a d),inter_eq_right.mpr hSK]
    _ = _ := by
      apply setIntegral_congr_fun hK.measurableSet
      intro p _
      exact Set.indicator_mul_left _ _ _

end CubicFirstMoment

end

end OAI
