import OAI.Probability.DilutedSpin.FunctionalStability
import OAI.Probability.DilutedSpin.NormalizedCutoff

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable def referenceEnergy {p : ℕ} (z : InteractionSample p) : ℝ := z.1 (fun _ => true)
lemma referenceEnergy_integrable {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable referenceEnergy M.disorder.toMeasure := by
  apply hθ.mono' (show Measurable (referenceEnergy (p := p)) by unfold referenceEnergy; fun_prop).aestronglyMeasurable
  exact ae_of_all _ (fun z => norm_le_pi_norm z.1 (fun _ => true))

lemma logSumExp_add_constant {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (a : ℝ) :
    Real.log (∑ x,Real.exp (f x+a))=Real.log (∑ x,Real.exp (f x))+a := by
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul,Real.log_mul (ne_of_gt (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)) (Real.exp_ne_zero _),Real.log_exp]

lemma logPartition_center {p N k : ℕ} (θ : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) :
    logPartition (fun j => centerSample (θ j)) h indices=
      logPartition θ h indices-(∑ j,referenceEnergy (θ j)) := by
  have he σ : logWeight (fun j => centerSample (θ j)) h indices σ=
      logWeight θ h indices σ+(-(∑ j,referenceEnergy (θ j))) := by
    simp only [logWeight,centerSample,centeredInteraction,referenceEnergy,Finset.sum_sub_distrib]
    ring
  simp only [logPartition,he,logSumExp_add_constant,sub_eq_add_neg]

lemma indexAverage_center {p N k : ℕ} (hN : 0 < N) (θ : Fin k → InteractionSample p) (h : Fin N → ℝ) :
    indexAverage (fun j => centerSample (θ j)) h=indexAverage θ h-(∑ j,referenceEnergy (θ j)) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hc : (Fintype.card (Fin k → Fin p → Fin N):ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [indexAverage,logPartition_center,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [sub_div,mul_div_cancel_left₀ _ hc]

lemma fieldAverage_center {p N k : ℕ} (M : Model p) (hN : 0 < N)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (θ : Fin k → InteractionSample p) :
    fieldAverage (N := N) (centeredModel M) (fun j => centerSample (θ j))=
      fieldAverage (N := N) M θ-(∑ j,referenceEnergy (θ j)) := by
  rw [centeredModel,indexAverage_mapModel]
  simp only [id_eq,indexAverage_center hN]
  rw [integral_sub (indexAverage_integrable_and_fieldAverage_bound M hh hN θ).1 (integrable_const _)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,fieldAverage]

lemma disorderAverage_center {p N : ℕ} (M : Model p) (hN : 0 < N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    disorderAverage (centeredModel M) N k=disorderAverage M N k-
      (k:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  rw [centeredModel,disorderAverage_map_eq]
  change (∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (centeredModel M) (fun j => centerSample (θ j))
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))=_
  simp_rw [fieldAverage_center M hN hh]
  rw [integral_sub (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).1
    (integrable_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)),
    integral_pi_sum M.disorder.toMeasure (referenceEnergy_integrable M hθ)]
  simp only [Fintype.card_fin,disorderAverage]

lemma pressure_center {p N : ℕ} (M : Model p) (hN : 0 < N)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    pressure (centeredModel M) N=pressure M N-(M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  change (∫ k,disorderAverage (centeredModel M) N k ∂poissonMeasure (M.alpha*N))/N=_
  simp_rw [disorderAverage_center M hN hθ hh]
  rw [integral_sub (disorderAverage_integrable_and_pressure_bound M hθ hh hN).1
    ((poisson_integrable_count _).mul_const _),integral_mul_const,poisson_mean]
  change ((∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))-(M.alpha*N:ℝ≥0)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure))/N=_
  simp only [NNReal.coe_mul,NNReal.coe_natCast,pressure,disorderAverage,fieldAverage,indexAverage]
  have hn : (N:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hN)
  field_simp
end DilutedSpinGlass

end

end OAI
