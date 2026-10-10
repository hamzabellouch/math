import Mathlib
import OAI.Probability.SKValue.GroundState.RotatedCoefficients
import OAI.Probability.SKValue.GroundState.ExponentialMoments

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma finiteMaximum_le_iff {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (t : ℝ) :
    finiteMaximum x ≤ t ↔ ∀ i, x i≤t := by
  constructor
  · intro h i; exact (le_finiteMaximum x i).trans h
  · intro h; obtain ⟨i,hi⟩ := exists_finiteMaximum x; simpa only [←hi] using h i

noncomputable def logSumExp {ι : Type*} [Fintype ι] (d : ι → ℝ) : ℝ :=
  Real.log (∑ i, Real.exp (d i))

lemma exp_sum_pos {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) :
    0<∑ i, Real.exp (d i) := Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty

lemma gumbel_shift_cdf (d t : ℝ) :
    cdf (gumbelLaw.map (fun x ↦ x+d)) t=Real.exp (-Real.exp (-(t-d))) := by
  have : IsProbabilityMeasure (gumbelLaw.map (fun x ↦ x+d)) := inferInstance
  rw [cdf_eq_real,measureReal_def,Measure.map_apply (by fun_prop) measurableSet_Iic]
  have he : (fun x : ℝ ↦ x+d) ⁻¹' Iic t=Iic (t-d) := by ext x; simp only [mem_preimage,mem_Iic]; constructor <;> intro h <;> linarith
  rw [he,←measureReal_def,←cdf_eq_real,gumbel_cdf]

lemma gumbel_max_cdf {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (t : ℝ) :
    cdf ((Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))) t=
      Real.exp (-Real.exp (-(t-logSumExp d))) := by
  have hm : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have : IsProbabilityMeasure ((Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))) := inferInstance
  rw [cdf_eq_real,measureReal_def,Measure.map_apply hm measurableSet_Iic]
  have he : (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) ⁻¹' Iic t=
      univ.pi (fun i ↦ Iic (t-d i)) := by
    ext z
    simp only [mem_preimage,mem_Iic,finiteMaximum_le_iff,mem_univ_pi]
    exact forall_congr' (fun i ↦ by constructor <;> intro h <;> linarith)
  rw [he,Measure.pi_pi,ENNReal.toReal_prod]
  simp only [←measureReal_def,←cdf_eq_real,gumbel_cdf]
  rw [←Real.exp_sum]
  congr 1
  simp only [logSumExp]
  rw [show -(t-Real.log (∑ i, Real.exp (d i)))=-t+Real.log (∑ i, Real.exp (d i)) by ring,
    Real.exp_add,Real.exp_log (exp_sum_pos d)]
  simp_rw [show ∀ i, -(t-d i)=-t+d i by intro i; ring,Real.exp_add]
  rw [Finset.sum_neg_distrib,←Finset.mul_sum]

theorem gumbel_max_law {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) :
    (Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))=
      gumbelLaw.map (fun x ↦ x+logSumExp d) := by
  have hm : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have : IsProbabilityMeasure ((Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))) := inferInstance
  have : IsProbabilityMeasure (gumbelLaw.map (fun x ↦ x+logSumExp d)) := inferInstance
  apply prob_measure_eq_of_cdf
  intro t
  rw [gumbel_max_cdf,gumbel_shift_cdf]

lemma gumbel_max_integrable {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) :
    Integrable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i))
      (Measure.pi (fun _ : ι ↦ gumbelLaw)) := by
  have hm : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have h : Integrable (fun x : ℝ ↦ x) ((Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))) := by
    rw [gumbel_max_law,integrable_map_measure (by fun_prop) (by fun_prop)]
    exact gumbel_integrable.add (integrable_const _)
  exact (integrable_map_measure (by fun_prop) hm.aemeasurable).mp h

lemma integral_gumbel_max {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) :
    (∫ z, finiteMaximum (fun i ↦ d i+z i) ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
      gumbelMean+logSumExp d := by
  have hm : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have h := congrArg (fun μ : Measure ℝ ↦ ∫ x, x ∂μ) (gumbel_max_law d)
  rw [integral_map hm.aemeasurable (by fun_prop),integral_map (by fun_prop) (by fun_prop)] at h
  rw [h,integral_add gumbel_integrable (integrable_const _)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,gumbelMean]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal
namespace SKValueG

lemma log_tangent_bound {x m : ℝ} (hx : 0<x) (hm : 0 < m) :
    Real.log x ≤ x/m-1+Real.log m := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hm)
  rw [Real.log_div hx.ne' hm.ne'] at h
  linarith

lemma log_mean_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (hx : ∀ i, 0<x i) :
    (∑ i, Real.log (x i))/(Fintype.card ι : ℝ) ≤
      Real.log ((∑ i, x i)/(Fintype.card ι : ℝ)) := by
  let c : ℝ := Fintype.card ι
  have hc : 0<c := by dsimp [c]; positivity
  let m : ℝ := (∑ i, x i)/c
  have hm : 0 < m := div_pos (Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty) hc
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ log_tangent_bound (hx i) hm)
  have hs : (∑ i, x i) ≠ 0 := (Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty).ne'
  have he : (∑ i, (x i/m-1+Real.log m))=c*Real.log m := by
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_div]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp [m,c]
    field_simp [hs]
    ring
  rw [he] at h
  exact (div_le_iff₀ hc).mpr (by nlinarith)

lemma integral_log_le_log_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hl : Integrable (fun ω ↦ Real.log (f ω)) μ)
    (hp : ∀ᵐ ω ∂μ, 0<f ω) :
    (∫ ω, Real.log (f ω) ∂μ) ≤ Real.log (∫ ω, f ω ∂μ) := by
  have hm : 0<∫ ω, f ω ∂μ := integral_pos_iff_support_of_nonneg_ae (hp.mono (fun _ h ↦ h.le)) hf |>.mpr (by
    have hs : Function.support f =ᵐ[μ] univ := hp.mono (fun ω hω ↦ by apply propext; change (f ω≠0) ↔ True; simp [hω.ne'])
    rw [measure_congr hs]
    simp)
  have h := integral_mono_ae hl
    (((hf.div_const (∫ ω, f ω ∂μ)).sub (integrable_const 1)).add
      (integrable_const (Real.log (∫ ω, f ω ∂μ))))
    (hp.mono (fun ω hω ↦ log_tangent_bound hω hm))
  have he : (∫ ω, (f ω/(∫ ω, f ω ∂μ)-1)+Real.log (∫ ω, f ω ∂μ) ∂μ)=
      Real.log (∫ ω, f ω ∂μ) := by
    rw [integral_add (f := fun ω ↦ f ω/(∫ ω, f ω ∂μ)-1)
      (g := fun _ ↦ Real.log (∫ ω, f ω ∂μ))
      ((hf.div_const _).sub (integrable_const 1)) (integrable_const _),
      integral_sub (f := fun ω ↦ f ω/(∫ ω, f ω ∂μ)) (g := fun _ ↦ (1 : ℝ))
      (hf.div_const _) (integrable_const 1),integral_div]
    simp [hm.ne']
  exact h.trans_eq he

end SKValueG

end

end OAI
