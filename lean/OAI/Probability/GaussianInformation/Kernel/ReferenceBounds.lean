import Mathlib
import OAI.Probability.GaussianInformation.Kernel.GaussianReference

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open GaussianTools

lemma continuous_integrable_on_support {d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {f : Vec d → ℝ} (hf : Continuous f) (s : Vec d) (R : ℝ)
    (hs : ∀ᵐ u ∂ν, u ∈ closedBall s R) : Integrable f ν := by
  have h := hf.continuousOn.integrableOn_compact (μ := ν) (isCompact_closedBall s R)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hs] at h

lemma integrable_log_atDensity {p d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ)
    (s : Vec d) (R : ℝ) (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) :
    Integrable (fun u => Real.log (atDensity r X y u)) ν := by
  apply continuous_integrable_on_support ν _ s R hs
  have hc : Continuous (fun u => atDensity r X y u) := by
    unfold atDensity labelDensity gaussianPDFReal applyRows
    fun_prop
  exact hc.log (fun u => (atDensity_pos hr X y u).ne')

lemma log_integral_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (v : α → ℝ)
    (hv : ∀ᵐ x ∂μ,0 < v x) (hvi : Integrable v μ)
    (hvlog : Integrable (fun x => Real.log (v x)) μ)
    {a : ℝ} (ha : 0 < a) (hva : (∫ x,v x ∂μ) ≤ a) :
    (∫ x,Real.log (v x) ∂μ) ≤ Real.log a := by
  have hpoint : ∀ᵐ x ∂μ,Real.log (v x) ≤ v x/a-1+Real.log a := by
    filter_upwards [hv] with x hx
    have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
    rw [Real.log_div hx.ne' ha.ne'] at h
    linarith
  have h := integral_mono_ae hvlog (((hvi.div_const a).sub (integrable_const 1)).add (integrable_const (Real.log a))) hpoint
  have he : (∫ x,v x/a-1+Real.log a ∂μ) = (∫ x,v x ∂μ)/a-1+Real.log a := by
    rw [integral_add (f := fun x => v x/a-1) (g := fun _ => Real.log a)
        ((hvi.div_const a).sub (integrable_const 1)) (integrable_const _),
      integral_sub (f := fun x => v x/a) (g := fun _ => (1:ℝ)) (hvi.div_const a) (integrable_const 1),
      integral_div]
    simp
  change (∫ x,Real.log (v x) ∂μ) ≤ (∫ x,v x/a-1+Real.log a ∂μ) at h
  rw [he] at h
  have hb : (∫ x,v x ∂μ)/a ≤ 1 := (div_le_one ha).mpr hva
  linarith

lemma local_log_lower {p d L : ℕ} (hL : 0 < L) (ν τ : Measure (Vec d))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] {m : ℝ} (hm : 0 < m)
    (hdom : ENNReal.ofReal m • τ ≤ ν)
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ)
    (s : Vec d) (R : ℝ) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R) (j : Fin L) :
    Real.log m-Real.log L+(∫ u,Real.log (atDensity (r j) X y u) ∂τ) ≤
      Real.log (mixture ν r X y) := by
  have hpos := integral_atDensity_pos τ (hr j) X y
  have hpoint : m*(∫ u,atDensity (r j) X y u ∂τ)/(L:ℝ) ≤ mixture ν r X y := by
    have h := integral_mono_measure hdom
      (Filter.Eventually.of_forall (fun u => (atDensity_pos (hr j) X y u).le))
      (integrable_atDensity ν (hr j) X y)
    rw [integral_smul_measure,ENNReal.toReal_ofReal hm.le,smul_eq_mul] at h
    exact (div_le_div_of_nonneg_right h (by positivity)).trans (mixture_lower ν r hr X y j)
  have hj := log_integral_ge τ (atDensity (r j) X y)
    (Filter.Eventually.of_forall (fun u => atDensity_pos (hr j) X y u))
    (integrable_atDensity τ (hr j) X y) (integrable_log_atDensity τ (hr j) X y s R hs) hpos le_rfl
  have hlog := Real.log_le_log (by positivity : 0 < m*(∫ u,atDensity (r j) X y u ∂τ)/(L:ℝ)) hpoint
  rw [Real.log_div (mul_ne_zero hm.ne' hpos.ne') (by positivity),Real.log_mul hm.ne' hpos.ne'] at hlog
  linarith

noncomputable def energy {p d : ℕ} (X : Mat p d) (v : Vec d) (e : Fin p → ℝ) : ℝ :=
  ∑ i,(applyRows X v i+e i)^2
noncomputable def matEnergy {p d : ℕ} (X : Mat p d) : ℝ := ∑ i,∑ j,(X i j)^2

lemma energy_nonneg {p d : ℕ} (X : Mat p d) (v : Vec d) (e : Fin p → ℝ) :
    0 ≤ energy X v e := Finset.sum_nonneg (fun i _ => sq_nonneg (applyRows X v i+e i))
lemma matEnergy_nonneg {p d : ℕ} (X : Mat p d) : 0 ≤ matEnergy X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))

lemma energy_le {p d : ℕ} (X : Mat p d) (v : Vec d) (e : Fin p → ℝ) :
    energy X v e ≤ 2*matEnergy X*‖v‖^2+2*∑ i,(e i)^2 := by
  have hh (i : Fin p) : (applyRows X v i)^2 ≤ (∑ j,(X i j)^2)*‖v‖^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) (fun j => v j)
    dsimp [applyRows]
    rw [EuclideanSpace.norm_sq_eq]
    simpa using h
  calc
    _ ≤ ∑ i,(2*((∑ j,(X i j)^2)*‖v‖^2)+2*(e i)^2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [hh i,sq_nonneg (applyRows X v i-e i)]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]; dsimp [matEnergy]; ring

lemma integrable_matEnergy {p d : ℕ} :
    Integrable (@matEnergy p d) (Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (((memLp_id_gaussianReal (2:NNReal)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin p => scalarRow d) i)).integrable_sq

lemma integrable_energy_rows {p d : ℕ} (v : Vec d) (e : Fin p → ℝ) :
    Integrable (fun X : Mat p d => energy X v e) (Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  apply integrable_finsetSum
  intro i _
  exact (((row_memLp v).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin p => scalarRow d) i)).add (memLp_const (e i))).integrable_sq

lemma energy_rows_le {p d : ℕ} (v : Vec d) (e : Fin p → ℝ) :
    (∫ X : Mat p d,energy X v e ∂Measure.pi (fun _ : Fin p => scalarRow d)) ≤
      2*(p:ℝ)*‖v‖^2+2*∑ i,(e i)^2 := rows_shift_energy v e

lemma log_atDensity_shift {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d)
    (s u : Vec d) (e : Fin p → ℝ) :
    Real.log (atDensity r X (applyRows X s+e) u) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-energy X (s-u) e/(2*r^2) := by
  rw [atDensity,log_labelDensity hr]
  congr 2
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  rw [applyRows_sub]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

end ReferenceGaussian

end OAI
