import OAI.Geometry.TranslativeCovering.PoissonConfig

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal NNReal

variable {Ω : Type u_1} [MeasurableSpace Ω]
abbrev RawConfig (Ω : Type u_2) := Σ n : ℕ, Fin n → Ω

lemma measurable_sigmaMk {β : ℕ → Type u_3} [∀ n, MeasurableSpace (β n)] (n : ℕ) :
    Measurable (Sigma.mk n : β n → Σ n, β n) := by
  intro s hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) n

lemma measurableSet_sigma {β : ℕ → Type u_4} [∀ n, MeasurableSpace (β n)]
    {s : Set (Σ n, β n)} (h : ∀ n, MeasurableSet (Sigma.mk n ⁻¹' s)) :
    MeasurableSet s := MeasurableSpace.measurableSet_iInf.mpr h

noncomputable def sample (r : ℝ≥0) (σ : Measure Ω) : Measure (RawConfig Ω) :=
  Measure.sum fun n => poissonMeasure r {n} •
    (Measure.pi (fun _ : Fin n => σ)).map (Sigma.mk n)

instance sample_probability (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (sample r σ) := by
  constructor
  rw [sample, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.map_apply (measurable_sigmaMk _) MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  simp only [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq,
    ENNReal.ofReal_one]

def avoidance (E : Set Ω) : Set (RawConfig Ω) := {x | ∀ i, x.2 i ∉ E}

lemma measurable_avoidance {E : Set Ω} (hE : MeasurableSet E) :
    MeasurableSet (avoidance E) := by
  apply measurableSet_sigma
  intro n
  change MeasurableSet {f : Fin n → Ω | ∀ i, f i ∉ E}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun i => hE.compl.preimage (measurable_pi_apply i))

lemma avoidance_prob (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    {E : Set Ω} (hE : MeasurableSet E) :
    (sample r σ) (avoidance E) = ENNReal.ofReal (Real.exp (- (r : ℝ) * σ.real E)) := by
  rw [sample, Measure.sum_apply _ (measurable_avoidance hE)]
  have hterm (n : ℕ) : (poissonMeasure r {n} •
      (Measure.pi (fun _ : Fin n => σ)).map (Sigma.mk n)) (avoidance E) =
      ENNReal.ofReal (Real.exp (-r) * ((r : ℝ) * σ.real Eᶜ)^n / n.factorial) := by
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_sigmaMk n) (measurable_avoidance hE)]
    have he : Sigma.mk n ⁻¹' avoidance E = Set.univ.pi (fun _ : Fin n => Eᶜ) := by
      ext f
      simp only [avoidance, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, mem_compl_iff,
        forall_const]
    rw [he, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      poissonMeasure_singleton, ← ENNReal.ofReal_toReal (measure_ne_top σ Eᶜ)]
    rw [← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity)]
    change _ = ENNReal.ofReal (Real.exp (-r) * ((r : ℝ) * (σ Eᶜ).toReal)^n / n.factorial)
    congr 1
    rw [mul_pow]
    ring
  simp_rw [hterm]
  have hs : HasSum (fun n : ℕ => Real.exp (-r) * ((r : ℝ)*σ.real Eᶜ)^n / n.factorial)
      (Real.exp (- (r : ℝ) * σ.real E)) := by
    convert! (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*σ.real Eᶜ)).mul_left
      (Real.exp (-r)) using 1
    · simp only [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, probReal_compl_eq_one_sub hE]
      congr 1
      ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]

end PoissonSample

end OAI
