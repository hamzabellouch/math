import Mathlib
import OAI.Probability.SKGap.Gaussian.SquareTail2

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
namespace SKGapCutoff.Regression

lemma prod_event_le_of_section_law {H A B C : Type*}
    [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ρ : Measure H) (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [SFinite ν]
    (f : H × A → C) (g : H × B → C) (hf : Measurable f) (hg : Measurable g)
    (G : Set H) (hG : MeasurableSet G)
    (hfg : ∀ h ∈ G, μ.map (fun a => f (h,a)) = ν.map (fun b => g (h,b)))
    (T : Set C) (hT : MeasurableSet T) :
    (ρ.prod μ) (f ⁻¹' T) ≤ (ρ.prod ν) (g ⁻¹' T)+ρ Gᶜ := by
  rw [Measure.prod_apply (hf hT), Measure.prod_apply (hg hT)]
  have hm := measurable_measure_prodMk_left (ν := ν) (hg hT)
  calc
    _ ≤ ∫⁻ h, ν (Prod.mk h ⁻¹' (g ⁻¹' T)) + Gᶜ.indicator (fun _ => (1:ℝ≥0∞)) h ∂ρ := by
      apply lintegral_mono
      intro h
      change μ (Prod.mk h ⁻¹' (f ⁻¹' T)) ≤ ν (Prod.mk h ⁻¹' (g ⁻¹' T)) +
        Gᶜ.indicator (fun _ => (1:ℝ≥0∞)) h
      by_cases hh : h ∈ G
      · have he := congrArg (fun m : Measure C => m T) (hfg h hh)
        rw [Measure.map_apply (show Measurable (fun a => f (h,a)) from hf.comp measurable_prodMk_left) hT,
          Measure.map_apply (show Measurable (fun b => g (h,b)) from hg.comp measurable_prodMk_left) hT] at he
        rw [Set.indicator_of_notMem (show h ∉ Gᶜ from fun hc => hc hh), add_zero]
        change μ ((fun a => f (h,a)) ⁻¹' T) ≤ ν ((fun b => g (h,b)) ⁻¹' T)
        exact le_of_eq he
      · simp only [Set.indicator_of_mem (show h ∈ Gᶜ from hh)]
        exact (prob_le_one (μ := μ)).trans (le_add_left le_rfl)
    _ = _ := by
      rw [lintegral_add_left hm, lintegral_indicator hG.compl]
      simp

lemma exponentiallyRare_of_measure_le_add
    {H A B : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (B n)]
    (ρ : ∀ n, Measure (H n)) (μ : ∀ n, Measure (A n)) (ν : ∀ n, Measure (B n))
    (S : ∀ n, Set (H n)) (T : ∀ n, Set (A n)) (V : ∀ n, Set (B n))
    (hT : ExponentiallyRare μ T) (hV : ExponentiallyRare ν V)
    (hS : ∀ᶠ n in atTop, ρ n (S n) ≤ μ n (T n)+ν n (V n)) :
    ExponentiallyRare ρ S := by
  obtain ⟨C,c,hC,hc,hTc⟩ := hT
  obtain ⟨D,d,hD,hd,hVd⟩ := hV
  refine ⟨C+D,min c d,by positivity,lt_min hc hd,?_⟩
  filter_upwards [hTc,hVd,hS] with n hn hm hs
  refine hs.trans ((add_le_add hn hm).trans ?_)
  have hc' : Real.exp (-c*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left c d,Nat.cast_nonneg (α := ℝ) n]
  have hd' : Real.exp (-d*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right c d,Nat.cast_nonneg (α := ℝ) n]
  rw [add_mul,ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc' hC.le))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd' hD.le))

theorem ExponentialEmpiricalConcentration.of_section_law
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H A B : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (B n)]
    (ρ : ∀ n, Measure (H n)) (μ : ∀ n, Measure (A n)) (η : ∀ n, Measure (B n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, SFinite (η n)]
    (X : ∀ n, H n × A n → Fin n → E) (Y : ∀ n, H n × B n → Fin n → E)
    (hXm : ∀ n, Measurable (X n)) (hYm : ∀ n, Measurable (Y n))
    (G : ∀ n, Set (H n)) (hG : ∀ n, MeasurableSet (G n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hXY : ∀ᶠ n in atTop, ∀ h ∈ G n,
      (μ n).map (fun a => X n (h,a)) = (η n).map (fun b => Y n (h,b)))
    {ν : Measure E}
    (hY : ExponentialEmpiricalConcentration (fun n => (ρ n).prod (η n)) Y ν) :
    ExponentialEmpiricalConcentration (fun n => (ρ n).prod (μ n)) X ν := by
  intro f K hf B hB ε hε
  apply exponentiallyRare_of_measure_le_add
    (fun n => (ρ n).prod (μ n)) (fun n => (ρ n).prod (η n)) ρ _ _ _
    (hY f K hf B hB ε hε) hrare
  filter_upwards [hXY] with n hn
  let T : Set (Fin n → E) := {z | ε ≤ |(∑ i, f (z i))/(n:ℝ)-∫ x, f x ∂ν|}
  have hT : MeasurableSet T := by
    apply measurableSet_le measurable_const
    exact (Measurable.sub ((Finset.measurable_sum _ (fun i _ =>
      hf.continuous.measurable.comp (measurable_pi_apply i))).div_const _) measurable_const).abs
  exact prod_event_le_of_section_law (ρ n) (μ n) (η n) (X n) (Y n)
    (hXm n) (hYm n) (G n) (hG n) hn T hT

theorem ExponentialSquareTails.of_section_law
    {H A B : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (B n)]
    (ρ : ∀ n, Measure (H n)) (μ : ∀ n, Measure (A n)) (η : ∀ n, Measure (B n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, SFinite (η n)]
    (X : ∀ n, H n × A n → Fin n → ℝ) (Y : ∀ n, H n × B n → Fin n → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hYm : ∀ n, Measurable (Y n))
    (G : ∀ n, Set (H n)) (hG : ∀ n, MeasurableSet (G n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hXY : ∀ᶠ n in atTop, ∀ h ∈ G n,
      (μ n).map (fun a => X n (h,a)) = (η n).map (fun b => Y n (h,b)))
    (hY : ExponentialSquareTails (fun n => (ρ n).prod (η n)) Y) :
    ExponentialSquareTails (fun n => (ρ n).prod (μ n)) X := by
  intro ε hε
  obtain ⟨R,hR,hYR⟩ := hY ε hε
  refine ⟨R,hR,?_⟩
  apply exponentiallyRare_of_measure_le_add
    (fun n => (ρ n).prod (μ n)) (fun n => (ρ n).prod (η n)) ρ _ _ _ hYR hrare
  filter_upwards [hXY] with n hn
  let T : Set (Fin n → ℝ) := {z | ε ≤ (∑ i, squareTail R (z i))/(n:ℝ)}
  have hT : MeasurableSet T := by
    apply measurableSet_le measurable_const
    exact (Finset.measurable_sum _ (fun i _ =>
      (measurable_squareTail R).comp (measurable_pi_apply i))).div_const _
  exact prod_event_le_of_section_law (ρ n) (μ n) (η n) (X n) (Y n)
    (hXm n) (hYm n) (G n) (hG n) hn T hT

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology

namespace SKGapCutoff.Regression

noncomputable def unitVector {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => v i/Real.sqrt (∑ j, v j^2)

lemma unitVector_sq_sum {n : ℕ} (v : Fin n → ℝ) :
    ∑ i, unitVector v i^2 = if ∑ i, v i^2 = 0 then 0 else 1 := by
  have hs : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [unitVector, div_pow, ← Finset.sum_div, Real.sq_sqrt hs]
  split_ifs with h
  · simp [h]
  · exact div_self h

lemma unitVector_sq_le {n : ℕ} (v : Fin n → ℝ) : ∑ i, unitVector v i^2 ≤ 1 := by
  rw [unitVector_sq_sum]
  split_ifs <;> norm_num

lemma unitVector_sq_eq {n : ℕ} (v : Fin n → ℝ) (hv : 0 < ∑ i, v i^2) :
    ∑ i, unitVector v i^2 = 1 := by
  rw [unitVector_sq_sum, ite_eq_right (ne_of_gt hv)]

lemma residualProjection_idem {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ*U=1) : residualProjection U*residualProjection U=residualProjection U := by
  rw [residualProjection, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    ← residualProjection, residualProjection_mul U hU, Matrix.zero_mul, sub_zero]

lemma normalized_residual_perpendicular {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ*U=1) (v : Fin n → ℝ) :
    Uᵀ *ᵥ unitVector (residualProjection U *ᵥ v)=0 := by
  have he : unitVector (residualProjection U *ᵥ v) =
      (Real.sqrt (∑ i, (residualProjection U *ᵥ v) i^2))⁻¹ • (residualProjection U *ᵥ v) := by
    ext i
    change _ = (Real.sqrt (∑ j, (residualProjection U *ᵥ v) j^2))⁻¹ * (residualProjection U *ᵥ v) i
    simp only [unitVector, div_eq_mul_inv, mul_comm]
  rw [he, Matrix.mulVec_smul, Matrix.mulVec_mulVec, mul_residualProjection U hU,
    Matrix.zero_mulVec, smul_zero]

lemma normalized_residual_fixed {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ*U=1) (v : Fin n → ℝ) :
    residualProjection U *ᵥ unitVector (residualProjection U *ᵥ v)=
      unitVector (residualProjection U *ᵥ v) := by
  change (1-U*Uᵀ) *ᵥ unitVector (residualProjection U *ᵥ v) = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    normalized_residual_perpendicular U hU, Matrix.mulVec_zero, sub_zero]

lemma residual_scaled_predictor {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (residualProjection U *ᵥ v) i = v i-
      ∑ a, (Real.sqrt n*U i a)*((∑ j, Real.sqrt n*U j a*v j)/(n:ℝ)) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hs : (Real.sqrt (n:ℝ))^2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [residualProjection, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec,Pi.sub_apply]
  congr 1
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_div,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*(U i a*U j a*v j)) hs]

lemma scaled_unitVector {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (i : Fin n) :
    Real.sqrt n*unitVector v i = v i/Real.sqrt ((∑ j, v j^2)/(n:ℝ)) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  rw [Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [unitVector,div_div_eq_mul_div]
  ring

@[fun_prop] lemma measurable_unitVector {n : ℕ} : Measurable (@unitVector n) := by
  unfold unitVector
  fun_prop

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
