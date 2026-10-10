import Mathlib
import OAI.Probability.SKGap.Entropy.ProdFst

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
namespace SKGapCutoff.Regression
lemma independent_bounded_average_tail_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Type*} [MeasurableSpace F] (τ : Measure F) {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → F) (hXi : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) τ μ) (f : Fin n → F → ℝ)
    (hf : ∀ i, Measurable (f i)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ i z, |f i z| ≤ B) (ε : ℝ) (hε : 0 ≤ ε) :
    μ {g | ε ≤ |((∑ i, f i (X i g)) - ∑ i, ∫ z, f i z ∂τ)/(n:ℝ)|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(2*B^2))) := by
  let m (i : Fin n) := ∫ z, f i z ∂τ
  have hi : iIndepFun (fun i (g : Ω) => f i (X i g)-m i) μ :=
    hXi.comp (fun i z => f i z-m i) (fun i => (hf i).sub_const (m i))
  have hm (i : Fin n) : (∫ g : Ω, f i (X i g) ∂μ) = m i :=
    (hX i).integral_comp (hf i).aestronglyMeasurable
  have hsub (i : Fin n) : HasSubgaussianMGF (fun g : Ω => f i (X i g)-m i)
      ((‖B-(-B)‖₊/2)^2) μ := by
    have hb : ∀ᵐ g : Ω ∂μ, f i (X i g) ∈ Set.Icc (-B) B :=
      Filter.Eventually.of_forall (fun g => abs_le.mp (hbound i (X i g)))
    simpa only [hm] using hasSubgaussianMGF_of_mem_Icc
      (show AEMeasurable (fun g : Ω => f i (X i g)) μ from
        (hf i).comp_aemeasurable (hX i).aemeasurable) hb
  have hh := subgaussian_abs_tail
    (HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => hsub i))
    (ε*n) (by positivity)
  have he (g : Ω) :
      (ε*(n:ℝ) ≤ |∑ i, (f i (X i g)-m i)|) ↔
        ε ≤ |((∑ i, f i (X i g)) - ∑ i, m i)/(n:ℝ)| := by
    rw [Finset.sum_sub_distrib, abs_div, abs_of_pos (show (0:ℝ) < n from Nat.cast_pos.mpr hn)]
    exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).symm
  simp only [he] at hh
  convert hh using 1
  congr 3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
    coe_nnnorm, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith : 0 ≤ B-(-B))]
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  by_cases hB0 : B=0
  · simp [hB0]
  · field_simp
    ring

lemma probability_average_lipschitz
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [MeasurableSpace F] [BorelSpace F]
    (τ : Measure F) [IsProbabilityMeasure τ]
    {f : E × F → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : ∀ z, |f z| ≤ B) :
    LipschitzWith K (fun x => ∫ y, f (x,y) ∂τ) := by
  have hi (x : E) : Integrable (fun y => f (x,y)) τ := by
    apply integrable_bounded_lipschitz τ (K := K) _ B (fun y => hB (x,y))
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using
      hf.dist_le_mul (x,y) (x,z)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← integral_sub (hi x) (hi y)]
  have hh := norm_integral_le_of_norm_le_const (μ := τ)
    (C := (K:ℝ)*dist x y) (f := fun z => f (x,z)-f (y,z))
    (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs, ← Real.dist_eq, Prod.dist_eq, dist_self,
        max_eq_left (dist_nonneg)] using hf.dist_le_mul (x,z) (y,z)))
  simpa using hh

lemma probability_average_bound {E F : Type*} [MeasurableSpace F]
    (τ : Measure F) [IsProbabilityMeasure τ] {f : E × F → ℝ}
    (B : ℝ) (hB : ∀ z, |f z| ≤ B) (x : E) :
    |∫ z, f (x,z) ∂τ| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := τ)
    (C := B) (f := fun z => f (x,z))
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hB (x,z)))
  simpa using h

lemma iid_seed_empirical_tail
    {E F H : Type*} [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace H]
    (τ : Measure F) [IsProbabilityMeasure τ] (ρ : Measure H) [IsProbabilityMeasure ρ]
    {n : ℕ} (hn : 0 < n) (X : H → Fin n → E) (hX : Measurable X)
    (f : E × F → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B) (ε : ℝ) (hε : 0 ≤ ε) :
    (ρ.prod (Measure.pi (fun _ : Fin n => τ))) {z | ε ≤
      |((∑ i, f (X z.1 i,z.2 i)) - ∑ i, ∫ w, f (X z.1 i,w) ∂τ)/(n:ℝ)|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(2*B^2))) := by
  have hM : Measurable (fun x => ∫ y, f (x,y) ∂τ) :=
    (show StronglyMeasurable (Function.uncurry (fun x y => f (x,y))) from
      hf.stronglyMeasurable).integral_prod_right.measurable
  apply probability_prod_section_bound
  · apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    apply Measurable.sub
    · apply Finset.measurable_sum
      intro i _
      exact hf.comp ((((measurable_pi_apply i).comp hX).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
    · apply Finset.measurable_sum
      intro i _
      exact hM.comp (((measurable_pi_apply i).comp hX).comp measurable_fst)
  · intro h
    exact independent_bounded_average_tail_law τ hn
      (fun i (z : Fin n → F) => z i)
      (iIndepFun_pi (fun _ => measurable_id.aemeasurable))
      (fun i => (measurePreserving_eval (fun _ : Fin n => τ) i).hasLaw)
      (fun i w => f (X h i,w)) (fun i => hf.comp measurable_prodMk_left)
      B hB (fun i w => hbound _) ε hε

theorem ExponentialEmpiricalConcentration.iid_seed
    {E F : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν] (τ : Measure F) [IsProbabilityMeasure τ]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν) :
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (Measure.pi (fun _ : Fin n => τ)))
      (fun n z i => (X n z.1 i,z.2 i)) (ν.prod τ) := by
  intro f K hf B hbound ε hε
  let D := |B|+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hb : ∀ z, |f z| ≤ D := fun z => (hbound z).trans (by dsimp [D]; linarith [le_abs_self B])
  let ψ : E → ℝ := fun x => ∫ y, f (x,y) ∂τ
  have hp := probability_average_lipschitz τ hf D hb
  have hpb := probability_average_bound τ D hb
  have hm : ∫ z, f z ∂ν.prod τ = ∫ x, ψ x ∂ν :=
    integral_prod f (integrable_bounded_lipschitz _ hf D hb)
  have hold := ((hX.average ψ hp D hpb) (ε/2) (by positivity)).prod_fst
    (fun n => Measure.pi (fun _ : Fin n => τ))
  have hnew : ExponentiallyRare
      (fun n => (ρ n).prod (Measure.pi (fun _ : Fin n => τ)))
      (fun n => {z | ε/2 ≤ |((∑ i, f (X n z.1 i,z.2 i)) - ∑ i, ψ (X n z.1 i))/(n:ℝ)|}) := by
    refine ⟨2,ε^2/(8*D^2),by norm_num,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hh := iid_seed_empirical_tail τ (ρ n) hn (X n) (hXm n) f hf.continuous.measurable
      D hD.le hb (ε/2) (by positivity)
    have he : -((ε/2)^2*(n:ℝ))/(2*D^2) = -(ε^2/(8*D^2))*(n:ℝ) := by
      field_simp
      ring
    simpa only [ψ, he, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      using hh
  apply (hold.union hnew).mono
  refine Filter.Eventually.of_forall ?_
  intro n z hz
  change ε ≤ |(∑ i, f (X n z.1 i,z.2 i))/(n:ℝ)-∫ w, f w ∂ν.prod τ| at hz
  rw [hm] at hz
  by_cases ho : ε/2 ≤ dist ((∑ i, ψ (X n z.1 i))/(n:ℝ)) (∫ x, ψ x ∂ν)
  · exact Or.inl ho
  apply Or.inr
  by_contra hn
  have ho' : |(∑ i, ψ (X n z.1 i))/(n:ℝ) - ∫ x, ψ x ∂ν| < ε/2 := lt_of_not_ge ho
  have hn' : |((∑ i, f (X n z.1 i,z.2 i)) - ∑ i, ψ (X n z.1 i))/(n:ℝ)| < ε/2 :=
    lt_of_not_ge hn
  rw [sub_div] at hn'
  have ht := abs_add_le
    ((∑ i, f (X n z.1 i,z.2 i))/(n:ℝ) - (∑ i, ψ (X n z.1 i))/(n:ℝ))
    ((∑ i, ψ (X n z.1 i))/(n:ℝ) - ∫ x, ψ x ∂ν)
  rw [sub_add_sub_cancel] at ht
  linarith

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
