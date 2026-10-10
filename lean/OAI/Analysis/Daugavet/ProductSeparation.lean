import OAI.Analysis.Daugavet.WholeBallCoefficients

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uB uR uIota uKappa

namespace ExactModuli.KW

section ProductModels
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

/-- Near-disjointness from every old unit vector, using only the new scalar tail. -/
lemma near_additivity {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {w u : B → ℝ} {f : R → ℝ}
    (hw : Integrable w μ) (hu : Integrable u μ) (hf : Integrable f ν)
    (hfm : Measurable f) (hf0 : ∀ v, 0 ≤ f v)
    (hw1 : ∫ b, |w b| ∂μ = 1) (hu1 : ∫ b, |u b| ∂μ = 1)
    (hf1 : ∫ v, f v ∂ν = 1) {c : ℝ} (hc : 0 ≤ c) :
    2 - 2 * (ν.real {v | c < f v} + c) ≤
      ∫ z : B × R, |w z.1 + u z.1 * f z.2| ∂(μ.prod ν) := by
  let S := {v | c < f v}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hfm
  let W : B × R → ℝ := fun z => w z.1
  let V : B × R → ℝ := fun z => u z.1 * f z.2
  let A : B × R → ℝ := fun z => |w z.1| * S.indicator (1 : R → ℝ) z.2
  let C : B × R → ℝ := fun z => c * |u z.1|
  have hW : Integrable W (μ.prod ν) := (measurePreserving_fst.integrable_comp hw.aestronglyMeasurable).mpr hw
  have hV : Integrable V (μ.prod ν) := hu.mul_prod hf
  have hA : Integrable A (μ.prod ν) := hw.abs.mul_prod ((integrable_const 1).indicator hS)
  have hC : Integrable C (μ.prod ν) :=
    ((measurePreserving_fst.integrable_comp hu.abs.aestronglyMeasurable).mpr hu.abs).const_mul c
  have hpoint (z : B × R) : |W z| + |V z| - 2 * (A z + C z) ≤ |W z + V z| := by
    apply le_trans _ (abs_add_lower _ _)
    have hmin : min |W z| |V z| ≤ A z + C z := by
      by_cases hz : z.2 ∈ S
      · simp only [A, Set.indicator_of_mem hz, Pi.one_apply, mul_one, C]
        exact (min_le_left _ _).trans (le_add_of_nonneg_right (mul_nonneg hc (abs_nonneg _)))
      · have hfz : f z.2 ≤ c := le_of_not_gt hz
        simp only [A, Set.indicator_of_notMem hz, mul_zero, zero_add, C]
        apply (min_le_right _ _).trans
        dsimp [V]
        rw [abs_mul, abs_of_nonneg (hf0 _), mul_comm c]
        exact mul_le_mul_of_nonneg_left hfz (abs_nonneg _)
    linarith
  have hineq := integral_mono ((hW.abs.add hV.abs).sub ((hA.add hC).const_mul 2))
    (hW.add hV).abs hpoint
  have hWi : (∫ z, |W z| ∂(μ.prod ν)) = 1 :=
    (mp_integral measurePreserving_fst hw.abs.aestronglyMeasurable).trans hw1
  have hVi : (∫ z, |V z| ∂(μ.prod ν)) = 1 := by
    simp only [V, abs_mul, abs_of_nonneg (hf0 _)]
    rw [integral_prod_mul (fun b => |u b|) f, hu1, hf1, one_mul]
  have hAi : (∫ z, A z ∂(μ.prod ν)) = ν.real S := by
    rw [show A = (fun z : B × R => |w z.1| * S.indicator (1 : R → ℝ) z.2) from rfl,
      integral_prod_mul (fun b => |w b|) (S.indicator (1 : R → ℝ)), hw1, one_mul, integral_indicator_one hS]
  have hCi : (∫ z, C z ∂(μ.prod ν)) = c := by
    dsimp [C]
    rw [integral_const_mul, mp_integral measurePreserving_fst hu.abs.aestronglyMeasurable, hu1, mul_one]
  simp only [Pi.sub_apply, Pi.add_apply] at hineq
  rw [integral_sub (f := fun z => |W z| + |V z|) (g := fun z => 2 * (A z + C z)) (hW.abs.add hV.abs) ((hA.add hC).const_mul 2),
    integral_add hW.abs hV.abs, integral_const_mul, integral_add hA hC, hWi, hVi, hAi, hCi] at hineq
  simpa only [W, V, S, show (1 : ℝ) + 1 = 2 by norm_num] using hineq

/-- Radial retraction to the old L1 unit ball, pointwise on representatives. -/
def normalizeFunction (μ : Measure B) (f : B → ℝ) (b : B) : ℝ :=
  f b / max 1 (∫ b, |f b| ∂μ)

omit [IsProbabilityMeasure μ] in
lemma integrable_normalizeFunction [IsProbabilityMeasure μ]
    {f : B → ℝ} (hf : Integrable f μ) :
    Integrable (normalizeFunction μ f) μ := hf.div_const _

omit [IsProbabilityMeasure μ] in
lemma normalizeFunction_bounds [IsProbabilityMeasure μ]
    {f : B → ℝ} (_hf : Integrable f μ) {R : ℝ}
    (hR : 1 ≤ R) (hN : (∫ b, |f b| ∂μ) ≤ R) :
    (∫ b, |normalizeFunction μ f b| ∂μ) ≤ 1 ∧
    (∫ b, |f b - normalizeFunction μ f b| ∂μ) ≤ R - 1 := by
  let N := ∫ b, |f b| ∂μ
  have hN0 : 0 ≤ N := integral_nonneg (fun b => abs_nonneg _)
  by_cases hN1 : N ≤ 1
  · have heq : normalizeFunction μ f = f := by
      funext b
      change f b / max 1 N = f b
      rw [max_eq_left hN1, div_one]
    rw [heq]
    constructor
    · exact hN1
    · simp only [sub_self, abs_zero, integral_zero]
      linarith
  · have hNpos : 0 < N := by linarith
    have hNgt : 1 < N := lt_of_not_ge hN1
    have heq : normalizeFunction μ f = fun b => f b / N := by
      funext b
      change f b / max 1 N = f b / N
      rw [max_eq_right hNgt.le]
    rw [heq]
    constructor
    · simp only [abs_div, abs_of_pos hNpos]
      rw [integral_div]
      change N / N ≤ 1
      simp [hNpos.ne']
    · have hpoint (b : B) : |f b - f b / N| = ((N - 1) / N) * |f b| := by
        have he : f b - f b / N = ((N - 1) / N) * f b := by field_simp
        rw [he, abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hNgt.le) hNpos.le)]
      simp_rw [hpoint]
      rw [integral_const_mul]
      change (N - 1) / N * N ≤ R - 1
      rw [div_mul_cancel₀ _ hNpos.ne']
      exact sub_le_sub_right hN 1

/-- Markov's inequality after discarding a small exceptional set. -/
lemma restricted_markov {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsFiniteMeasure ν] {f b : R → ℝ} (hf : Integrable f ν) (hb : Integrable b ν)
    (hf0 : ∀ v, 0 ≤ f v) (hb0 : ∀ v, 0 ≤ b v)
    {D : Set R} (hD : MeasurableSet D) (hdom : ∀ v ∈ D, f v ≤ b v)
    {h : ℝ} (hh : 0 < h) :
    ν.real {v | h < f v} ≤ ν.real Dᶜ + (∫ v, b v ∂ν) / h := by
  classical
  let T := D.indicator f
  have hT : Integrable T ν := hf.indicator hD
  have hT0 : ∀ v, 0 ≤ T v := fun v => Set.indicator_nonneg (fun v _ => hf0 v) v
  have hTb (v : R) : T v ≤ b v := by
    by_cases hv : v ∈ D
    · simpa only [T, Set.indicator_of_mem hv] using hdom v hv
    · simpa only [T, Set.indicator_of_notMem hv] using hb0 v
  have hbound := (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hT0) hT h).trans
    (integral_mono hT hb hTb)
  have hprob : ν.real {v | h ≤ T v} ≤ (∫ v, b v ∂ν) / h := by
    apply (le_div_iff₀ hh).mpr
    simpa only [mul_comm] using hbound
  have hsub : {v | h < f v} ⊆ Dᶜ ∪ {v | h ≤ T v} := by
    intro v hv
    change h < f v at hv
    by_cases hvD : v ∈ D
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq, T, Set.indicator_of_mem hvD] using hv.le)
    · exact Or.inl hvD
  exact (measureReal_mono (μ := ν) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl hprob))

/-- Fubini on the good event controls the old approximant before normalization. -/
lemma old_norm_on_good_set {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {g : B × R → ℝ} {ψ U : B → ℝ}
    (hg : Integrable g (μ.prod ν)) (hψ : Integrable ψ μ) (hU : Integrable U μ)
    (_hU0 : ∀ b, 0 ≤ U b) {m r : ℝ} (hm : ∫ b, U b ∂μ = m) (_hr : 0 ≤ r)
    (hg1 : ∫ z, |g z| ∂(μ.prod ν) ≤ 1)
    {D : Set R} (hD : MeasurableSet D) (hDpos : 0 < ν.real D)
    (hgood : ∀ b v, v ∈ D → |g (b, v) - ψ b| ≤ r * U b) :
    (∫ b, |ψ b| ∂μ) ≤ r * m + 1 / ν.real D := by
  let J := D.indicator (1 : R → ℝ)
  have hJ : Integrable J ν := (integrable_const 1).indicator hD
  have hA : Integrable (fun z : B × R => |ψ z.1| * J z.2) (μ.prod ν) := hψ.abs.mul_prod hJ
  have hC : Integrable (fun z : B × R => (r * U z.1) * J z.2) (μ.prod ν) := (hU.const_mul r).mul_prod hJ
  have hpoint (z : B × R) : |ψ z.1| * J z.2 ≤ |g z| + (r * U z.1) * J z.2 := by
    by_cases hz : z.2 ∈ D
    · simp only [J, Set.indicator_of_mem hz, Pi.one_apply, mul_one]
      have ht : |ψ z.1| ≤ |g z| + |g z - ψ z.1| := by
        simpa only [Real.norm_eq_abs, sub_sub_cancel] using norm_sub_le (g z) (g z - ψ z.1)
      exact ht.trans (add_le_add le_rfl (hgood z.1 z.2 hz))
    · simp only [J, Set.indicator_of_notMem hz, mul_zero, add_zero]
      exact abs_nonneg _
  have hineq := integral_mono hA (hg.abs.add hC) hpoint
  simp only [Pi.add_apply] at hineq
  rw [integral_prod_mul (fun b => |ψ b|) J, integral_add hg.abs hC,
    integral_prod_mul (fun b => r * U b) J, integral_const_mul, hm,
    show (∫ v, J v ∂ν) = ν.real D from integral_indicator_one hD] at hineq
  have hlin : ((∫ b, |ψ b| ∂μ) - r * m) * ν.real D ≤ 1 := by nlinarith
  have hdiv := (le_div_iff₀ hDpos).mpr hlin
  linarith

end ProductModels
end ExactModuli.KW

end

end OAI
