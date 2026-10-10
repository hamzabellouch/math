import OAI.Analysis.Daugavet.ProductModels

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uB uR uIota uKappa

namespace ExactModuli.KW

section ProductModels
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

/-- The representation used in the whole-ball argument. -/
def enlargedFunction (p : ℝ) (x : B → ℝ) (u : κ → B → ℝ) (a : κ → ι → ℝ)
    (z : B × (κ → cube ι)) : ℝ :=
  x z.1 + ∑ k, u k z.1 * rowSum p (a k) (z.2 k)

lemma measurable_enlargedFunction (p : ℝ) {x : B → ℝ} {u : κ → B → ℝ}
    (hx : Measurable x) (hu : ∀ k, Measurable (u k)) (a : κ → ι → ℝ) :
    Measurable (enlargedFunction p x u a) := by
  apply (hx.comp measurable_fst).add
  exact Finset.measurable_sum _ (fun k _ => (hu k |>.comp measurable_fst).mul
    ((measurable_rowSum p (a k)).comp ((measurable_pi_apply k).comp measurable_snd)))

omit [IsProbabilityMeasure μ] in
lemma integrable_enlargedFunction [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 1 < p) {x : B → ℝ} {u : κ → B → ℝ}
    (hx : Integrable x μ) (hu : ∀ k, Integrable (u k) μ) (a : κ → ι → ℝ) :
    Integrable (enlargedFunction p x u a) (μ.prod (arrayMeasure κ ι)) := by
  apply ((measurePreserving_fst.integrable_comp hx.aestronglyMeasurable).mpr hx).add
  apply integrable_finsetSum
  intro k _
  exact (hu k).mul_prod ((measurePreserving_eval (fun _ : κ => cubeMeasure ι) k).integrable_comp
    (integrable_rowSum hp (a k)).aestronglyMeasurable |>.mpr (integrable_rowSum hp (a k)))

omit [MeasurableSpace B] in
lemma resampling_difference [MeasurableSpace B] [DecidableEq κ]
    (p : ℝ) (x : B → ℝ) (u : κ → B → ℝ) (a : κ → ι → ℝ)
    (k : κ) (z : B × (κ → ι → unitInterval × unitInterval)) :
    enlargedFunction p x u a (z.1, selectRows (fun _ => false) z.2) -
      enlargedFunction p x u a (z.1, selectRows (fun l => decide (l = k)) z.2) =
    u k z.1 * diffRowSum p (a k) (z.2 k) := by
  classical
  simp only [enlargedFunction, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · simp [selectRows, rowSum, diffRowSum, difference, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub]
  · intro l _ hl
    have heq : selectRows (fun _ => false) z.2 l = selectRows (fun t => decide (t = k)) z.2 l := by
      funext j
      simp [selectRows, hl]
    rw [heq, sub_self]
  · simp

/-- Resampling controls the coefficients of EVERY representation of a point of the new unit ball. -/
theorem coefficient_bound_108 {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2)
    {x : B → ℝ} {u : κ → B → ℝ} (hx : Integrable x μ)
    (hu : ∀ k, Integrable (u k) μ) (hun : ∀ k, ∫ b, |u k b| ∂μ = 1)
    (a : κ → ι → ℝ)
    (hg : ∫ z, |enlargedFunction p x u a z| ∂(μ.prod (arrayMeasure κ ι)) ≤ 1)
    (k : κ) : coefficientNorm p (a k) ≤ 108 := by
  classical
  let g := enlargedFunction p x u a
  have hgi : Integrable g (μ.prod (arrayMeasure κ ι)) := integrable_enlargedFunction hp hx hu a
  let f₁ := Prod.map (id : B → B) (selectRows (ι := ι) (fun _ : κ => false))
  let f₂ := Prod.map (id : B → B) (selectRows (ι := ι) (fun l : κ => decide (l = k)))
  have hm₁ : MeasurePreserving f₁ (μ.prod (pairedArrayMeasure κ ι)) (μ.prod (arrayMeasure κ ι)) :=
    (MeasurePreserving.id μ).prod (measurePreserving_selectRows _)
  have hm₂ : MeasurePreserving f₂ (μ.prod (pairedArrayMeasure κ ι)) (μ.prod (arrayMeasure κ ι)) :=
    (MeasurePreserving.id μ).prod (measurePreserving_selectRows _)
  have hi₁ : Integrable (fun z => g (f₁ z)) (μ.prod (pairedArrayMeasure κ ι)) :=
    (hm₁.integrable_comp hgi.aestronglyMeasurable).mpr hgi
  have hi₂ : Integrable (fun z => g (f₂ z)) (μ.prod (pairedArrayMeasure κ ι)) :=
    (hm₂.integrable_comp hgi.aestronglyMeasurable).mpr hgi
  have hdiff : (∫ z, |g (f₁ z) - g (f₂ z)| ∂(μ.prod (pairedArrayMeasure κ ι))) ≤ 2 := by
    calc
      _ ≤ ∫ z, |g (f₁ z)| + |g (f₂ z)| ∂(μ.prod (pairedArrayMeasure κ ι)) :=
        integral_mono (hi₁.sub hi₂).abs (hi₁.abs.add hi₂.abs)
          (fun z => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_sub_le (g (f₁ z)) (g (f₂ z)))
      _ = 2 * ∫ z, |g z| ∂(μ.prod (arrayMeasure κ ι)) := by
        rw [integral_add hi₁.abs hi₂.abs, mp_integral hm₁ hgi.abs.aestronglyMeasurable,
          mp_integral hm₂ hgi.abs.aestronglyMeasurable]
        ring
      _ ≤ 2 := by dsimp [g]; linarith
  have hid : (∫ z, |g (f₁ z) - g (f₂ z)| ∂(μ.prod (pairedArrayMeasure κ ι))) =
      ∫ v, |diffRowSum p (a k) v| ∂pairCubeMeasure ι := by
    simp only [g, f₁, f₂, Prod.map_def, id_eq, resampling_difference, abs_mul]
    rw [integral_prod_mul (μ := μ) (ν := pairedArrayMeasure κ ι)
      (fun b => |u k b|) (fun v => |diffRowSum p (a k) (v k)|), hun k, one_mul]
    exact mp_integral (measurePreserving_eval (fun _ : κ => pairCubeMeasure ι) k) (integrable_diffRowSum hp (a k)).abs.aestronglyMeasurable
  rw [hid] at hdiff
  have hl := diffRowSum_lower hp hpmax (a k)
  linarith

/-- Averaging over the resampled copy produces a deterministic center. -/
lemma concentration_center {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {z : R → ℝ} (hz : Measurable z) {r q : ℝ}
    (h : (ν.prod ν).real {v | r < |z v.1 - z v.2|} < q) :
    ∃ c : ℝ, ν.real {v | r < |z v - c|} < q := by
  let S : Set (R × R) := {v | r < |z v.1 - z v.2|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    ((hz.comp measurable_fst).sub (hz.comp measurable_snd)).abs
  have hi : Integrable (S.indicator (1 : R × R → ℝ)) (ν.prod ν) :=
    (integrable_const 1).indicator hS
  have hinner (y : R) : (∫ x, S.indicator (1 : R × R → ℝ) (x, y) ∂ν) =
      ν.real {x | r < |z x - z y|} := by
    have heq : (fun x => S.indicator (1 : R × R → ℝ) (x, y)) =
        {x | r < |z x - z y|}.indicator (1 : R → ℝ) := by
      funext x
      simp [S, Set.indicator_apply]
    rw [heq, integral_indicator_one (measurableSet_lt measurable_const (hz.sub_const (z y)).abs)]
  have htotal : (ν.prod ν).real S = ∫ y, ν.real {x | r < |z x - z y|} ∂ν := by
    rw [← integral_indicator_one hS, integral_prod_symm _ hi]
    simp_rw [hinner]
  by_contra hn
  push Not at hn
  have hint : Integrable (fun y => ν.real {x | r < |z x - z y|}) ν := by
    simpa only [hinner] using hi.integral_prod_right
  have hq := integral_mono (integrable_const q) hint (fun y => hn (z y))
  simp only [integral_const, probReal_univ, one_smul] at hq
  rw [← htotal] at hq
  exact (not_lt_of_ge hq) h

lemma diffRowSum_prod_tail (p : ℝ) (a : ι → ℝ) (r : ℝ) :
    ((cubeMeasure ι).prod (cubeMeasure ι)).real {v | r < |rowSum p a v.1 - rowSum p a v.2|} =
      (pairCubeMeasure ι).real {v | r < |diffRowSum p a v|} := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow unitInterval unitInterval ι
  have he : MeasurePreserving e (pairCubeMeasure ι) ((cubeMeasure ι).prod (cubeMeasure ι)) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ _ _
  have heq := he.measure_preimage (s := {v | r < |rowSum p a v.1 - rowSum p a v.2|}) (measurableSet_lt measurable_const
    (((measurable_rowSum p a).comp measurable_fst).sub
      ((measurable_rowSum p a).comp measurable_snd)).abs).nullMeasurableSet
  have hset : e ⁻¹' {v | r < |rowSum p a v.1 - rowSum p a v.2|} =
      {v | r < |diffRowSum p a v|} := by
    ext v
    change (r < |rowSum p a (fun j => (v j).1) - rowSum p a (fun j => (v j).2)|) ↔ _
    simp [rowSum, diffRowSum, difference, Finset.sum_sub_distrib, mul_sub]
  simp only [measureReal_def, ← heq, hset]

lemma rowSum_concentration {p r q : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2)
    (hr : 0 < r) (hpq : 10 * (108 * scale p / r) ^ p < q)
    (a : ι → ℝ) (ha : coefficientNorm p a ≤ 108) :
    ∃ c : ℝ, (cubeMeasure ι).real {v | r < |rowSum p a v - c|} < q := by
  apply concentration_center (measurable_rowSum p a)
  rw [diffRowSum_prod_tail]
  apply lt_of_le_of_lt (diffRowSum_tail hp hpmax a hr)
  apply lt_of_le_of_lt _ hpq
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow
  · exact div_nonneg (mul_nonneg (scale_pos hp).le (coefficientNorm_nonneg p a)) hr.le
  · apply div_le_div_of_nonneg_right _ hr.le
    nlinarith [scale_pos hp]
  · linarith

lemma abs_add_lower (a b : ℝ) : |a| + |b| - 2 * min |a| |b| ≤ |a + b| := by
  have h₁ : |a| ≤ |a + b| + |b| := by
    simpa only [Real.norm_eq_abs, add_neg_cancel_right, abs_neg] using (norm_add_le (a + b) (-b))
  have h₂ : |b| ≤ |a| + |a + b| := by
    simpa only [Real.norm_eq_abs, neg_add_cancel_left, abs_neg] using (norm_add_le (-a) (a + b))
  rcases le_total |a| |b| with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

end ProductModels
end ExactModuli.KW

end

end OAI
