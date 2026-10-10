import OAI.Analysis.Daugavet.Enlargement

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uX u_1 uB

namespace ExactModuli

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measureDistance_self (f : Lp ℝ 1 μ) : measureDistance μ f f = 0 := by
  apply le_antisymm _ (measureDistance_nonneg f f)
  apply le_of_forall_pos_le_add
  intro ε hε
  simpa only [zero_add] using (measureDistance_le_of_tail f f hε (by simpa [not_lt_of_ge hε.le] using hε))

omit [IsProbabilityMeasure μ] in
lemma measureDistance_symm [IsProbabilityMeasure μ] (f g : Lp ℝ 1 μ) :
    measureDistance μ f g = measureDistance μ g f := by
  simp only [measureDistance, abs_sub_comm (f _) (g _)]

lemma measureDistance_triangle (f g k : Lp ℝ 1 μ) :
    measureDistance μ f k ≤ measureDistance μ f g + measureDistance μ g k := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let a := measureDistance μ f g + ε / 2
  let b := measureDistance μ g k + ε / 2
  have ha : 0 < a := by dsimp [a]; linarith [measureDistance_nonneg f g]
  have hb : 0 < b := by dsimp [b]; linarith [measureDistance_nonneg g k]
  have hfa := tail_lt_of_measureDistance_lt f g (show measureDistance μ f g < a by dsimp [a]; linarith)
  have hgb := tail_lt_of_measureDistance_lt g k (show measureDistance μ g k < b by dsimp [b]; linarith)
  have hsub : {ω | a + b < |f ω - k ω|} ⊆
      {ω | a < |f ω - g ω|} ∪ {ω | b < |g ω - k ω|} := by
    intro ω hω
    by_contra hh
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hh
    have ht : |f ω - k ω| ≤ |f ω - g ω| + |g ω - k ω| := abs_sub_le _ _ _
    exact (not_lt_of_ge (ht.trans (add_le_add hh.1 hh.2))) hω
  have htail : μ.real {ω | a + b < |f ω - k ω|} < a + b :=
    (measureReal_mono hsub).trans_lt ((measureReal_union_le _ _).trans_lt (add_lt_add hfa hgb))
  have hh := measureDistance_le_of_tail f k (add_pos ha hb) htail
  dsimp [a,b] at hh
  linarith

/-- Markov's norm-to-measure estimate, in a form avoiding an unnecessary metric instance. -/
lemma measureDistance_le_of_norm_sub_lt_sq (f g : Lp ℝ 1 μ) {ε : ℝ} (hε : 0 < ε)
    (hfg : ‖f - g‖ < ε ^ 2) : measureDistance μ f g ≤ ε := by
  have hi : Integrable (fun ω => |f ω - g ω|) μ :=
    ((L1.integrable_coeFn f).sub (L1.integrable_coeFn g)).abs
  have hint : (∫ ω, |f ω - g ω| ∂μ) = ‖f - g‖ := by
    exact (KW.L1_norm_of_ae (f-g) (Lp.coeFn_sub f g)).symm
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (fun ω => abs_nonneg (f ω-g ω))) hi ε
  rw [hint] at hm
  have hle : μ.real {ω | ε ≤ |f ω - g ω|} < ε := by nlinarith
  apply measureDistance_le_of_tail f g hε
  exact (measureReal_mono (μ := μ) (show {ω | ε < |f ω-g ω|} ⊆ {ω | ε ≤ |f ω-g ω|} from by
    intro ω hω
    change ε < |f ω-g ω| at hω
    change ε ≤ |f ω-g ω|
    exact hω.le)).trans_lt hle

end ExactModuli

namespace ExactModuli.KW

lemma normalizeL1_approx {B : Type uB} [MeasurableSpace B] {μ : Measure B}
    (x y : Lp ℝ 1 μ) (hx : ‖x‖ ≤ 1) :
    ‖x - normalizeL1 y‖ ≤ 2 * ‖x-y‖ := by
  by_cases hy : ‖y‖ ≤ 1
  · simp only [normalizeL1, max_eq_left hy, inv_one, one_smul]
    linarith [norm_nonneg (x-y)]
  have hyp : 0 < ‖y‖ := by linarith
  have hinv : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hyp).mpr (le_of_not_ge hy)
  have hcost : ‖y - normalizeL1 y‖ = ‖y‖ - 1 := by
    calc
      _ = ‖(1 - ‖y‖⁻¹) • y‖ := by
        rw [normalizeL1, max_eq_right (le_of_not_ge hy), sub_smul, one_smul]
      _ = (1 - ‖y‖⁻¹) * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hinv)]
      _ = ‖y‖ - 1 := by rw [sub_mul, one_mul, inv_mul_cancel₀ hyp.ne']
  calc
    ‖x - normalizeL1 y‖ ≤ ‖x-y‖ + ‖y-normalizeL1 y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x-y‖ := by
      rw [hcost]
      have ht := norm_sub_norm_le y x
      rw [norm_sub_rev] at ht
      linarith

lemma sphere_normalize_approx {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x y : X) (hx : ‖x‖ = 1) (hy : y ≠ 0) :
    ‖x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x-y‖ := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hcost : ‖y - ‖y‖⁻¹ • y‖ = |‖y‖ - 1| := by
    calc
      _ = ‖(1 - ‖y‖⁻¹) • y‖ := by rw [sub_smul, one_smul]
      _ = |(1 - ‖y‖⁻¹) * ‖y‖| := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg y)]
      _ = |‖y‖ - 1| := by rw [sub_mul, one_mul, inv_mul_cancel₀ hyp.ne']
  calc
    ‖x - ‖y‖⁻¹ • y‖ ≤ ‖x-y‖ + ‖y-‖y‖⁻¹ • y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x-y‖ := by
      rw [hcost, ← hx]
      have ht := abs_norm_sub_norm_le y x
      rw [norm_sub_rev] at ht
      linarith

end ExactModuli.KW

end

end OAI
