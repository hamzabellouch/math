import OAI.Probability.LatticePassage.EfronStein
import OAI.Probability.LatticePassage.FiniteResampling
import OAI.Probability.LatticePassage.LocalizationMean

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma integrable_finitePassageTime (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    Integrable (finitePassageTime x y R)
      (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) := by
  have h₁ := integrable_map_measure (μ := environmentLaw) (g := (id : ℝ → ℝ))
    aestronglyMeasurable_id (measurable_localPassageTime x y R).aemeasurable
  have h₂ := integrable_map_measure (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (g := (id : ℝ → ℝ))
    aestronglyMeasurable_id (measurable_finitePassageTime x y R).aemeasurable
  rw [finitePassageTime_law] at h₁
  exact h₂.mp (h₁.mpr (integrable_localPassageTime x y R hR))

theorem finitePassageTime_centered_lmoment (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    (∫⁻ v : LocalCoordinates x R, ENNReal.ofReal
      ((finitePassageTime x y R v - ∫ w, finitePassageTime x y R w
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))^2)
      ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) ≤ 4*(R : ℝ≥0∞) := by
  classical
  apply (centered_square_lintegral_le_resampling (expMeasure 1)
    (measurable_finitePassageTime x y R) (integrable_finitePassageTime x y R hR)).trans
  have h := finite_absolute_resampling_lmoment x y R hR 2 (by omega)
  norm_num [sq_abs] at h
  exact h

lemma finitePassageTime_mean (x y : Vertex) (R : ℕ) :
    (∫ v, finitePassageTime x y R v
      ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) =
    ∫ ω, localPassageTime ω x y R ∂environmentLaw := by
  have h₁ := integral_map (μ := environmentLaw)
    (measurable_localPassageTime x y R).aemeasurable (f := (id : ℝ → ℝ)) aestronglyMeasurable_id
  have h₂ := integral_map (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))
    (measurable_finitePassageTime x y R).aemeasurable (f := (id : ℝ → ℝ)) aestronglyMeasurable_id
  rw [finitePassageTime_law] at h₁
  exact h₂.symm.trans h₁

theorem localPassageTime_centered_lmoment (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    (∫⁻ ω : Environment, ENNReal.ofReal
      ((localPassageTime ω x y R - ∫ η, localPassageTime η x y R ∂environmentLaw)^2)
      ∂environmentLaw) ≤ 4*(R : ℝ≥0∞) := by
  let g := fun a : ℝ => ENNReal.ofReal
    ((a - ∫ η, localPassageTime η x y R ∂environmentLaw)^2)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have h₁ := lintegral_map (μ := environmentLaw) hg (measurable_localPassageTime x y R)
  have h₂ := lintegral_map
    (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) hg
    (measurable_finitePassageTime x y R)
  rw [finitePassageTime_law] at h₁
  have he := h₁.symm.trans h₂
  change (∫⁻ ω, g (localPassageTime ω x y R) ∂environmentLaw) ≤ _
  rw [he]
  dsimp [g]
  rw [← finitePassageTime_mean]
  exact finitePassageTime_centered_lmoment x y R hR

lemma centered_square_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) (s : ℝ) (hs : 0 < s) :
    μ {v | s ≤ |f v - ∫ w, f w ∂μ|} ≤
      (∫⁻ v, ENNReal.ofReal ((f v - ∫ w, f w ∂μ)^2) ∂μ) / ENNReal.ofReal (s^2) := by
  have hm := meas_ge_le_lintegral_div (μ := μ)
    (f := fun v => ENNReal.ofReal ((f v - ∫ w, f w ∂μ)^2))
    (by fun_prop) (ε := ENNReal.ofReal (s^2)) (by positivity) ENNReal.ofReal_ne_top
  apply (measure_mono (show {v | s ≤ |f v - ∫ w, f w ∂μ|} ⊆
      {v | ENNReal.ofReal (s^2) ≤ ENNReal.ofReal ((f v - ∫ w, f w ∂μ)^2)} from ?_)).trans hm
  intro v hv
  apply ENNReal.ofReal_le_ofReal
  have h := pow_le_pow_left₀ hs.le hv 2
  simpa only [sq_abs] using h

lemma sqrt_scale_ratio (R : ℕ) (hR : 0 < R) (t : ℝ) :
    (4*(R : ℝ≥0∞)) / ENNReal.ofReal ((t*sqrt R)^2) = 4/ENNReal.ofReal (t^2) := by
  rw [mul_pow, sq_sqrt (Nat.cast_nonneg R), ENNReal.ofReal_mul (sq_nonneg t),
    ENNReal.ofReal_natCast]
  exact ENNReal.mul_div_mul_right _ _ (by exact_mod_cast hR.ne') (by finiteness)

theorem finitePassageTime_centered_sqrt_tail (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))
      {v | t*sqrt R ≤ |finitePassageTime x y R v - ∫ w, finitePassageTime x y R w
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)|} ≤
      4/ENNReal.ofReal (t^2) := by
  have hpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hR
  have hs : 0 < t*sqrt R := mul_pos ht (sqrt_pos.mpr (by exact_mod_cast hpos))
  apply (centered_square_markov _ _ (measurable_finitePassageTime x y R) _ hs).trans
  calc
    _ ≤ (4*(R : ℝ≥0∞))/ENNReal.ofReal ((t*sqrt R)^2) := by
      gcongr
      exact finitePassageTime_centered_lmoment x y R hR
    _ = _ := sqrt_scale_ratio R hpos t

theorem localPassageTime_centered_sqrt_tail (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (t : ℝ) (ht : 0 < t) :
    environmentLaw {ω | t*sqrt R ≤ |localPassageTime ω x y R -
      ∫ η, localPassageTime η x y R ∂environmentLaw|} ≤ 4/ENNReal.ofReal (t^2) := by
  have hpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hR
  have hs : 0 < t*sqrt R := mul_pos ht (sqrt_pos.mpr (by exact_mod_cast hpos))
  apply (centered_square_markov _ _ (measurable_localPassageTime x y R) _ hs).trans
  calc
    _ ≤ (4*(R : ℝ≥0∞))/ENNReal.ofReal ((t*sqrt R)^2) := by
      gcongr
      exact localPassageTime_centered_lmoment x y R hR
    _ = _ := sqrt_scale_ratio R hpos t

end CompanionFPP

end OAI
