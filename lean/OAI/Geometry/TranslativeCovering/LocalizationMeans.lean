import OAI.Geometry.TranslativeCovering.LocalizationRates

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace LocalizationMeans
open Set MeasureTheory Metric SourceParameters LocalizationRates LatticeAveraging LocalizationGood
open scoped ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
lemma count_mean {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) {r R : ℝ} (hr : 0≤r) (_hR : 0≤R)
    (hρ : ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a) ≤ ENNReal.ofReal (R/(2*v))) :
    ∫⁻ y,field Λ p (countFn (closedBall (0:Space n) r)) y ∂uniformWindow F ≤
      ENNReal.ofReal ((r/a)^n*(R/(2*v))) := by
  unfold countFn
  rw [normalized_averaging Λ hF p (measurable_const.indicator measurableSet_closedBall)]
  simp only [lintegral_indicator measurableSet_closedBall,lintegral_const,
    Measure.restrict_apply_univ,one_mul]
  rw [ball_scale a_pos hr]
  calc
    _ = ENNReal.ofReal ((r/a)^n)*(((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a)) := by ac_rfl
    _ ≤ ENNReal.ofReal ((r/a)^n)*ENNReal.ofReal (R/(2*v)) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (pow_nonneg (div_nonneg hr a_pos.le) _)).symm

lemma bounds {n : ℕ} [NeZero n] {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2)
    (hr : 0<rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
    (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
    (hρ : ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a) ≤ ENNReal.ofReal (R/(2*v))) :
    uniformWindow F (good Λ p a (rminus n) (β n) (ENNReal.ofReal (Cloc*R)))ᶜ ≤ 1/100 ∧
    (∫⁻ y,field Λ p (countFn (closedBall (0:Space n) (W n))) y ∂uniformWindow F) ≤ (N n R:ℝ≥0∞)/40 := by
  have hR0 : 0<R := lt_of_lt_of_le (by norm_num) hR
  have hv : 0<v := by norm_num [v]
  have hCloc : 0<Cloc := by norm_num [Cloc,v]
  have hC : 0<Cloc*R := mul_pos hCloc hR0
  let := probability_window hF0 hFtop
  have hnum (q : ℝ) (hq : 0≤q) : ENNReal.ofReal (q*(R/(2*v))) = ENNReal.ofReal (Cloc*R)*(ENNReal.ofReal (q/2000)) := by
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    dsimp [Cloc]
    field_simp
    ring
  have hout : ∫⁻ y,field Λ p (countFn (closedBall (0:Space n) (β n))) y ∂uniformWindow F ≤ ENNReal.ofReal (Cloc*R)*(3/2000) := by
    calc
      _ ≤ ENNReal.ofReal ((β n/a)^n*(R/(2*v))) := count_mean Λ p hF hβ.le hR0.le hρ
      _ ≤ ENNReal.ofReal (3*(R/(2*v))) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right houter (by positivity))
      _ = _ := by rw [hnum 3 (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2000)]; norm_num
  have hin : ∫⁻ y,field Λ p (countFn (ball (0:Space n) (rminus n))) y ∂uniformWindow F ≤ 1/200 := by
    have hm : ∀ y,field Λ p (countFn (ball (0:Space n) (rminus n))) y ≤ field Λ p (countFn (closedBall (0:Space n) (rminus n))) y := by
      intro y
      apply Finset.sum_le_sum
      intro i _
      apply ENNReal.tsum_le_tsum
      intro l
      exact Set.indicator_le_indicator_of_subset ball_subset_closedBall (fun _ => bot_le) _
    calc
      _ ≤ ∫⁻ y,field Λ p (countFn (closedBall (0:Space n) (rminus n))) y ∂uniformWindow F := lintegral_mono hm
      _ ≤ ENNReal.ofReal ((rminus n/a)^n*(R/(2*v))) := count_mean Λ p hF hr.le hR0.le hρ
      _ ≤ ENNReal.ofReal (1/200) := ENNReal.ofReal_le_ofReal (by
        calc
          _ ≤ (rminus n/a)^n*((n:ℝ)^2/(2*v)) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hRn (by positivity)) (pow_nonneg (div_nonneg hr.le a_pos.le) _)
          _ ≤ _ := by simpa only [mul_comm] using hinner)
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<200)]; norm_num
  have hweight : ∫⁻ y,field Λ p (weightedFn a (β n)) y ∂uniformWindow F ≤ ENNReal.ofReal (Cloc*R)*(5/2000) := by
    rw [normalized_averaging Λ hF p (measurable_weightedFn a (β n))]
    have hVβ : volume (closedBall (0:Space n) (β n)) ≤ 3*volume (closedBall (0:Space n) a) := by
      rw [ball_scale a_pos hβ.le]
      gcongr
      simpa using ENNReal.ofReal_le_ofReal houter
    calc
      _ ≤ ((Fintype.card I:ℝ≥0∞)/volume F)*(volume (closedBall (0:Space n) (β n))+2*volume (closedBall (0:Space n) a)) := by gcongr; exact WeightedVolume.weighted_lintegral a_pos
      _ ≤ ((Fintype.card I:ℝ≥0∞)/volume F)*(3*volume (closedBall (0:Space n) a)+2*volume (closedBall (0:Space n) a)) := by gcongr
      _ = 5*(((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a)) := by ring
      _ ≤ 5*ENNReal.ofReal (R/(2*v)) := by gcongr
      _ = ENNReal.ofReal (5*(R/(2*v))) := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]; norm_num
      _ = _ := by rw [hnum 5 (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2000)]; norm_num
  refine ⟨bad_bound Λ p a (rminus n) (β n) _ (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top (uniformWindow F) hin hout hweight,?_⟩
  have hW0 : 0<W n := by simpa only [W,β,add_assoc] using add_pos D_pos hβ
  have hWL : W n≤L n := by
    have he : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
    dsimp [W,L]; linarith only [he]
  have hceil : 20*R/v*(L n/a)^n≤(N n R:ℝ) := Nat.le_ceil _
  calc
    _ ≤ ENNReal.ofReal ((W n/a)^n*(R/(2*v))) := count_mean Λ p hF hW0.le hR0.le hρ
    _ ≤ ENNReal.ofReal ((N n R:ℝ)/40) := ENNReal.ofReal_le_ofReal (by
      have hh : (W n/a)^n≤(L n/a)^n := pow_le_pow_left₀ (div_nonneg hW0.le a_pos.le) (div_le_div_of_nonneg_right hWL a_pos.le) n
      have h1 := mul_le_mul_of_nonneg_right hh (show 0≤R/(2*v) by positivity)
      have he : (L n/a)^n*(R/(2*v)) = (20*R/v*(L n/a)^n)/40 := by ring
      rw [he] at h1
      exact h1.trans (div_le_div_of_nonneg_right hceil (by norm_num)))
    _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<40)]; norm_num
end LocalizationMeans

end OAI
