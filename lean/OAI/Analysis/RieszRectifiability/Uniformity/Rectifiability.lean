import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CleanCellChartTargetBridge
import OAI.Analysis.RieszRectifiability.Uniformity.Growth
import OAI.Analysis.RieszRectifiability.Uniformity.SurfacePieces
import OAI.Analysis.RieszRectifiability.Uniformity.RestartBudgets

namespace OAI

/-!
# Quantitative ball images with constants chosen before the measure

Clean-cell charts with relative deficit `ζ` yield genuine ball images with mass
fraction `(1 - ζ) / (C * 32 ^ n)` and the rescaled Lipschitz bound. The final
assembly chooses the surface-piece and restart budgets from the fixed dimension,
AD constant, and common Riesz bound before introducing the measure. Degenerate
supports are handled directly through the admissible-radius condition.
-/

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_ball_images_of_clean_cell_deficits {n d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hAD : ADRegularWithConstant n C μ)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζone : ζ < 1) (M : ℝ≥0)
    (hcharts : ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∃ f : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith M f ∧ μ (cleanSupportCell μ R hR k z \ Set.range f) ≤
          ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z)) : BallImageConclusion n μ ((1 - ζ) / (C * 32 ^ n)) (M * (1 / 4)) := by
  obtain ⟨hC, hballs⟩ := hAD
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hkeep : 0 < 1 - ζ := sub_pos.mpr hζone
  let θ := (1 - ζ) / (C * 32 ^ n)
  have hθ : 0 < θ := div_pos hkeep (mul_pos hCpos (by positivity))
  change BallImageConclusion n μ θ (M * (1 / 4))
  intro x hx r hr
  have hR : 0 < r / 4 := div_pos hr.1 (by norm_num)
  obtain ⟨zc, hzc, hnear⟩ := (supportLatticeNets μ (r / 4) hR 0).covers x hx
  let z : (supportLatticeNets μ (r / 4) hR 0).points := ⟨zc, hzc⟩
  have hrad : latticeRadius (r / 4) 0 = r / 4 := by simp only [latticeRadius, pow_zero, mul_one]
  have hcore : AdmissibleRadius μ (latticeRadius (r / 4) 0 / 8) := by
    refine ⟨div_pos (latticeRadius_pos _ hR 0) (by norm_num), ?_⟩
    apply (ENNReal.ofReal_le_ofReal ?_).trans hr.2
    rw [hrad]
    linarith [hr.1]
  obtain ⟨f, hf, hdeficit⟩ := hcharts (r / 4) hR 0 z hcore
  have hmass := cleanSupportCell_measure_bounds μ C G hCpos hG hg
    (fun y hy s hs => (hballs y hy s hs).1) (r / 4) hR 0 hcore z
  have hfinite : μ (cleanSupportCell μ (r / 4) hR 0 z) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass.2
  have hret := retained_mass_of_chart_deficit μ _ (Set.range f) hfinite ζ hζ hdeficit
  have hcoef : θ * r ^ n = (1 - ζ) * ((latticeRadius (r / 4) 0 / 8) ^ n / C) := by
    rw [hrad]
    change (1 - ζ) / (C * 32 ^ n) * r ^ n = (1 - ζ) * ((r / 4 / 8) ^ n / C)
    rw [div_div, show (4 : ℝ) * 8 = 32 by norm_num, div_pow]
    ring
  have hretained : ENNReal.ofReal (θ * r ^ n) ≤
      μ (cleanSupportCell μ (r / 4) hR 0 z ∩ Set.range f) := by
    rw [hcoef, ENNReal.ofReal_mul hkeep.le]
    exact (mul_le_mul_right hmass.1 (ENNReal.ofReal (1 - ζ))).trans hret
  have hcell : cleanSupportCell μ (r / 4) hR 0 z ⊆ ball x r := by
    intro y hy
    have hdist := (supportLatticeCell_bounds μ (r / 4) hR 0 z).2 hy.1
    change dist y zc ≤ 2 * latticeRadius (r / 4) 0 at hdist
    rw [hrad] at hdist hnear
    have htri := dist_triangle y zc x
    rw [dist_comm zc x] at htri
    change dist y x < r
    linarith [hr.1]
  obtain ⟨F, hF, hFRange⟩ := exists_rescaled_ball_chart (latticeRadius (r / 4) 0)
    (0 : Ambient n) (1 / 4) (by norm_num) f M hf
  have hdomain : latticeRadius (r / 4) 0 / ((1 / 4 : ℝ≥0) : ℝ) = r := by
    rw [hrad]
    norm_num
    ring
  rw [hdomain] at hF hFRange
  let g := (ball (0 : Ambient n) r).domRestrict F
  have hcover : Set.range f ⊆ Set.range g := by
    intro y hy
    obtain ⟨u, hu, hFu⟩ := hFRange.symm ▸ hy
    exact ⟨⟨u, hu⟩, hFu⟩
  refine ⟨g, hF.to_restrict, hretained.trans (measure_mono ?_)⟩
  exact fun y hy => ⟨hcell hy.1, hcover hy.2⟩

theorem quantitative_higher_codimension_riesz_rectifiability : QuantitativeFullStatement := by
  intro d n _hd hn hnd C hC D
  cases n with
  | zero => omega
  | succ p =>
    have hnd' : p + 1 ≤ d := by omega
    let G : ℝ := 9 ^ d * C
    have hG : 0 < G := mul_pos (by positivity) (zero_lt_one.trans_le hC)
    obtain ⟨ε, hε, hεfine, hsmall, hpieces⟩ :=
      quantitative_uniform_restart_surface_pieces (Nat.succ_pos p) hnd' C G hC hG
    obtain ⟨δ, hδ, b, _hb, hcharts⟩ := quantitative_recursive_chart_from_surface_pieces
      hnd' C G D hC hG 1024 ε (by norm_num) hε hεfine hsmall (1 / 2) (by norm_num)
    obtain ⟨N, P, hdata⟩ := hpieces δ hδ
    let M := badBudgetChartConstant
      (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) b
    refine ⟨(1 - (1 / 2 : ℝ)) / (C * 32 ^ (p + 1)),
      div_pos (by norm_num) (mul_pos (zero_lt_one.trans_le hC) (by positivity)),
      M * (1 / 4), ?_⟩
    intro μ hreg hAD hRiesz
    let : μ.Regular := hreg
    by_cases hsupport : μ.support.Nontrivial
    · have hg : GlobalUpperGrowth (p + 1) G μ := quantitative_global_growth hnd' μ C hAD hsupport
      apply quantitative_ball_images_of_clean_cell_deficits μ C hAD G hG hg
        (1 / 2) (by norm_num) (by norm_num) M
      intro R hR k z hcore
      obtain ⟨E, data, hloss⟩ := hdata μ hAD hg R hR k z hcore
      obtain ⟨g, hglip, _, hdeficit⟩ := hcharts N P μ hAD hg hRiesz R hR k z hcore E data hloss
      exact ⟨g, hglip, hdeficit⟩
    · intro x _hx r hr
      have hdiam : ediam μ.support = 0 := ediam_eq_zero_iff.mpr (Set.not_nontrivial_iff.mp hsupport)
      have hz : ENNReal.ofReal r = 0 := le_antisymm (hdiam ▸ hr.2) zero_le
      exact ((ENNReal.ofReal_pos.mpr hr.1).ne' hz).elim

end
end RieszRectifiability

end OAI
