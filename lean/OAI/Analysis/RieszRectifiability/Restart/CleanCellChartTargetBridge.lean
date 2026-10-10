import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartAreaLoss
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellFinitePieceMassFraction

namespace OAI

/-!
# From clean-cell deficits to ball charts

A relative chart deficit `ζ` leaves at least the fraction `1 - ζ` of a finite
cell's mass in the chart image. For a support ball of radius `r`, a clean cell at
scale `r / 4` lies inside that ball and contains a core of radius `r / 32`.
The lower AD bound supplies the retained mass fraction `(1 - ζ) / (C * 32 ^ n)`;
rescaling the chart domain to radius `r` multiplies its Lipschitz bound by `1 / 4`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem retained_mass_of_chart_deficit {d : ℕ} (μ : Measure (Ambient d))
    (Q T : Set (Ambient d)) (hfinite : μ Q ≠ ⊤) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (hdeficit : μ (Q \ T) ≤ ENNReal.ofReal ζ * μ Q) :
    ENNReal.ofReal (1 - ζ) * μ Q ≤ μ (Q ∩ T) := by
  have hsub : Q ⊆ (Q ∩ T) ∪ (Q \ T) := by
    intro x hx
    by_cases ht : x ∈ T
    · exact Or.inl ⟨hx, ht⟩
    · exact Or.inr ⟨hx, ht⟩
  have hmass : μ Q ≤ μ (Q ∩ T) + μ (Q \ T) + 0 := by
    simpa only [add_zero] using! (measure_mono (μ := μ) hsub).trans (measure_union_le _ _)
  have h := mass_fraction_of_two_deficits _ _ _ 0 hfinite ζ 0 hζ le_rfl hmass hdeficit (by simp)
  simpa only [sub_zero] using! h

theorem uniformlyRectifiable_of_uniform_clean_cell_deficits {n d : ℕ}
    (μ : Measure (Ambient d)) (hAD : ADRegular n μ)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζone : ζ < 1) (M : ℝ≥0)
    (hcharts : ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∃ f : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith M f ∧ μ (cleanSupportCell μ R hR k z \ Set.range f) ≤
          ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z)) : UniformlyRectifiable n μ := by
  obtain ⟨C, hC, hballs⟩ := hAD
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hkeep : 0 < 1 - ζ := sub_pos.mpr hζone
  let θ := (1 - ζ) / (C * 32 ^ n)
  have hθ : 0 < θ := div_pos hkeep (mul_pos hCpos (by positivity))
  refine ⟨θ, hθ, M * (1 / 4), ?_⟩
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

end

end RieszRectifiability

end OAI
