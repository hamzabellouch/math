import Mathlib
import OAI.Probability.Ballisticity.Crossings.TailCuts

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailGrowth

lemma first_tail_threshold (μ : Measure ℤ) [IsFiniteMeasure μ] {q : ℝ}
    (hq : 0 < q) (hqμ : q < μ.real Set.univ) :
    ∃ j : ℤ, q ≤ μ.real (Set.Iic j) ∧ μ.real (Set.Iio j) < q := by
  have htop : Tendsto (fun j : ℤ => μ.real (Set.Iic j)) atTop (𝓝 (μ.real Set.univ)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_Iic_atTop μ)
  have hbot := TailCuts.lower_tendsto μ
  obtain ⟨b,hb⟩ := eventually_atBot.mp (hbot.eventually (gt_mem_nhds hq))
  have hbound : ∃ b : ℤ, ∀ z, q ≤ μ.real (Set.Iic z) → b ≤ z := by
    refine ⟨b,fun z hz => ?_⟩
    by_contra h
    exact (not_lt_of_ge hz) (hb z (le_of_lt (lt_of_not_ge h)))
  have hex : ∃ j : ℤ, q ≤ μ.real (Set.Iic j) :=
    ((htop.eventually (lt_mem_nhds hqμ)).exists).imp fun j hj => hj.le
  obtain ⟨j,hj,hmin⟩ := Int.exists_least_of_bdd hbound hex
  refine ⟨j,hj,?_⟩
  have he : Set.Iio j = Set.Iic (j-1) := by ext z; simp only [Set.mem_Iio,Set.mem_Iic]; omega
  rw [he]
  by_contra h
  have := hmin (j-1) (le_of_not_gt h)
  omega

lemma ordered_pair_common_cut (μ ν : Measure ℤ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.real Set.univ ≤ 1) (hν : ν.real Set.univ ≤ 1)
    (R : ℤ) {q : ℝ} (hq : 0 < q)
    (hpair : q ≤ (μ.prod ν).real {p | p.1 + R ≤ p.2}) :
    ∃ j : ℤ, q / 2 ≤ μ.real (Set.Iic j) ∧ q / 2 ≤ ν.real (Set.Ici (j+R)) := by
  have hqμ : q ≤ μ.real Set.univ := by
    calc
      q ≤ (μ.prod ν).real {p | p.1 + R ≤ p.2} := hpair
      _ ≤ (μ.prod ν).real (Set.univ ×ˢ Set.univ) :=
        measureReal_mono (by intro p hp; exact ⟨Set.mem_univ _,Set.mem_univ _⟩) (measure_ne_top _ _)
      _ = μ.real Set.univ * ν.real Set.univ := measureReal_prod_prod _ _
      _ ≤ μ.real Set.univ * 1 := mul_le_mul_of_nonneg_left hν (measureReal_nonneg)
      _ = μ.real Set.univ := mul_one _
  obtain ⟨j,hj,hprev⟩ := first_tail_threshold μ (by linarith : 0 < q/2) (by linarith : q/2 < μ.real Set.univ)
  refine ⟨j,hj,?_⟩
  by_contra hh
  have hh' : ν.real (Set.Ici (j+R)) < q/2 := lt_of_not_ge hh
  have hsub : {p : ℤ × ℤ | p.1 + R ≤ p.2} ⊆
      (Set.Iio j ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Ici (j+R)) := by
    intro p hp
    by_cases hx : p.1 < j
    · exact Or.inl ⟨hx,Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _,by change j+R ≤ p.2; dsimp at hp; omega⟩
  have hle : q ≤ μ.real (Set.Iio j) + ν.real (Set.Ici (j+R)) := by
    calc
      q ≤ (μ.prod ν).real {p | p.1+R ≤ p.2} := hpair
      _ ≤ (μ.prod ν).real ((Set.Iio j ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Ici (j+R))) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (μ.prod ν).real (Set.Iio j ×ˢ Set.univ) +
          (μ.prod ν).real (Set.univ ×ˢ Set.Ici (j+R)) := measureReal_union_le _ _
      _ = μ.real (Set.Iio j) * ν.real Set.univ + μ.real Set.univ * ν.real (Set.Ici (j+R)) := by
        rw [measureReal_prod_prod,measureReal_prod_prod]
      _ ≤ μ.real (Set.Iio j) * 1 + 1 * ν.real (Set.Ici (j+R)) :=
        add_le_add (mul_le_mul_of_nonneg_left hν measureReal_nonneg)
          (mul_le_mul_of_nonneg_right hμ measureReal_nonneg)
      _ = μ.real (Set.Iio j) + ν.real (Set.Ici (j+R)) := by ring
  linarith

noncomputable def statistic (μ : Measure ℤ) (R : ℤ) : ℝ :=
  ⨆ j : ℤ, TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j

lemma score_bddAbove (μ : Measure ℤ) [IsFiniteMeasure μ] (R : ℤ) :
    BddAbove (Set.range (TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R)) := by
  refine ⟨μ.real Set.univ,?_⟩
  rintro _ ⟨j,rfl⟩
  exact (min_le_left _ _).trans (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))

lemma score_le_statistic (μ : Measure ℤ) [IsFiniteMeasure μ] (R j : ℤ) :
    TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j ≤ statistic μ R :=
  le_ciSup (score_bddAbove μ R) j

lemma statistic_le_mass (μ : Measure ℤ) [IsFiniteMeasure μ] (R : ℤ) :
    statistic μ R ≤ μ.real Set.univ := by
  apply ciSup_le
  intro j
  exact (min_le_left _ _).trans (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))

lemma statistic_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hfull : ∀ j, 0 < μ.real {j}) (R : ℤ) : 0 < statistic μ R := by
  apply lt_of_lt_of_le _ (score_le_statistic μ R 0)
  exact lt_min (TailCuts.lower_pos μ hfull _) (TailCuts.upper_pos μ hfull _)

lemma statistic_eq_max (μ : Measure ℤ) [IsFiniteMeasure μ] (R j : ℤ)
    (hj : ∀ k, TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R k ≤
      TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j) :
    statistic μ R = TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j := by
  exact le_antisymm (ciSup_le hj) (score_le_statistic μ R j)

lemma statistic_grows (μ ν w' : Measure ℤ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure w']
    (hμ : μ.real Set.univ ≤ 1) (hν : ν.real Set.univ ≤ 1)
    (R : ℤ) {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t)
    (hpair : q ≤ (μ.prod ν).real {p | p.1+R ≤ p.2})
    (hleft : ∀ j, t * μ.real (Set.Iic j) ≤ w'.real (Set.Iic j))
    (hright : ∀ j, t * ν.real (Set.Ici j) ≤ w'.real (Set.Ici j)) :
    t * q / 2 ≤ statistic w' R := by
  obtain ⟨j,hj,hj'⟩ := ordered_pair_common_cut μ ν hμ hν R hq hpair
  apply le_trans _ (score_le_statistic w' R j)
  change t*q/2 ≤ min _ _
  exact le_min (by simpa [mul_div_assoc, TailCuts.lower, TailCuts.upper] using (mul_le_mul_of_nonneg_left hj ht).trans (hleft j))
    (by simpa [mul_div_assoc, TailCuts.lower, TailCuts.upper] using (mul_le_mul_of_nonneg_left hj' ht).trans (hright (j+R)))

lemma log_statistic_grows (μ ν w w' : Measure ℤ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure w] [IsFiniteMeasure w']
    (hμ : μ.real Set.univ ≤ 1) (hν : ν.real Set.univ ≤ 1)
    (R : ℤ) {Q C a Z : ℝ} (hw : 0 < statistic w R) (hQ : 0 < Q)
    (hpair : Q ≤ (μ.prod ν).real {p | p.1+R ≤ p.2})
    (hlog : -a-Z ≤ Real.log Q)
    (hleft : ∀ j, (Real.exp C * statistic w R) * μ.real (Set.Iic j) ≤ w'.real (Set.Iic j))
    (hright : ∀ j, (Real.exp C * statistic w R) * ν.real (Set.Ici j) ≤ w'.real (Set.Ici j)) :
    C-a-Z-Real.log 2 ≤ Real.log (statistic w' R) - Real.log (statistic w R) := by
  have ht := mul_pos (Real.exp_pos C) hw
  have hg := statistic_grows μ ν w' hμ hν R hQ ht.le hpair hleft hright
  have hp : 0 < Real.exp C * statistic w R * Q / 2 :=
    div_pos (mul_pos ht hQ) (by norm_num)
  have hh := Real.log_le_log hp hg
  rw [Real.log_div (ne_of_gt (mul_pos ht hQ)) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_mul (ne_of_gt ht) (ne_of_gt hQ),
    Real.log_mul (ne_of_gt (Real.exp_pos C)) (ne_of_gt hw), Real.log_exp] at hh
  linarith

end TailGrowth

end

end OAI
