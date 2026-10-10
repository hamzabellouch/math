import OAI.MeasureTheory.Falconer.Slicing.GaussianChartTripleKernelMeasurable

namespace OAI

/-! # Expected mass of nearly dependent retained original triples -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussian_bad_triple_mass (μ : Measure (Space n)) [SFinite μ]
    (G : Set (Space n × Space n)) (E : Set (Space n × Space n × Space n)) (hE : MeasurableSet E)
    {b W K ℓ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hK : 0 ≤ K) (hℓ : (h:ℝ) < ℓ)
    (g k : ℕ) (hW : 8*W/b^2 ≤ 1/(2:ℝ)^g)
    (hretained : ∀ w ∈ E, ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
      b ≤ ‖w.2.1-w.1‖ ∧ b ≤ ‖w.2.2-w.1‖ ∧ (w.1,w.2.2) ∈ G ∧
      Real.sqrt (tripleGram (gnomonicChart w.1 : Space (n+1))
        (gnomonicChart w.2.1 : Space (n+1)) (gnomonicChart w.2.2 : Space (n+1))) < W)
    (hdiag : ∀ p z, (p,z) ∈ G → z ≠ p)
    (hcap : ∀ p, ∀ j : ℕ, j ≤ g+k → ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ)) :
    (∫⁻ A : Fin h → Space (n+1),
      ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^(g+k))).prod
        ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^(g+k))).prod
          (gaussianChartSliceMeasure μ A (1/(2:ℝ)^(g+k))))) E ∂gaussianRows (n+1) h) ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h) *
      ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^((h:ℝ)-ℓ))*
        (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ℓ))))) * (μ univ)^2 := by
  classical
  let r : ℝ := 1/(2:ℝ)^(g+k)
  let F : Space n × Space n × Space n → ℝ≥0∞ :=
    fun w => gaussianChartTripleWeight h r w.1 w.2.1 w.2.2
  let C : ℝ≥0∞ := ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h) *
    ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^((h:ℝ)-ℓ))*
      (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ℓ)))))
  have hm : Measurable (E.indicator F) := (gaussianChartTripleWeight_measurable r).indicator hE
  have hfiber (p q : Space n) : (∫⁻ z, E.indicator F (p,q,z) ∂μ) ≤ C := by
    let T : Set (Space n) := {z | (p,q,z) ∈ E}
    have hT : MeasurableSet T := hE.preimage (by fun_prop)
    have he : (fun z => E.indicator F (p,q,z)) =
        T.indicator (fun z => gaussianChartTripleWeight h r p q z) := rfl
    rw [he,lintegral_indicator hT]
    by_cases ht : T.Nonempty
    · obtain ⟨z,hz⟩ := ht
      obtain ⟨hp,hq,_,hpq,_,_,_⟩ := hretained (p,q,z) hz
      apply anchored_bad_triple_potential μ G T hT p q hp hq hb hb1 hpq hK hℓ g k hW
      · intro y hy
        obtain ⟨_,_,hy1,_,hpy,hG,hgram⟩ := hretained (p,q,y) hy
        exact ⟨hG,hy1,hpy,hgram⟩
      · exact hdiag p
      · exact hcap p
    · have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp ht
      simp only [he,Measure.restrict_empty,lintegral_zero_measure,zero_le]
  rw [gaussian_chart_triple_average μ _ E hE,← lintegral_indicator hE,
    lintegral_prod _ hm.aemeasurable]
  calc
    _ ≤ ∫⁻ p : Space n, ∫⁻ _q : Space n, C ∂μ ∂μ := by
      apply lintegral_mono
      intro p
      calc
        _ = ∫⁻ q : Space n, ∫⁻ z : Space n, E.indicator F (p,q,z) ∂μ ∂μ :=
          lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
        _ ≤ _ := lintegral_mono (hfiber p)
    _ = _ := by
      simp only [lintegral_const]
      change C*μ univ*μ univ = C*(μ univ)^2
      ring

end Falconer

end OAI
