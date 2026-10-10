import OAI.MeasureTheory.Falconer.Estimates.EndpointBadTriples
import OAI.MeasureTheory.Falconer.Radial.RadialPairSeparation

namespace OAI

/-! # The actual measurable bad-triple relation on retained original labels -/

namespace Falconer
open Set MeasureTheory
variable {n : ℕ}

noncomputable def chartTripleVolume (w : Space n × Space n × Space n) : ℝ :=
  Real.sqrt (tripleGram (gnomonicChart w.1 : Space (n+1))
    (gnomonicChart w.2.1 : Space (n+1)) (gnomonicChart w.2.2 : Space (n+1)))

lemma chartTripleVolume_measurable : Measurable (chartTripleVolume (n := n)) := by
  have h₁ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.1 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp measurable_fst)
  have h₂ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.2.1 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
  have h₃ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.2.2 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
  unfold chartTripleVolume tripleGram
  simp only [Matrix.det_fin_three,Matrix.gram_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  fun_prop

def badChartTriples (G : Set (Space n × Space n)) (W : ℝ) :
    Set (Space n × Space n × Space n) :=
  {w | ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
    (w.1,w.2.1) ∈ G ∧ (w.1,w.2.2) ∈ G ∧ chartTripleVolume w < W}

lemma badChartTriples_measurable {G : Set (Space n × Space n)} (hG : MeasurableSet G)
    (W : ℝ) : MeasurableSet (badChartTriples G W) := by
  have h₁ := hG.preimage (show Measurable (fun w : Space n × Space n × Space n =>
    (w.1,w.2.1)) from by fun_prop)
  have h₂ := hG.preimage (show Measurable (fun w : Space n × Space n × Space n =>
    (w.1,w.2.2)) from by fun_prop)
  have hn₁ : MeasurableSet {w : Space n × Space n × Space n | ‖w.1‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hn₂ : MeasurableSet {w : Space n × Space n × Space n | ‖w.2.1‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hn₃ : MeasurableSet {w : Space n × Space n × Space n | ‖w.2.2‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  exact hn₁.inter (hn₂.inter (hn₃.inter
    (h₁.inter (h₂.inter (measurableSet_lt chartTripleVolume_measurable measurable_const)))))

lemma badChartTriples_retained (G : Set (Space n × Space n)) (W b : ℝ)
    (hsep : ∀ p z, (p,z) ∈ G → b ≤ dist p z) :
    ∀ w ∈ badChartTriples G W, ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
      b ≤ ‖w.2.1-w.1‖ ∧ b ≤ ‖w.2.2-w.1‖ ∧ (w.1,w.2.2) ∈ G ∧
      chartTripleVolume w < W := by
  intro w hw
  obtain ⟨h₁,h₂,h₃,hpq,hpz,hvol⟩ := hw
  refine ⟨h₁,h₂,h₃,?_,?_,hpz,hvol⟩
  · simpa only [dist_eq_norm,norm_sub_rev] using hsep _ _ hpq
  · simpa only [dist_eq_norm,norm_sub_rev] using hsep _ _ hpz

end Falconer

end OAI
