import OAI.MeasureTheory.Falconer.Estimates.BadTripleRelation

namespace OAI

/-! # Original pair deletions in three-label slice incidence -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

def firstAnchoredPair (E : Set (Space n × Space n)) :
    Set (Space n × Space n × Space n) := {w | (w.1,w.2.1) ∈ E}

def secondAnchoredPair (E : Set (Space n × Space n)) :
    Set (Space n × Space n × Space n) := {w | (w.1,w.2.2) ∈ E}

lemma firstAnchoredPair_measurable {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    MeasurableSet (firstAnchoredPair E) := hE.preimage (by fun_prop)

lemma secondAnchoredPair_measurable {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    MeasurableSet (secondAnchoredPair E) := hE.preimage (by fun_prop)

lemma firstAnchoredPair_mass (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    (μ.prod (μ.prod μ)) (firstAnchoredPair E) = μ univ*(μ.prod μ) E := by
  rw [Measure.prod_apply (firstAnchoredPair_measurable hE)]
  have hs (x : Space n) : Prod.mk x ⁻¹' firstAnchoredPair E = (Prod.mk x ⁻¹' E) ×ˢ univ := by ext w; simp [firstAnchoredPair]
  simp_rw [hs,Measure.prod_prod,mul_comm _ (μ univ)]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _),← Measure.prod_apply hE]

lemma secondAnchoredPair_mass (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    (μ.prod (μ.prod μ)) (secondAnchoredPair E) = μ univ*(μ.prod μ) E := by
  rw [Measure.prod_apply (secondAnchoredPair_measurable hE)]
  have hs (x : Space n) : Prod.mk x ⁻¹' secondAnchoredPair E = univ ×ˢ (Prod.mk x ⁻¹' E) := by ext w; simp [secondAnchoredPair]
  simp_rw [hs,Measure.prod_prod]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _),← Measure.prod_apply hE]

def endpointExceptionalTriples (G : Set (Space n × Space n)) (W : ℝ) :
    Set (Space n × Space n × Space n) :=
  badChartTriples G W ∪ (firstAnchoredPair Gᶜ ∪ secondAnchoredPair Gᶜ)

lemma endpointExceptionalTriples_measurable {G : Set (Space n × Space n)}
    (hG : MeasurableSet G) (W : ℝ) : MeasurableSet (endpointExceptionalTriples G W) :=
  (badChartTriples_measurable hG W).union
    ((firstAnchoredPair_measurable hG.compl).union (secondAnchoredPair_measurable hG.compl))

lemma endpointExceptionalTriples_mass (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {G : Set (Space n × Space n)} (hG : MeasurableSet G) (W : ℝ) :
    (μ.prod (μ.prod μ)) (endpointExceptionalTriples G W) ≤
      (μ.prod (μ.prod μ)) (badChartTriples G W)+2*μ univ*(μ.prod μ) Gᶜ := by
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measure_union_le _ _).trans_eq
  rw [firstAnchoredPair_mass μ hG.compl,secondAnchoredPair_mass μ hG.compl]
  ring

lemma endpointExceptionalTriples_volume {G : Set (Space n × Space n)} {W : ℝ}
    {w : Space n × Space n × Space n} (hw : w ∉ endpointExceptionalTriples G W)
    (h₁ : ‖w.1‖ ≤ 1) (h₂ : ‖w.2.1‖ ≤ 1) (h₃ : ‖w.2.2‖ ≤ 1) :
    W ≤ chartTripleVolume w := by
  have hpq : (w.1,w.2.1) ∈ G := by
    by_contra hn
    exact hw (Or.inr (Or.inl hn))
  have hpz : (w.1,w.2.2) ∈ G := by
    by_contra hn
    exact hw (Or.inr (Or.inr hn))
  by_contra hv
  exact hw (Or.inl ⟨h₁,h₂,h₃,hpq,hpz,lt_of_not_ge hv⟩)

end Falconer

end OAI
