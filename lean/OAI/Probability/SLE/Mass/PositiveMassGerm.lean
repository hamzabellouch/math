import OAI.Probability.SLE.Stochastic.BrownianGerm
import OAI.Probability.SLE.Mass.CanonicalMassConstruction

namespace OAI

/-! A uniform positive chance of early mass, together with the Brownian
germ law, gives mass before every positive time. The scaling estimate
needed to apply this lemma is kept explicit. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

lemma earlyMassGerm_tail {Ω : Type*} (E : ℕ → Set Ω) (k : ℕ) :
    (⋂ N : ℕ, ⋃ j ≥ N, E j) = (⋂ N : ℕ, ⋃ j ≥ max N k, E j) := by
  ext ω
  simp only [mem_iInter,mem_iUnion]
  constructor
  · intro h N
    exact h (max N k)
  · intro h N
    obtain ⟨j,hj,hE⟩ := h N
    exact ⟨j,(le_max_left N k).trans hj,hE⟩

/-- This is the zero-one step of the canonical mass positivity argument.
The lower bound will come from scaling a single nonzero compact mean. -/
theorem positive_mass_all_times_of_uniform_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (Z : ℝ≥0 → Ω → ℝ≥0∞)
    (hZ : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) Z)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t => Z t ω))
    (ε : ℕ → ℝ≥0) (hεanti : Antitone ε) (hε : Tendsto ε atTop (𝓝 0))
    (p : ℝ≥0∞) (hp : 0<p) (hprob : ∀ n, p ≤ P {ω | 0<Z (ε n) ω}) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0<t → 0<Z t ω := by
  let E : ℕ → Set Ω := fun n => {ω | 0<Z (ε n) ω}
  let A : ℕ → Set Ω := fun N => ⋃ j ≥ N, E j
  let G : Set Ω := ⋂ N, A N
  have hEp (j k : ℕ) (hkj : k≤j) :
      MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (ε k)] (E j) := by
    have hz : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (ε k)]
        (Z (ε j)) := (hZ (ε j)).mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono (hεanti hkj)) le_rfl
    exact measurableSet_lt measurable_const hz
  have hGp (k : ℕ) : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (ε k)] G := by
    change MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (ε k)]
      (⋂ N : ℕ, ⋃ j ≥ N, E j)
    rw [earlyMassGerm_tail E k]
    apply MeasurableSet.iInter
    intro N
    apply MeasurableSet.iUnion
    intro j
    apply MeasurableSet.iUnion
    intro hj
    exact hEp j k ((le_max_right N k).trans hj)
  have hEm (j : ℕ) : MeasurableSet (E j) :=
    (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le _ _ (hEp j j le_rfl)
  have hAm (N : ℕ) : MeasurableSet (A N) :=
    MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => hEm j))
  have hGm : MeasurableSet G := MeasurableSet.iInter hAm
  have hAa : Antitone A := by
    intro N M hNM ω hω
    obtain ⟨j,hj⟩ := mem_iUnion.mp hω
    obtain ⟨hjM,hωE⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hNM.trans hjM,hωE⟩⟩
  have hpG : p≤P G := by
    change p≤P (⋂ N, A N)
    rw [hAa.measure_iInter (fun N => (hAm N).nullMeasurableSet) ⟨0,measure_ne_top P _⟩]
    apply le_iInf
    intro N
    apply (hprob N).trans (measure_mono ?_)
    intro ω hω
    exact mem_iUnion.mpr ⟨N,mem_iUnion.mpr ⟨le_rfl,hω⟩⟩
  have hGone : P G=1 := by
    rcases brownian_germ_zero_one hB hm hc h0 ε hε G hGp with hG | hG
    · exact ((ne_of_gt hp) (le_zero_iff.mp (hpG.trans hG.le))).elim
    · exact hG
  have hGa : ∀ᵐ ω ∂P, ω∈G := (mem_ae_iff_prob_eq_one hGm).mpr hGone
  filter_upwards [hGa,hmono] with ω hω hωmono
  intro t ht
  obtain ⟨N,hN⟩ := (hε.eventually (eventually_lt_nhds ht)).exists
  have hg : ∀ N : ℕ, ∃ j, N≤j ∧ ω∈E j := by
    intro N
    change ω∈⋂ N, ⋃ j ≥ N, E j at hω
    obtain ⟨j,hj⟩ := mem_iUnion.mp (mem_iInter.mp hω N)
    obtain ⟨hNj,hmem⟩ := mem_iUnion.mp hj
    exact ⟨j,hNj,hmem⟩
  obtain ⟨j,hj,hωj⟩ := hg N
  exact lt_of_lt_of_le hωj (hωmono ((hεanti hj).trans hN.le))

end SLEExactGauge

end

end OAI
