import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A graph with all three coordinates explicitly specified. -/
def branchGraph (f g h : E3 → E3) : E3 → Triple := fun x => (f x, (g x, h x))

lemma measurable_branchGraph {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (branchGraph f g h) := hf.prodMk (hg.prodMk hh)

/-- The marginal used by the two-branch construction. -/
def branchMarginal (nu : Measure E3) (H1 H2 H3 H4 : E3 → E3) : Measure E3 :=
  (1 / 3 : ℝ≥0∞) • nu +
    (1 / 6 : ℝ≥0∞) • (Measure.map H1 nu + Measure.map H2 nu +
      Measure.map H3 nu + Measure.map H4 nu)

/-- Each branch is averaged over its three cyclic coordinate orderings. -/
def branchCoupling (nu : Measure E3) (H1 H2 H3 H4 : E3 → E3) : Measure Triple :=
  (1 / 6 : ℝ≥0∞) •
    (Measure.map (branchGraph id H1 H2) nu +
      Measure.map (branchGraph H1 H2 id) nu +
      Measure.map (branchGraph H2 id H1) nu +
      Measure.map (branchGraph id H3 H4) nu +
      Measure.map (branchGraph H3 H4 id) nu +
      Measure.map (branchGraph H4 id H3) nu)

lemma map_tripleFst_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleFst (Measure.map (branchGraph f g h) nu) = Measure.map f nu := by
  rw [Measure.map_map (show Measurable tripleFst from measurable_fst) (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleSnd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleSnd (Measure.map (branchGraph f g h) nu) = Measure.map g nu := by
  rw [Measure.map_map (show Measurable tripleSnd from measurable_fst.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleThd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleThd (Measure.map (branchGraph f g h) nu) = Measure.map h nu := by
  rw [Measure.map_map (show Measurable tripleThd from measurable_snd.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma six_smul_group (a b c d e : Measure E3) :
    (1 / 6 : ℝ≥0∞) • (a + b + c + a + d + e) =
      (1 / 3 : ℝ≥0∞) • a + (1 / 6 : ℝ≥0∞) • (b + c + d + e) := by
  have h : (1 / 3 : ℝ≥0∞) = 1 / 6 + 1 / 6 := by
    simp only [one_div]
    change ((3 : NNReal) : ℝ≥0∞)⁻¹ = ((6 : NNReal) : ℝ≥0∞)⁻¹ +
      ((6 : NNReal) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (6 : NNReal) ≠ 0), ← ENNReal.coe_add]
    norm_num
  rw [h, add_smul]
  simp only [smul_add]
  ac_rfl

lemma map_tripleFst_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleFst (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleFst := measurable_fst
  simp only [branchCoupling, Measure.map_smul _ hp.aemeasurable, Measure.map_add _ _ hp,
    map_tripleFst_branchGraph nu measurable_id h1 h2,
    map_tripleFst_branchGraph nu h1 h2 measurable_id,
    map_tripleFst_branchGraph nu h2 measurable_id h1,
    map_tripleFst_branchGraph nu measurable_id h3 h4,
    map_tripleFst_branchGraph nu h3 h4 measurable_id,
    map_tripleFst_branchGraph nu h4 measurable_id h3, Measure.map_id]
  exact six_smul_group _ _ _ _ _

lemma map_tripleSnd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleSnd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleSnd := measurable_fst.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul _ hp.aemeasurable, Measure.map_add _ _ hp,
    map_tripleSnd_branchGraph nu measurable_id h1 h2,
    map_tripleSnd_branchGraph nu h1 h2 measurable_id,
    map_tripleSnd_branchGraph nu h2 measurable_id h1,
    map_tripleSnd_branchGraph nu measurable_id h3 h4,
    map_tripleSnd_branchGraph nu h3 h4 measurable_id,
    map_tripleSnd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

lemma map_tripleThd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleThd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleThd := measurable_snd.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul _ hp.aemeasurable, Measure.map_add _ _ hp,
    map_tripleThd_branchGraph nu measurable_id h1 h2,
    map_tripleThd_branchGraph nu h1 h2 measurable_id,
    map_tripleThd_branchGraph nu h2 measurable_id h1,
    map_tripleThd_branchGraph nu measurable_id h3 h4,
    map_tripleThd_branchGraph nu h3 h4 measurable_id,
    map_tripleThd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

lemma isProbabilityMeasure_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchCoupling nu H1 H2 H3 H4) := by
  constructor
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply (measurable_branchGraph measurable_id h1 h2) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h1 h2 measurable_id) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h2 measurable_id h1) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph measurable_id h3 h4) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h3 h4 measurable_id) MeasurableSet.univ,
    Measure.map_apply (measurable_branchGraph h4 measurable_id h3) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, smul_eq_mul]
  norm_num only [one_div, show (1 + 1 + 1 + 1 + 1 + 1 : ℝ≥0∞) = 6 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The explicit two-branch mixture is an admissible coupling of its five-component marginal. -/
theorem isThreeCoupling_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    IsThreeCoupling (branchMarginal nu H1 H2 H3 H4) (branchCoupling nu H1 H2 H3 H4) :=
  ⟨isProbabilityMeasure_branchCoupling nu h1 h2 h3 h4,
    map_tripleFst_branchCoupling nu h1 h2 h3 h4,
    map_tripleSnd_branchCoupling nu h1 h2 h3 h4,
    map_tripleThd_branchCoupling nu h1 h2 h3 h4⟩

lemma isProbabilityMeasure_branchMarginal (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchMarginal nu H1 H2 H3 H4) := by
  have := isProbabilityMeasure_branchCoupling nu h1 h2 h3 h4
  rw [← map_tripleFst_branchCoupling nu h1 h2 h3 h4]
  infer_instance

/-- Any measurable cyclically invariant property holding on the two branches
also holds almost everywhere for their explicit coupling. -/
theorem ae_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) {P : Triple → Prop} (hP : MeasurableSet {t | P t})
    (hcycle : ∀ x y z, P (x, (y, z)) → P (y, (z, x)))
    (h12 : ∀ᵐ x ∂nu, P (x, (H1 x, H2 x)))
    (h34 : ∀ᵐ x ∂nu, P (x, (H3 x, H4 x))) :
    ∀ᵐ t ∂branchCoupling nu H1 H2 H3 H4, P t := by
  have h12r : ∀ᵐ x ∂nu, P (branchGraph H1 H2 id x) :=
    h12.mono fun x hx => hcycle _ _ _ hx
  have h12rr : ∀ᵐ x ∂nu, P (branchGraph H2 id H1 x) :=
    h12r.mono fun x hx => hcycle _ _ _ hx
  have h34r : ∀ᵐ x ∂nu, P (branchGraph H3 H4 id x) :=
    h34.mono fun x hx => hcycle _ _ _ hx
  have h34rr : ∀ᵐ x ∂nu, P (branchGraph H4 id H3 x) :=
    h34r.mono fun x hx => hcycle _ _ _ hx
  unfold branchCoupling
  apply Measure.ae_smul_measure
  simp only [ae_add_measure_iff,
    ae_map_iff (measurable_branchGraph measurable_id h1 h2).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h1 h2 measurable_id).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h2 measurable_id h1).aemeasurable hP,
    ae_map_iff (measurable_branchGraph measurable_id h3 h4).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h3 h4 measurable_id).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h4 measurable_id h3).aemeasurable hP]
  exact ⟨⟨⟨⟨⟨h12, h12r⟩, h12rr⟩, h34⟩, h34r⟩, h34rr⟩

end Problem356

end

end OAI
