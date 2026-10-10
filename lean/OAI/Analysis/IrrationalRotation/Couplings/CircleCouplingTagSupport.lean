import OAI.Analysis.IrrationalRotation.Couplings.CircleConditionalLabels

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma rawLaw_ae_tag_left {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = some 4 → z.2.1 < 1 / (2 * m) := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' false
    (P := fun l x => l = some 4 → x < 1 / (2 * m))
  · simp only [imp_iff_not_or, endpoint, Bool.false_eq_true, ite_false]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
  · exact Eventually.of_forall (by intro x h; cases h)
  · intro i
    by_cases hi : i = 4
    · subst i
      filter_upwards [intervalLaw_ae_mem 0 (1 / (2 * m))] with x hx
      exact fun _ => hx.2
    · exact Eventually.of_forall (fun _ h => (hi (Option.some.inj h)).elim)

lemma rawLaw_ae_tag_right {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = some 4 → 1 - 1 / (2 * m) ≤ z.2.2 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' true
    (P := fun l x => l = some 4 → 1 - 1 / (2 * m) ≤ x)
  · simp only [imp_iff_not_or, endpoint, ite_true]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_le measurable_const (measurable_snd.comp measurable_snd))
  · exact Eventually.of_forall (by intro x h; cases h)
  · intro i
    by_cases hi : i = 4
    · subst i
      filter_upwards [intervalLaw_ae_mem (1 - 1 / (2 * m)) 1] with x hx
      exact fun _ => hx.1
    · exact Eventually.of_forall (fun _ h => (hi (Option.some.inj h)).elim)

end Invariant233.CircleDigitCoupling

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_tag_raw_support (j : ℕ) {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    ∀ᵐ ω ∂law p j, label i ω = some 4 →
      (ω i).2.1 < 1 / (2 * (p.m s : ℝ)) ∧
        1 - 1 / (2 * (p.m s : ℝ)) ≤ (ω i).2.2 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => z.1 = some 4 → z.2.1 < 1 / (2 * (p.m s : ℝ)) ∧
      1 - 1 / (2 * (p.m s : ℝ)) ≤ z.2.2)
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  rw [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
  have hm : (100 : ℝ) ≤ p.m s := by
    exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  filter_upwards [rawLaw_ae_tag_left hm (hp.coupling_a_bounds s hs).1
    (hp.coupling_a_bounds s hs).2 (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2,
    rawLaw_ae_tag_right hm (hp.coupling_a_bounds s hs).1
    (hp.coupling_a_bounds s hs).2 (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2]
      with z hl hr
  exact fun h => ⟨hl h, hr h⟩

lemma ae_tag_coordinate_support (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    ∀ᵐ ω ∂law p j, label i ω = some 4 →
      p.coordinate i (point p hr false ω) < 1 / (p.m s : ℝ) ∧
        1 - 1 / (p.m s : ℝ) < p.coordinate i (point p hr true ω) := by
  have hsmall := hp.coupling_bin_small hs hi (le_refl (1 / (p.m s : ℝ)))
  have hhalf : (1 / (p.m s : ℝ)) / 2 = 1 / (2 * (p.m s : ℝ)) := by ring
  rw [hhalf] at hsmall
  have hsum : 1 / (2 * (p.m s : ℝ)) + 1 / (2 * (p.m s : ℝ)) =
      1 / (p.m s : ℝ) := by ring
  filter_upwards [ae_tag_raw_support hp j hs hi,
    ae_rounding_bound hp j hr i false, ae_rounding_bound hp j hr i true]
      with ω htag hx hy
  intro hl
  have hraw := htag hl
  have hx' := (abs_le.mp hx).2
  have hy' := (abs_le.mp hy).1
  simp only [endpoint, Bool.false_eq_true, ite_false, ite_true] at hx' hy'
  constructor <;> linarith [hraw.1, hraw.2]

lemma ae_all_tag_coordinate_support (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ s, 1 ≤ s → ∀ i ∈ p.block s, label i ω = some 4 →
      p.coordinate i (point p hr false ω) < 1 / (p.m s : ℝ) ∧
        1 - 1 / (p.m s : ℝ) < p.coordinate i (point p hr true ω) := by
  exact ae_all_iff.mpr (fun s => ae_all_iff.mpr (fun hs =>
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun hi =>
      ae_tag_coordinate_support hp j hr hs hi))))

end Invariant233.CircleCoupling

end

end OAI
