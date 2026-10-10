import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingSupport
import OAI.Analysis.IrrationalRotation.Couplings.MixedRadixHybridLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.UniformQuantization

lemma quantize_mono_on_unit {q : ℕ} [NeZero q] {x y : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) (hxy : x ≤ y) :
    quantize q x ≤ quantize q y := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hfx : ⌊(q : ℝ) * x⌋₊ < q :=
    (Nat.floor_lt (mul_nonneg hq.le hx.1)).mpr (by nlinarith [hx.2])
  have hfy : ⌊(q : ℝ) * y⌋₊ < q :=
    (Nat.floor_lt (mul_nonneg hq.le hy.1)).mpr (by nlinarith [hy.2])
  change ⌊(q : ℝ) * x⌋₊ % q ≤ ⌊(q : ℝ) * y⌋₊ % q
  rw [Nat.mod_eq_of_lt hfx, Nat.mod_eq_of_lt hfy]
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hxy hq.le)

lemma quantize_val_eq_floor {q : ℕ} [NeZero q] {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) : (quantize q x : ℕ) = ⌊(q : ℝ) * x⌋₊ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hf : ⌊(q : ℝ) * x⌋₊ < q :=
    (Nat.floor_lt (mul_nonneg hq.le hx.1)).mpr (by nlinarith [hx.2])
  exact Nat.mod_eq_of_lt hf

end Invariant233.UniformQuantization

namespace Invariant233.CircleDigitCoupling
open OneCoordinateCoupling

lemma rawLaw_ae_ordered {κ m a b t : ℝ} (hm : 1 ≤ m) :
    ∀ᵐ z ∂rawLaw κ m a b t, endpoint false z ≤ endpoint true z := by
  apply rawLaw_ae_of_components
  · exact measurableSet_le (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)
  · exact Eventually.of_forall (fun _ => le_rfl)
  · exact replacement_ae_ordered (by linarith : 2 ≤ 2 * m)

end Invariant233.CircleDigitCoupling

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coordinateLaw_ae_ordered (j i : ℕ) :
    ∀ᵐ z ∂coordinateLaw p j i, endpoint false z ≤ endpoint true z := by
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (measurableSet_le (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd))).2
    exact Eventually.of_forall (fun _ => le_rfl)
  · rw [coordinateLaw, ite_eq_right hi]
    apply rawLaw_ae_ordered
    have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    exact_mod_cast (show 1 ≤ p.m (p.blockIndex i) by
      have := hp.m_ge_200 _ hs
      omega)

lemma coordinateLaw_ae_endpoint_unit (j : ℕ) (side : Bool) (i : ℕ) :
    ∀ᵐ z ∂coordinateLaw p j i, endpoint side z ∈ Ico (0 : ℝ) 1 := by
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    have hmeas : Measurable (endpoint side) := by
      cases side
      · exact measurable_fst.comp measurable_snd
      · exact measurable_snd.comp measurable_snd
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (measurableSet_Ico.preimage hmeas)).2
    cases side <;> exact CouplingMixture.intervalLaw_ae_mem 0 1
  · rw [coordinateLaw, ite_eq_right hi]
    have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
      exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by
        have := hp.m_ge_200 _ hs
        omega)
    exact rawLaw_ae_endpoint_unit hm (hp.coupling_a_bounds _ hs).1
      (hp.coupling_a_bounds _ hs).2 (hp.coupling_b_bounds _ hs).1
      (hp.coupling_b_bounds _ hs).2 side

lemma ae_digits_ordered (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ i, digits p hr false ω i ≤ digits p hr true ω i := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply ae_all_iff.2
  intro i
  have h : ∀ᵐ z ∂coordinateLaw p j i,
      observedDigit p hr false i z ≤ observedDigit p hr true i z := by
    filter_upwards [coordinateLaw_ae_ordered hp j i,
      coordinateLaw_ae_endpoint_unit hp j false i,
      coordinateLaw_ae_endpoint_unit hp j true i] with z hz hx hy
    let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
    exact UniformQuantization.quantize_mono_on_unit hx hy hz
  exact (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae h

lemma ae_coordinates_ordered (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i) :
    ∀ᵐ ω ∂law p j, ∀ i,
      p.coordinate i (point p hr false ω) ≤ p.coordinate i (point p hr true ω) := by
  filter_upwards [ae_digits_ordered hp j hr, ae_nonterminal_digits hp j hr false,
    ae_nonterminal_digits hp j hr true] with ω horder hx hy
  intro i
  rw [coordinate_point_eq_tail hp hr false ω hx i,
    coordinate_point_eq_tail hp hr true ω hy i]
  exact MixedRadix.tailValue_mono hr horder i

lemma ae_raw_endpoints_unit (j : ℕ) (side : Bool) :
    ∀ᵐ ω ∂law p j, ∀ i, endpoint side (ω i) ∈ Ico (0 : ℝ) 1 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (coordinateLaw_ae_endpoint_unit hp j side i)

lemma ae_coordinate_raw_error (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, ∀ i,
      |p.coordinate i (point p hr side ω) - endpoint side (ω i)| ≤
        1 / (MixedRadix.radices p.q i : ℝ) := by
  filter_upwards [ae_nonterminal_digits hp j hr side,
    ae_raw_endpoints_unit hp j side] with ω hnt hu
  intro i
  rw [coordinate_point_eq_tail hp hr side ω hnt i]
  apply MixedRadix.abs_tailValue_sub_raw_le_of_floor hr _ i (hu i).1
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  exact (UniformQuantization.quantize_val_eq_floor (hu i)).symm

end Invariant233.CircleCoupling

end

end OAI
