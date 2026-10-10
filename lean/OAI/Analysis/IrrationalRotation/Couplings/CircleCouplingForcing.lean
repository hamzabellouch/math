import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingSupport

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_endpoint_unit (j : ℕ) (i : ℕ) (side : Bool) :
    ∀ᵐ ω ∂law p j, endpoint side (ω i) ∈ Ico (0 : ℝ) 1 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => endpoint side z ∈ Ico (0 : ℝ) 1)
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (show MeasurableSet {z : CoordinateSample | endpoint side z ∈ Ico (0 : ℝ) 1} from by
        apply measurableSet_Ico.preimage
        cases side
        · exact measurable_fst.comp measurable_snd
        · exact measurable_snd.comp measurable_snd)).2
    cases side <;> exact CouplingMixture.intervalLaw_ae_mem 0 1
  · have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by exact_mod_cast
      (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
    rw [coordinateLaw, ite_eq_right hi]
    exact rawLaw_ae_endpoint_unit hm (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
      (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2 side

lemma ae_rounding_bound (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (i : ℕ) (side : Bool) :
    ∀ᵐ ω ∂law p j, |p.coordinate i (point p hr side ω) - endpoint side (ω i)| ≤
      1 / (MixedRadix.radices p.q i : ℝ) := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  filter_upwards [ae_endpoint_unit hp j i side, ae_nonterminal_digits hp j hr side] with ω hunit hnt
  have hraw : endpoint side (ω i) ∈ bin _ (digits p hr side ω i) :=
    (UniformQuantization.quantize_eq_iff _ hunit).mp rfl
  exact (abs_sub_lt_bin_width _ (coordinate_point_mem_bin hp hr side ω hnt i) hraw).le

lemma ae_top_raw_support (j : ℕ) {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, label i ω = topLabel which →
      1 - width (p.a s) (p.b s) which / 2 ≤ (ω i).2.2 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => z.1 = topLabel which → 1 - width (p.a s) (p.b s) which / 2 ≤ z.2.2)
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  rw [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  exact rawLaw_ae_top_support hm (hp.coupling_a_bounds s hs).1 (hp.coupling_a_bounds s hs).2
    (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2 which

lemma ae_bottom_raw_support (j : ℕ) {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, label i ω = bottomLabel which →
      (ω i).2.1 < width (p.a s) (p.b s) which / 2 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => z.1 = bottomLabel which → z.2.1 < width (p.a s) (p.b s) which / 2)
  have hi0 : i ≠ 0 := by have := (p.mem_block_iff s i).mp hi; omega
  rw [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi]
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  exact rawLaw_ae_bottom_support hm (hp.coupling_a_bounds s hs).1 (hp.coupling_a_bounds s hs).2
    (hp.coupling_b_bounds s hs).1 (hp.coupling_b_bounds s hs).2 which

lemma ae_top_forces (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ, label i ω = topLabel which →
      u ≤ 1 - width (p.a s) (p.b s) which → u ≤ p.coordinate i (point p hr true ω) := by
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact (hp.coupling_a_bounds s hs).1
    · exact (hp.coupling_b_bounds s hs).1
  filter_upwards [ae_top_raw_support hp j hs hi which, ae_rounding_bound hp j hr i true] with ω hsupp hround
  intro u hl hu
  exact top_forces_crossing (hsupp hl) hround (hp.coupling_bin_small hs hi hw) hu

lemma ae_bottom_forces (j : ℕ) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) (which : Bool) :
    ∀ᵐ ω ∂law p j, ∀ u : ℝ, label i ω = bottomLabel which →
      width (p.a s) (p.b s) which ≤ u → p.coordinate i (point p hr false ω) < u := by
  have hw : 1 / (p.m s : ℝ) ≤ width (p.a s) (p.b s) which := by
    cases which
    · exact (hp.coupling_a_bounds s hs).1
    · exact (hp.coupling_b_bounds s hs).1
  filter_upwards [ae_bottom_raw_support hp j hs hi which, ae_rounding_bound hp j hr i false] with ω hsupp hround
  intro u hl hu
  exact bottom_forces_crossing (hsupp hl) hround (hp.coupling_bin_small hs hi hw) hu

end Invariant233.CircleCoupling

end

end OAI
