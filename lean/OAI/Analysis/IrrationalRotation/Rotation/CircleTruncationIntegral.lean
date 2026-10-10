import OAI.Analysis.IrrationalRotation.Model.CircleTruncationEvent
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingForcing
import OAI.Analysis.IrrationalRotation.Rotation.CanonicalCircleFiniteLower

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem ae_truncationEvent_exclusions (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    ∀ᵐ ω ∂law p j, ω ∈ truncationEvent p j hr r →
      ∀ s, j ≤ s → ∀ i ∈ p.block s,
        p.coordinate i (point p hr false ω) < 1 - 2 * (p.K j : ℝ) / p.N s ∧
        2 * (p.K j : ℝ) / p.N s < p.coordinate i (point p hr true ω) := by
  have hu (side : Bool) : ∀ᵐ ω ∂law p j, ∀ i,
      endpoint side (ω i) ∈ Ico (0 : ℝ) 1 :=
    ae_all_iff.mpr (fun i => ae_endpoint_unit hp j i side)
  filter_upwards [hu false, hu true, ae_nonterminal_digits hp j hr false,
    ae_nonterminal_digits hp j hr true] with ω hx hy hdx hdy
  intro hE
  have hfloor (side : Bool) (hunit : ∀ i, endpoint side (ω i) ∈ Ico (0 : ℝ) 1)
      (i : ℕ) :
      ⌊(MixedRadix.radices p.q i : ℝ) * endpoint side (ω i)⌋₊ =
        (digits p hr side ω i : ℕ) := by
    have hq : (0 : ℝ) < MixedRadix.radices p.q i := by exact_mod_cast hr i
    have hf : ⌊(MixedRadix.radices p.q i : ℝ) * endpoint side (ω i)⌋₊ <
        MixedRadix.radices p.q i :=
      (Nat.floor_lt (mul_nonneg hq.le (hunit i).1)).mpr (by nlinarith [(hunit i).2])
    change _ = _ % MixedRadix.radices p.q i
    rw [Nat.mod_eq_of_lt hf]
  exact hp.source_good_event_exclusions j hj (digits p hr false ω) (digits p hr true ω)
    hdx hdy (fun i => (ω i).2.1) (fun i => (ω i).2.2)
    (fun i => (hx i).1) (fun i => (hy i).1)
    (hfloor false hx) (hfloor true hy) hE.1 hE.2.2.1

theorem truncationEvent_integral_lower (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hFm : StronglyMeasurable (fun x => F x ProjectionCocycleWindow.basisZero))
    (hF : ∀ x, IsStarProjection (F x)) :
    p.ε j * (law p j).real (truncationEvent p j hr
      (fun x => ((F x ProjectionCocycleWindow.basisZero) 0).re)) ≤
      ∫ ω in truncationEvent p j hr
        (fun x => ((F x ProjectionCocycleWindow.basisZero) 0).re),
        ∑ n ∈ Finset.range (2 * p.K j + 1),
          ‖InvariantProjection.ConditionalConvolution.truncated (p.K j) n
            (fun v => (F (point p hr false ω) ProjectionCocycleWindow.basisZero) v /
              (p.floorCocycle θ v (point p hr false ω) : ℂ))
            (fun v => (p.floorCocycle θ (-v) (point p hr true ω) : ℂ) *
              conj (((1 - F (point p hr true ω)) ProjectionCocycleWindow.basisZero) (-v)))‖
        ∂law p j := by
  let := law_isProbabilityMeasure hp j
  let r : Circle → ℝ := fun x => ((F x ProjectionCocycleWindow.basisZero) 0).re
  have hrm : Measurable r :=
    Complex.continuous_re.measurable.comp
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable hFm).measurable)
  have htag : MeasurableSet (tagEvent p j) := by
    simp only [tagEvent, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : i ∈ p.block j
    · simpa only [hi, true_and] using
        (measurableSet_eq_fun (measurable_label i) (measurable_const (a := (some 4 : Label))))
    · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]
  have hEm : MeasurableSet (truncationEvent p j hr r) := by
    have hx (i : ℕ) : Measurable (fun ω : Sample => (ω i).2.1) :=
      measurable_fst.comp (measurable_snd.comp (measurable_pi_apply i))
    have hy (i : ℕ) : Measurable (fun ω : Sample => (ω i).2.2) :=
      measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))
    simp only [truncationEvent, Set.ofPred_and, Set.ofPred_forall]
    refine MeasurableSet.inter ?_ (htag.inter
      (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)))
    · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        (measurableSet_lt (hx i) measurable_const).inter
          (measurableSet_lt measurable_const (hy i))
    · exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
          (measurableSet_lt (hx i) measurable_const).inter
            (measurableSet_lt measurable_const (hy i))
    · exact measurableSet_le measurable_const (hrm.comp (measurable_point hp hr false))
    · exact measurableSet_le measurable_const
        (measurable_const.sub (hrm.comp (measurable_point hp hr true)))
  apply hp.canonical_projection_integral_lower (law p j) j hj
    (truncationEvent p j hr r) (point p hr false) (point p hr true)
    (measurable_point hp hr false) (measurable_point hp hr true)
    (fun ω => F (point p hr false ω)) (fun ω => F (point p hr true ω))
    (hFm.comp_measurable (measurable_point hp hr false))
    (hFm.comp_measurable (measurable_point hp hr true))
    (fun ω => hF _) (fun ω => hF _)
  filter_upwards [ae_restrict_mem hEm,
    ae_restrict_of_ae (ae_truncationEvent_exclusions hp j hj hr r)] with ω hω hexcl
  have hcuts := hexcl hω
  refine ⟨(fun s hs i hi => (hcuts s hs i hi).1),
    (fun s hs i hi => (hcuts s hs i hi).2), hω.2.2.2.1, ?_⟩
  have hdiag := hω.2.2.2.2
  change 1 / (j : ℝ) ≤ 1 - ((F (point p hr true ω) ProjectionCocycleWindow.basisZero) 0).re at hdiag
  linarith

end Invariant233.CircleCoupling

end

end OAI
