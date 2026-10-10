import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma cTransform_le_iff {v : M → ℝ} (hv : Continuous v) (x : M) (a : ℝ) :
    cTransform v x ≤ a ↔ ∀ y, -cost x y - v y ≤ a := by
  obtain ⟨y, hy, hmax⟩ := exists_cTransform_contact hv x
  constructor
  · intro h z
    exact (hmax z).trans h
  · intro h
    rw [hy]
    exact h y

lemma cTransform_antitone {v w : M → ℝ} (hv : Continuous v) (hw : Continuous w)
    (h : ∀ x, v x ≤ w x) : ∀ x, cTransform w x ≤ cTransform v x := by
  intro x
  rw [cTransform_le_iff hw]
  intro y
  have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
  linarith [h y]

lemma cTransform_cTransform_le {v : M → ℝ} (hv : Continuous v) (x : M) :
    cTransform (cTransform v) x ≤ v x := by
  rw [cTransform_le_iff (continuous_cTransform hv)]
  intro y
  have hh := cTransform_gap_nonneg hv y x
  rw [contactGap, cost_symm y x] at hh
  linarith

lemma cTransform_triple {v : M → ℝ} (hv : Continuous v) :
    cTransform (cTransform (cTransform v)) = cTransform v := by
  funext x
  exact le_antisymm (cTransform_cTransform_le (continuous_cTransform hv) x)
    (cTransform_antitone (continuous_cTransform (continuous_cTransform hv)) hv
      (cTransform_cTransform_le hv) x)

lemma cTransform_add_const {v : M → ℝ} (hv : Continuous v) (a : ℝ) :
    cTransform (fun x => v x + a) = fun x => cTransform v x - a := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff (v := fun x => v x + a) (hv.add continuous_const)]
    intro y
    have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
    linarith
  · obtain ⟨y, hy, _⟩ := exists_cTransform_contact hv x
    have hh := cTransform_gap_nonneg (v := fun x => v x + a) (hv.add continuous_const) x y
    dsimp [contactGap] at hh
    linarith

lemma cTransform_zero : cTransform (fun _ : M => (0 : ℝ)) = fun _ => 0 := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff continuous_const]
    intro y
    linarith [cost_nonneg x y]
  · have h := cTransform_gap_nonneg (v := fun _ : M => (0 : ℝ)) continuous_const x x
    simpa [contactGap, cost] using h

def boundedCTransform (v : M →ᵇ ℝ) : M →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨cTransform v, continuous_cTransform v.continuous⟩

lemma boundedCTransform_apply (v : M →ᵇ ℝ) (x : M) :
    boundedCTransform v x = cTransform v x := rfl

lemma boundedCTransform_nonexpansive : LipschitzWith 1 (boundedCTransform (M := M)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
  intro x
  rw [Real.dist_eq, abs_le]
  have hbound (a b : M →ᵇ ℝ) : cTransform a x - cTransform b x ≤ dist a b := by
    rw [sub_le_iff_le_add, cTransform_le_iff a.continuous]
    intro y
    have hg := cTransform_gap_nonneg b.continuous x y
    have hd := BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := b) y
    rw [Real.dist_eq, abs_le] at hd
    dsimp [contactGap] at hg
    linarith [hd.1]
  constructor
  · have hh := hbound w v
    rw [dist_comm w v] at hh
    change -dist v w ≤ cTransform v x - cTransform w x
    linarith
  · exact hbound v w

omit [Nonempty M] in

lemma isCompact_bounded_lipschitz (D : ℝ≥0) (H : ℝ) :
    IsCompact {f : M →ᵇ ℝ | LipschitzWith D f ∧ ∀ x, |f x| ≤ H} := by
  let A : Set (M →ᵇ ℝ) := {f | LipschitzWith D f ∧ ∀ x, |f x| ≤ H}
  have hclosed : IsClosed A := by
    apply IsClosed.inter
    · exact (isClosed_setOfPred_lipschitzWith (α := M) (β := ℝ) D).preimage
        (BoundedContinuousFunction.continuous_coe : Continuous (fun f : M →ᵇ ℝ => (f : M → ℝ)))
    · change IsClosed {f : M →ᵇ ℝ | ∀ x, |f x| ≤ H}
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro x
      exact isClosed_le ((continuous_apply x).comp BoundedContinuousFunction.continuous_coe).abs
        continuous_const
  apply BoundedContinuousFunction.arzela_ascoli₂ (Icc (-H) H) isCompact_Icc A hclosed
  · intro f x hf
    exact abs_le.mp (hf.2 x)
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro eps heps
    refine ⟨eps / ((D : ℝ) + 1), by positivity, ?_⟩
    intro y hy f
    have h := f.property.1.dist_le_mul y x
    have hstrict : (D : ℝ) * dist y x < eps := by
      have hy' := hy
      have hD : 0 ≤ (D : ℝ) := D.coe_nonneg
      have he := (lt_div_iff₀ (show 0 < (D : ℝ) + 1 by positivity)).mp hy'
      nlinarith [dist_nonneg (x := y) (y := x)]
    simpa only [dist_comm] using h.trans_lt hstrict

def normalizedDualPairs (x0 : M) : Set ((M →ᵇ ℝ) × (M →ᵇ ℝ)) :=
  {uv | uv.1 x0 = 0 ∧ boundedCTransform uv.2 = uv.1 ∧ boundedCTransform uv.1 = uv.2}

lemma isClosed_normalizedDualPairs (x0 : M) : IsClosed (normalizedDualPairs x0) := by
  apply IsClosed.inter
  · exact isClosed_eq (((continuous_apply x0).comp
      BoundedContinuousFunction.continuous_coe).comp continuous_fst) continuous_const
  · apply IsClosed.inter
    · exact isClosed_eq (boundedCTransform_nonexpansive.continuous.comp continuous_snd) continuous_fst
    · exact isClosed_eq (boundedCTransform_nonexpansive.continuous.comp continuous_fst) continuous_snd

lemma normalizedDualPairs_nonempty (x0 : M) : (normalizedDualPairs x0).Nonempty := by
  refine ⟨(0, 0), rfl, ?_, ?_⟩ <;>
    apply BoundedContinuousFunction.ext <;>
    intro x <;>
    exact congrFun cTransform_zero x

lemma normalizedDualPairs_bounds {D : ℝ≥0} (hD : ∀ x y : M, dist x y ≤ D)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ normalizedDualPairs x0) :
    (LipschitzWith D uv.1 ∧ ∀ x, |uv.1 x| ≤ (D : ℝ) ^ 2) ∧
      (LipschitzWith D uv.2 ∧ ∀ x, |uv.2 x| ≤ (D : ℝ) ^ 2) := by
  have hu : (uv.1 : M → ℝ) = cTransform uv.2 := congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.2.1.symm
  have hv : (uv.2 : M → ℝ) = cTransform uv.1 := congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.2.2.symm
  have hLu : LipschitzWith D uv.1 := by
    rw [hu]
    exact cTransform_lipschitz uv.2.continuous hD
  have hLv : LipschitzWith D uv.2 := by
    rw [hv]
    exact cTransform_lipschitz uv.1.continuous hD
  have hbu (x : M) : |uv.1 x| ≤ (D : ℝ) ^ 2 := by
    have hh := hLu.dist_le_mul x x0
    rw [h.1, Real.dist_eq, sub_zero] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (hD x x0) D.coe_nonneg])
  refine ⟨⟨hLu, hbu⟩, hLv, ?_⟩
  intro x
  rw [abs_le, hv]
  constructor
  · have hh := cTransform_gap_nonneg uv.1.continuous x x0
    rw [contactGap, h.1, cost] at hh
    have hdist := hD x x0
    have hd0 : 0 ≤ dist x x0 := dist_nonneg
    nlinarith [D.coe_nonneg, sq_nonneg ((D : ℝ) - dist x x0)]
  · rw [cTransform_le_iff uv.1.continuous]
    intro y
    have hb := (abs_le.mp (hbu y)).1
    linarith [cost_nonneg x y]

lemma isCompact_normalizedDualPairs (x0 : M) : IsCompact (normalizedDualPairs x0) := by
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M), Metric.diam_nonneg⟩
  have hD (x y : M) : dist x y ≤ D :=
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  refine ((isCompact_bounded_lipschitz D ((D : ℝ) ^ 2)).prod
    (isCompact_bounded_lipschitz D ((D : ℝ) ^ 2))).of_isClosed_subset
      (isClosed_normalizedDualPairs x0) ?_
  intro uv huv
  exact normalizedDualPairs_bounds hD huv

variable [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] in
lemma integral_boundedContinuous_lipschitz (mu : Measure M) [IsProbabilityMeasure mu] :
    LipschitzWith 1 (fun f : M →ᵇ ℝ => ∫ x, f x ∂mu) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have heq : (∫ x, f x ∂mu) - (∫ x, g x ∂mu) = ∫ x, (f - g) x ∂mu :=
    (integral_sub (f.integrable mu) (g.integrable mu)).symm
  rw [heq]
  exact (f - g).norm_integral_le_norm mu

def dualObjective (mu nu : Measure M) (uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)) : ℝ :=
  (∫ x, uv.1 x ∂mu) + ∫ y, uv.2 y ∂nu

omit [CompactSpace M] [Nonempty M] in
lemma continuous_dualObjective (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] : Continuous (dualObjective mu nu) :=
  ((integral_boundedContinuous_lipschitz mu).continuous.comp continuous_fst).add
    ((integral_boundedContinuous_lipschitz nu).continuous.comp continuous_snd)

lemma exists_minimizing_normalizedDualPair (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (x0 : M) :
    ∃ uv ∈ normalizedDualPairs x0, IsMinOn (dualObjective mu nu) (normalizedDualPairs x0) uv := by
  exact (isCompact_normalizedDualPairs x0).exists_isMinOn (normalizedDualPairs_nonempty x0)
    (continuous_dualObjective mu nu).continuousOn

def normalizeDualPair (x0 : M) (v : M →ᵇ ℝ) : (M →ᵇ ℝ) × (M →ᵇ ℝ) :=
  let a := boundedCTransform v
  (a + BoundedContinuousFunction.const M (-a x0),
    boundedCTransform a + BoundedContinuousFunction.const M (a x0))

omit [MeasurableSpace M] [BorelSpace M] in
lemma normalizeDualPair_mem (x0 : M) (v : M →ᵇ ℝ) :
    normalizeDualPair x0 v ∈ normalizedDualPairs x0 := by
  let a := boundedCTransform v
  change (a x0 + -a x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => cTransform a y + a x0) x = a x + -a x0
    rw [cTransform_add_const (continuous_cTransform a.continuous)]
    have hh := congrFun (cTransform_triple v.continuous) x
    change cTransform (cTransform a) x = a x at hh
    exact (congrArg (fun t : ℝ => t - a x0) hh).trans (by ring)
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => a y + -a x0) x = cTransform a x + a x0
    rw [cTransform_add_const a.continuous]
    ring

omit [CompactSpace M] [Nonempty M] in
lemma dualObjective_add_constants (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (a b : M →ᵇ ℝ) (k : ℝ) :
    dualObjective mu nu (a + BoundedContinuousFunction.const M (-k),
      b + BoundedContinuousFunction.const M k) = dualObjective mu nu (a,b) := by
  change (∫ x, (a x + -k) ∂mu) + (∫ y, (b y + k) ∂nu) = _
  rw [integral_add (a.integrable mu) (integrable_const _),
    integral_add (b.integrable nu) (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [dualObjective]
  ring

lemma dualObjective_normalize_le (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (x0 : M) (u v : M →ᵇ ℝ)
    (h : ∀ x y, 0 ≤ contactGap u v x y) :
    dualObjective mu nu (normalizeDualPair x0 v) ≤ dualObjective mu nu (u,v) := by
  rw [normalizeDualPair, dualObjective_add_constants]
  apply add_le_add
  · apply integral_mono (boundedCTransform v |>.integrable mu) (u.integrable mu)
    intro x
    rw [boundedCTransform_apply, cTransform_le_iff v.continuous]
    intro y
    have hh := h x y
    dsimp [contactGap] at hh
    linarith
  · apply integral_mono (boundedCTransform (boundedCTransform v) |>.integrable nu)
      (v.integrable nu)
    exact cTransform_cTransform_le v.continuous

end WeakMTWTransport
end

end OAI
