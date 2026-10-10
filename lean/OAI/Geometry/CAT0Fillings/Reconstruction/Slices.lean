import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.IntegralBoundary

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction

def centeredSlopeSet {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) (K : ℝ≥0) (r : ℝ) : Set α :=
  {x | ∀ y, dist y x < r → dist (f y) (f x) ≤ (K : ℝ) * dist y x}

lemma isClosed_centeredSlopeSet {α β : Type*}
    [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) (K : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    IsClosed (centeredSlopeSet f K r) := by
  refine IsSeqClosed.isClosed fun z x hz hx => ?_
  have hdist : Tendsto (fun j => dist x (z j)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := x)).dist hx
  have hnear : ∀ᶠ j in atTop, dist x (z j) < r :=
    (tendsto_order.1 hdist).2 r hr
  have hfx : Tendsto (fun j => f (z j)) atTop (𝓝 (f x)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    have hlim : Tendsto (fun j => (K : ℝ) * dist x (z j)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hdist
    apply squeeze_zero' (Eventually.of_forall fun j => dist_nonneg) ?_ hlim
    filter_upwards [hnear] with j hj
    simpa only [dist_comm] using hz j x hj
  intro y hy
  have hd : Tendsto (fun j => dist y (z j)) atTop (𝓝 (dist y x)) :=
    tendsto_const_nhds.dist hx
  have hnear' : ∀ᶠ j in atTop, dist y (z j) < r :=
    (tendsto_order.1 hd).2 r hy
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hfx)
    (tendsto_const_nhds.mul hd)
  filter_upwards [hnear'] with j hj
  exact hz j y hj

abbrev PieceIndex := ℕ × {r : ℚ // 0 < r} × ℚ

def slopePiece (f : ℝ → ℝ) (i : PieceIndex) : Set ℝ :=
  centeredSlopeSet f (i.1 : ℝ≥0) (3 * (i.2.1.1 : ℝ)) ∩
    closedBall (i.2.2 : ℝ) (i.2.1.1 : ℝ)

lemma isCompact_slopePiece (f : ℝ → ℝ) (i : PieceIndex) :
    IsCompact (slopePiece f i) := by
  have hr : (0 : ℝ) < i.2.1.1 := by exact_mod_cast i.2.1.2
  exact (isCompact_closedBall _ _).inter_left
    (isClosed_centeredSlopeSet f _ (mul_pos (by norm_num) hr))

lemma lipschitzOnWith_slopePiece (f : ℝ → ℝ) (i : PieceIndex) :
    LipschitzOnWith (i.1 : ℝ≥0) f (slopePiece f i) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  apply hy.1 x
  have hr : (0 : ℝ) < i.2.1.1 := by exact_mod_cast i.2.1.2
  have hxy := dist_triangle x (i.2.2 : ℝ) y
  have hx' : dist x (i.2.2 : ℝ) ≤ (i.2.1.1 : ℝ) := hx.2
  have hy' : dist (i.2.2 : ℝ) y ≤ (i.2.1.1 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_comm] using hy.2
  linarith

lemma mem_iUnion_slopePiece_of_differentiableAt {f : ℝ → ℝ} {x : ℝ}
    (hx : DifferentiableAt ℝ f x) : x ∈ ⋃ i : PieceIndex, slopePiece f i := by
  obtain ⟨c, hc⟩ := hx.isBigO_sub.bound
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp hc
  obtain ⟨m, hm⟩ := exists_nat_ge c
  obtain ⟨r, hr0, hrδ⟩ := exists_rat_btwn (div_pos hδ (by norm_num : (0 : ℝ) < 3))
  have hr : (0 : ℚ) < r := by exact_mod_cast hr0
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (by linarith : x - (r : ℝ) < x + r)
  refine mem_iUnion.mpr ⟨⟨m, ⟨r, hr⟩, q⟩, ?_⟩
  constructor
  · intro y hy
    have hyδ : dist y x < δ := by
      change dist y x < 3 * (r : ℝ) at hy
      linarith
    have hh := hlocal hyδ
    have hh' : dist (f y) (f x) ≤ c * dist y x := by
      simpa only [dist_eq_norm] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right (by simpa using hm) dist_nonneg)
  · change dist x (q : ℝ) ≤ (r : ℝ)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith

lemma ae_mem_iUnion_slopePiece {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x : ℝ, x ∈ ⋃ i : PieceIndex, slopePiece f i := by
  filter_upwards [hf.ae_differentiableAt] with x hx
  exact mem_iUnion_slopePiece_of_differentiableAt hx

end CAT0Fillings.SliceReconstruction

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma restrictCurrent_sub_of_subset {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E F : Set X}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hFE : F ⊆ E) :
    restrictCurrent hT E - restrictCurrent hT F = restrictCurrent hT (E \ F) := by
  funext b π
  by_cases hab : Admissible b π
  · simp only [Pi.sub_apply, restrictCurrent_apply hT E hab,
      restrictCurrent_apply hT F hab, restrictCurrent_apply hT (E \ F) hab]
    rw [← borelAction_sub (currentMassMeasure hT) hT
      ((integrable_boundedLip _ hab.1).indicator hE)
      ((integrable_boundedLip _ hab.1).indicator hF) π hab.2]
    congr 1
    funext x
    by_cases hxF : x ∈ F
    · simp [hxF, hFE hxF]
    · by_cases hxE : x ∈ E <;> simp [hxF, hxE]
  · simp [restrictCurrent, hab]

lemma superlevelSlice_increment {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) {s t : ℝ} (hst : s ≤ t) :
    superlevelSlice hT hB u s - superlevelSlice hT hB u t =
      restrictCurrent hB {x | s < u x ∧ u x ≤ t} -
        boundarySucc (restrictCurrent hT {x | s < u x ∧ u x ≤ t}) := by
  have hE a : MeasurableSet {x | a < u x} :=
    measurableSet_lt measurable_const hu.measurable
  have hsub : {x | t < u x} ⊆ {x | s < u x} := fun x hx => lt_of_le_of_lt hst hx
  have he : {x | s < u x} \ {x | t < u x} = {x | s < u x ∧ u x ≤ t} := by
    ext x
    simp
  have hRT := restrictCurrent_sub_of_subset hT (hE s) (hE t) hsub
  have hRB := restrictCurrent_sub_of_subset hB (hE s) (hE t) hsub
  rw [he] at hRT hRB
  rw [← hRB, ← hRT, boundarySucc_sub]
  simp only [superlevelSlice]
  abel

lemma superlevelSlice_increment_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) {s t : ℝ} (hst : s ≤ t)
    (b : X → ℝ) (π : Fin k → X → ℝ)
    (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    |superlevelSlice hT hB u s b π - superlevelSlice hT hB u t b π| ≤
      (currentMassMeasure hB).real {x | s < u x ∧ u x ≤ t} +
      (currentMassMeasure hT).real {x | s < u x ∧ u x ≤ t} := by
  let E : Set X := {x | s < u x ∧ u x ≤ t}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const hu.measurable).inter
      (measurableSet_le hu.measurable measurable_const)
  have hbl : BoundedLip b := ⟨⟨1, hb⟩, 1, hb1⟩
  have hadm : Admissible b π := ⟨hbl, fun i => ⟨1, hπ i⟩⟩
  have hi := congrFun (congrFun (superlevelSlice_increment hT hB hu hst) b) π
  simp only [Pi.sub_apply] at hi
  rw [hi]
  change |restrictCurrent hB E b π - boundarySucc (restrictCurrent hT E) b π| ≤ _
  apply (abs_sub _ _).trans
  apply add_le_add
  · have hc := restrictCurrent_controls hB hE b π hbl hπ
    apply hc.trans
    have hl := integral_mono (integrable_boundedLip ((currentMassMeasure hB).restrict E) hbl).abs (integrable_const (1 : ℝ)) hb1
    simpa only [integral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply_univ] using hl
  · rw [boundarySucc, ite_eq_left hadm]
    have hp : ∀ i, LipschitzWith 1 ((Matrix.vecCons b π) i) := by
      intro i
      refine Fin.cases hb (fun j => hπ j) i
    have hc := restrictCurrent_controls hT hE (fun _ => 1) (Matrix.vecCons b π)
      (BoundedLip.const 1) hp
    simpa only [abs_one, integral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply_univ] using hc

noncomputable def sliceController {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (u : X → ℝ) (t : ℝ) : ℝ :=
  (currentMassMeasure hB).real {x | u x ≤ t} +
  (currentMassMeasure hT).real {x | u x ≤ t}

lemma monotone_sliceController {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (u : X → ℝ) : Monotone (sliceController hT hB u) := by
  intro s t hst
  exact add_le_add (measureReal_mono fun x hx => hx.trans hst)
    (measureReal_mono fun x hx => hx.trans hst)

lemma sliceController_sub {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) {s t : ℝ} (hst : s ≤ t) :
    sliceController hT hB u t - sliceController hT hB u s =
      (currentMassMeasure hB).real {x | s < u x ∧ u x ≤ t} +
      (currentMassMeasure hT).real {x | s < u x ∧ u x ≤ t} := by
  have he : {x | s < u x ∧ u x ≤ t} = {x | u x ≤ t} \ {x | u x ≤ s} := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff, not_le]
    exact and_comm
  have hsub : {x | u x ≤ s} ⊆ {x | u x ≤ t} := fun x hx => hx.trans hst
  have hmeas : MeasurableSet {x | u x ≤ s} :=
    measurableSet_le hu.measurable measurable_const
  rw [he, measureReal_sdiff hsub hmeas, measureReal_sdiff hsub hmeas]
  unfold sliceController
  ring

lemma superlevelSlice_controller_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (s t : ℝ)
    (b : X → ℝ) (π : Fin k → X → ℝ)
    (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    |superlevelSlice hT hB u s b π - superlevelSlice hT hB u t b π| ≤
      |sliceController hT hB u s - sliceController hT hB u t| := by
  rcases le_total s t with hst | hts
  · rw [abs_sub_comm (sliceController hT hB u s),
      abs_of_nonneg (sub_nonneg.mpr (monotone_sliceController hT hB u hst)),
      sliceController_sub hT hB hu hst]
    exact superlevelSlice_increment_bound hT hB hu hst b π hb hb1 hπ
  · rw [abs_sub_comm (superlevelSlice hT hB u s b π),
      abs_of_nonneg (sub_nonneg.mpr (monotone_sliceController hT hB u hts)),
      sliceController_sub hT hB hu hts]
    exact superlevelSlice_increment_bound hT hB hu hts b π hb hb1 hπ

end CAT0Fillings.Slicing

namespace CAT0Fillings.Slicing
open SliceReconstruction
open Set Filter MeasureTheory
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

theorem exists_compact_slice_lipschitz_pieces {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) :
    ∃ E : PieceIndex → Set ℝ,
      (∀ i, IsCompact (E i)) ∧ (∀ᵐ t : ℝ, t ∈ ⋃ i, E i) ∧
      ∀ i (b : X → ℝ) (π : Fin k → X → ℝ),
        LipschitzWith 1 b → (∀ x, |b x| ≤ 1) →
        (∀ j, LipschitzWith 1 (π j)) →
        LipschitzOnWith (i.1 : ℝ≥0) (fun t => superlevelSlice hT hB u t b π) (E i) := by
  refine ⟨slopePiece (sliceController hT hB u),
    isCompact_slopePiece _, ae_mem_iUnion_slopePiece (monotone_sliceController hT hB u), ?_⟩
  intro i b π hb hb1 hπ
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  have hc := superlevelSlice_controller_bound hT hB hu s t b π hb hb1 hπ
  have hp := (lipschitzOnWith_slopePiece (sliceController hT hB u) i).dist_le_mul s hs t ht
  exact hc.trans (by simpa only [Real.dist_eq] using hp)

end CAT0Fillings.Slicing
end

end OAI
