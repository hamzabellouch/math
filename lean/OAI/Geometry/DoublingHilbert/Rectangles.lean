import OAI.Geometry.DoublingHilbert.Integration

namespace OAI

/-! Rectangle probability measures, transport estimates, and finite averaging. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace DoublingHilbert

/-- Uniform probability on a nondegenerate real interval. -/
structure Segment where
  lo : ℝ
  hi : ℝ
  lt : lo < hi

namespace Segment

def length (I : Segment) : ℝ := I.hi - I.lo

theorem length_pos (I : Segment) : 0 < I.length := sub_pos.mpr I.lt

def law (I : Segment) : Measure ℝ :=
  (ENNReal.ofReal I.length)⁻¹ • volume.restrict (Ioc I.lo I.hi)

instance (I : Segment) : IsProbabilityMeasure I.law := by
  constructor
  simp only [law, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, length,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr I.length_pos)
    ENNReal.ofReal_ne_top

theorem ae_iff (I : Segment) {P : ℝ → Prop} :
    (∀ᵐ x ∂I.law, P x) ↔ ∀ᵐ x, x ∈ Ioc I.lo I.hi → P x := by
  rw [law, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top),
    ae_restrict_iff' measurableSet_Ioc]

theorem ae_mem (I : Segment) : ∀ᵐ x ∂I.law, x ∈ Ioo I.lo I.hi := by
  rw [I.ae_iff]
  filter_upwards [volume.ae_ne I.hi] with x hx hmem
  exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩

theorem ae_of_ae (I : Segment) {P : ℝ → Prop} (hP : ∀ᵐ x, P x) :
    ∀ᵐ x ∂I.law, P x := I.ae_iff.mpr (hP.mono fun _ hx _ => hx)

theorem integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Segment) (g : ℝ → E) :
    (∫ x, g x ∂I.law) = I.length⁻¹ • ∫ x in I.lo..I.hi, g x := by
  rw [law, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal I.length_pos.le,
    intervalIntegral.integral_of_le I.lt.le]

theorem integrable_iff {E : Type*} [NormedAddCommGroup E]
    (I : Segment) {g : ℝ → E} :
    Integrable g I.law ↔ IntervalIntegrable g volume I.lo I.hi := by
  rw [law, integrable_smul_measure
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr I.length_pos)),
    intervalIntegrable_iff_integrableOn_Ioc_of_le I.lt.le]
  rfl

end Segment

structure Rectangle where
  x : Segment
  y : Segment

namespace Rectangle

def law (Q : Rectangle) : Measure (ℝ × ℝ) := Q.x.law.prod Q.y.law

def closed (Q : Rectangle) : Set (ℝ × ℝ) :=
  Icc Q.x.lo Q.x.hi ×ˢ Icc Q.y.lo Q.y.hi

def interior (Q : Rectangle) : Set (ℝ × ℝ) :=
  Ioo Q.x.lo Q.x.hi ×ˢ Ioo Q.y.lo Q.y.hi

instance (Q : Rectangle) : IsProbabilityMeasure Q.law := by
  unfold law
  infer_instance

theorem ae_mem (Q : Rectangle) : ∀ᵐ p ∂Q.law, p ∈ Q.interior := by
  exact ((Measure.quasiMeasurePreserving_fst.ae Q.x.ae_mem).and
    (Measure.quasiMeasurePreserving_snd.ae Q.y.ae_mem))

theorem ae_of_ae (Q : Rectangle) {P : ℝ × ℝ → Prop} (hP : ∀ᵐ p, P p) :
    ∀ᵐ p ∂Q.law, P p := by
  rw [Measure.volume_eq_prod] at hP
  have hx : Q.x.law ≪ volume := Measure.absolutelyContinuous_restrict.smul_left _
  have hy : Q.y.law ≪ volume := Measure.absolutelyContinuous_restrict.smul_left _
  exact (hx.prod hy).ae_le hP

theorem integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : ℝ × ℝ → E) (hg : Integrable g Q.law) :
    (∫ p, g p ∂Q.law) = ∫ x, ∫ y, g (x, y) ∂Q.y.law ∂Q.x.law :=
  integral_prod g hg

theorem integral_eq_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : ℝ × ℝ → E) (hg : Integrable g Q.law) :
    (∫ p, g p ∂Q.law) = ∫ y, ∫ x, g (x, y) ∂Q.x.law ∂Q.y.law :=
  (integral_prod g hg).trans (integral_integral_swap hg)

end Rectangle

section BoundedFields
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

/-- Globally bounded strongly measurable fields; all derivative selections below have this property. -/
def IsBoundedField (g : X → E) : Prop :=
  StronglyMeasurable g ∧ ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M

namespace IsBoundedField

theorem integrable {g : X → E} (hg : IsBoundedField g) (μ : Measure X)
    [IsFiniteMeasure μ] : Integrable g μ := by
  obtain ⟨M, hM⟩ := hg.2
  exact Integrable.of_bound hg.1.aestronglyMeasurable M (Eventually.of_forall hM)

theorem norm_sq {g : X → E} (hg : IsBoundedField g) :
    IsBoundedField (fun x => ‖g x‖ ^ 2) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.norm.pow 2, M ^ 2, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM x) 2

theorem sub {f g : X → E} (hf : IsBoundedField f) (hg : IsBoundedField g) :
    IsBoundedField (fun x => f x - g x) := by
  obtain ⟨M, hM⟩ := hf.2
  obtain ⟨N, hN⟩ := hg.2
  exact ⟨hf.1.sub hg.1, M + N, fun x => (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))⟩

theorem const (e : E) : IsBoundedField (fun _ : X => e) :=
  ⟨stronglyMeasurable_const, ‖e‖, fun _ => le_rfl⟩

end IsBoundedField
end BoundedFields

end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

namespace Rectangle

theorem law_eq (Q : Rectangle) : Q.law =
    (ENNReal.ofReal (Q.x.length * Q.y.length))⁻¹ •
      volume.restrict (Ioc Q.x.lo Q.x.hi ×ˢ Ioc Q.y.lo Q.y.hi) := by
  simp only [law, Segment.law, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.prod_restrict, ← Measure.volume_eq_prod,
    ENNReal.ofReal_mul Q.x.length_pos.le]
  rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top), mul_comm]

end Rectangle

namespace IsBoundedField
variable {X Y I E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E]

theorem comp_measurable {g : X → E} (hg : IsBoundedField g) {f : Y → X}
    (hf : Measurable f) : IsBoundedField (g ∘ f) :=
  ⟨hg.1.comp_measurable hf, by obtain ⟨M, hM⟩ := hg.2; exact ⟨M, fun y => hM (f y)⟩⟩

theorem select [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {g : I → X → E} (hg : ∀ i, IsBoundedField (g i))
    {σ : X → I} (hσ : Measurable σ) : IsBoundedField (fun p => g (σ p) p) := by
  classical
  choose M hM using fun i => (hg i).2
  have heq : (fun p => g (σ p) p) =
      fun p => ∑ i : I, {p | σ p = i}.indicator (g i) p := by
    funext p
    simp [Set.indicator_apply, eq_comm]
  refine ⟨?_, ∑ i, |M i|, fun p => ?_⟩
  · rw [heq]
    convert (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
      (hg i).1.indicator (hσ (measurableSet_singleton i))) using 1
    funext p
    simp only [Finset.sum_apply]
    rfl
  · exact (hM (σ p) p).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) (Finset.mem_univ _)))

variable [NormedSpace ℝ E]

theorem integral_snd {g : X × Y → E} (hg : IsBoundedField g) (ν : Measure Y)
    [IsProbabilityMeasure ν] : IsBoundedField (fun x => ∫ y, g (x, y) ∂ν) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.integral_prod_right', M, fun x => ?_⟩
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun y => hM (x, y))

theorem integral_fst {g : X × Y → E} (hg : IsBoundedField g) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsBoundedField (fun y => ∫ x, g (x, y) ∂μ) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.integral_prod_left', M, fun y => ?_⟩
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall fun x => hM (x, y))

end IsBoundedField
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

section RectangleFTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem boundedField_column {f : Base → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : Base) : IsBoundedField (column f v) :=
  ⟨stronglyMeasurable_column f v, C * ‖v‖, norm_column_le hf v⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_integral_rectangle_le_x (Q : Rectangle) {G : Base → E}
    (hG : IsBoundedField G) {R : ℝ}
    (hline : ∀ᵐ y ∂Q.y.law, ‖∫ x, G (x, y) ∂Q.x.law‖ ≤ R) :
    ‖∫ p, G p ∂Q.law‖ ≤ R := by
  rw [Q.integral_eq_swap G (hG.integrable Q.law)]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hline

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_integral_rectangle_le_y (Q : Rectangle) {G : Base → E}
    (hG : IsBoundedField G) {R : ℝ}
    (hline : ∀ᵐ x ∂Q.x.law, ‖∫ y, G (x, y) ∂Q.y.law‖ ≤ R) :
    ‖∫ p, G p ∂Q.law‖ ≤ R := by
  rw [Q.integral_eq G (hG.integrable Q.law)]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hline

/-- Endpoint transport for a measurably selected horizontal sheet on each row. -/
theorem horizontal_mean_bound {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (Q : Rectangle)
    {F : Base → E} {G : ι → Base → E} {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) {R : ℝ}
    (hleft : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.lo, y) - F (Q.x.lo, y)‖ ≤ R)
    (hright : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.hi, y) - F (Q.x.hi, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.2)) (1, 0) p ∂Q.law) -
      (∫ p, column F (1, 0) p ∂Q.law)‖ ≤ 2 * R / Q.x.length := by
  have hB : IsBoundedField (fun p => column (G (σ p.2)) (1, 0) p) :=
    IsBoundedField.select (fun i => boundedField_column (hG i) (1, 0))
    (hσ.comp measurable_snd)
  have hBF := boundedField_column hF (1, 0)
  rw [← integral_sub (hB.integrable Q.law) (hBF.integrable Q.law)]
  apply norm_integral_rectangle_le_x Q (hB.sub hBF)
  have hlines : ∀ᵐ y, ∀ i, ∀ a b : ℝ,
      (∫ x in a..b, column (G i) (1, 0) (x, y)) = G i (b, y) - G i (a, y) :=
    ae_all_iff.mpr fun i => ae_integral_column_x (hG i)
  filter_upwards [Q.y.ae_of_ae hlines, Q.y.ae_of_ae (ae_integral_column_x hF), hleft, hright]
    with y hy hFy hly hry
  rw [Q.x.integral_eq, intervalIntegral.integral_sub
    (intervalIntegrable_column_x (hG (σ y)) (1, 0) y _ _)
    (intervalIntegrable_column_x hF (1, 0) y _ _), hy, hFy]
  have heq : G (σ y) (Q.x.hi, y) - G (σ y) (Q.x.lo, y) -
      (F (Q.x.hi, y) - F (Q.x.lo, y)) =
      (G (σ y) (Q.x.hi, y) - F (Q.x.hi, y)) -
      (G (σ y) (Q.x.lo, y) - F (Q.x.lo, y)) := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos Q.x.length_pos]
  have hh := (norm_sub_le (G (σ y) (Q.x.hi, y) - F (Q.x.hi, y))
    (G (σ y) (Q.x.lo, y) - F (Q.x.lo, y))).trans
      (add_le_add hry hly)
  calc
    _ ≤ Q.x.length⁻¹ * (R + R) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Q.x.length_pos.le)
    _ = _ := by ring

/-- Endpoint transport for a selected vertical sheet on each column. -/
theorem vertical_mean_bound {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (Q : Rectangle)
    {F : Base → E} {G : ι → Base → E} {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) {R : ℝ}
    (hbottom : ∀ᵐ x ∂Q.x.law, ‖G (σ x) (x, Q.y.lo) - F (x, Q.y.lo)‖ ≤ R)
    (htop : ∀ᵐ x ∂Q.x.law, ‖G (σ x) (x, Q.y.hi) - F (x, Q.y.hi)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.1)) (0, 1) p ∂Q.law) -
      (∫ p, column F (0, 1) p ∂Q.law)‖ ≤ 2 * R / Q.y.length := by
  have hB : IsBoundedField (fun p => column (G (σ p.1)) (0, 1) p) :=
    IsBoundedField.select (fun i => boundedField_column (hG i) (0, 1))
    (hσ.comp measurable_fst)
  have hBF := boundedField_column hF (0, 1)
  rw [← integral_sub (hB.integrable Q.law) (hBF.integrable Q.law)]
  apply norm_integral_rectangle_le_y Q (hB.sub hBF)
  have hlines : ∀ᵐ x, ∀ i, ∀ a b : ℝ,
      (∫ y in a..b, column (G i) (0, 1) (x, y)) = G i (x, b) - G i (x, a) :=
    ae_all_iff.mpr fun i => ae_integral_column_y (hG i)
  filter_upwards [Q.x.ae_of_ae hlines, Q.x.ae_of_ae (ae_integral_column_y hF), hbottom, htop]
    with x hx hFx hbx htx
  rw [Q.y.integral_eq, intervalIntegral.integral_sub
    (intervalIntegrable_column_y (hG (σ x)) (0, 1) x _ _)
    (intervalIntegrable_column_y hF (0, 1) x _ _), hx, hFx]
  have heq : G (σ x) (x, Q.y.hi) - G (σ x) (x, Q.y.lo) -
      (F (x, Q.y.hi) - F (x, Q.y.lo)) =
      (G (σ x) (x, Q.y.hi) - F (x, Q.y.hi)) -
      (G (σ x) (x, Q.y.lo) - F (x, Q.y.lo)) := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos Q.y.length_pos]
  have hh := (norm_sub_le (G (σ x) (x, Q.y.hi) - F (x, Q.y.hi))
    (G (σ x) (x, Q.y.lo) - F (x, Q.y.lo))).trans
      (add_le_add htx hbx)
  calc
    _ ≤ Q.y.length⁻¹ * (R + R) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Q.y.length_pos.le)
    _ = _ := by ring

end RectangleFTC
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace Rectangle

def area (Q : Rectangle) : ℝ := Q.x.length * Q.y.length

theorem area_pos (Q : Rectangle) : 0 < Q.area := mul_pos Q.x.length_pos Q.y.length_pos

theorem law_eq_closed (Q : Rectangle) : Q.law =
    (ENNReal.ofReal Q.area)⁻¹ • volume.restrict Q.closed := by
  simp only [law, Segment.law, restrict_Ioc_eq_restrict_Icc,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict,
    ← Measure.volume_eq_prod, area, closed, ENNReal.ofReal_mul Q.x.length_pos.le]
  rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top), mul_comm]

theorem volume_closed (Q : Rectangle) : volume Q.closed = ENNReal.ofReal Q.area := by
  rw [closed, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  exact (ENNReal.ofReal_mul Q.x.length_pos.le).symm

theorem integral_eq_average_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : Base → E) :
    (∫ p, g p ∂Q.law) = ⨍ p in Q.closed, g p := by
  rw [setAverage_eq', law_eq_closed, volume_closed]

theorem integral_eq_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : Base → E) :
    (∫ p, g p ∂Q.law) = Q.area⁻¹ • ∫ p in Q.closed, g p := by
  rw [law_eq_closed, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal Q.area_pos.le]

theorem area_mul_integral (Q : Rectangle) (g : Base → ℝ) :
    Q.area * (∫ p, g p ∂Q.law) = ∫ p in Q.closed, g p := by
  rw [Q.integral_eq_closed, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ Q.area_pos.ne', one_mul]

/-- Trimming at most half of each side increases a nonnegative mean by at most four. -/
theorem integral_le_four_of_subset (P Q : Rectangle) {g : Base → ℝ}
    (hg : IsBoundedField g) (hpos : ∀ p, 0 ≤ g p)
    (hsub : Q.closed ⊆ P.closed)
    (hx : P.x.length / 2 ≤ Q.x.length) (hy : P.y.length / 2 ≤ Q.y.length) :
    (∫ p, g p ∂Q.law) ≤ 4 * (∫ p, g p ∂P.law) := by
  have : IsFiniteMeasure (volume.restrict P.closed) :=
    isFiniteMeasure_restrict.mpr (by rw [P.volume_closed]; exact ENNReal.ofReal_ne_top)
  have hi := setIntegral_mono_set (s := Q.closed) (t := P.closed) (hg.integrable (volume.restrict P.closed))
    (Eventually.of_forall hpos) (Eventually.of_forall hsub)
  rw [← Q.area_mul_integral g, ← P.area_mul_integral g] at hi
  have ha : P.area ≤ 4 * Q.area := by
    have := mul_le_mul hx hy (div_nonneg P.y.length_pos.le (by norm_num)) Q.x.length_pos.le
    dsimp [area]
    nlinarith
  have hpmean : 0 ≤ (∫ p, g p ∂P.law) := integral_nonneg hpos
  have hmul := mul_le_mul_of_nonneg_right ha hpmean
  nlinarith [Q.area_pos]

def square (p : Base) (r : ℝ) (hr : 0 < r) : Rectangle :=
  ⟨⟨p.1 - r, p.1 + r, by linarith⟩, ⟨p.2 - r, p.2 + r, by linarith⟩⟩

theorem square_closed (p : Base) (r : ℝ) (hr : 0 < r) :
    (square p r hr).closed = Metric.closedBall p r := by
  rw [← Prod.eta p, ← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]
  rfl

end Rectangle

section LocalSquare
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- Actual Lebesgue-good derivative points supply arbitrarily accurate base squares. -/
theorem goodSheetPoint_exists_rectangle {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) {w : Tuple} {p : Base} (hp : goodSheetPoint f w p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Rectangle, Q.closed ⊆ sheetDomain w ∧
      (∫ q, ‖column (globalSheet hf w) (1, 0) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2 ∂Q.law) < ε ∧
      (∫ q, ‖column (globalSheet hf w) (0, 1) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2 ∂Q.law) < ε := by
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0, Metric.closedBall p r ⊆ sheetDomain w :=
    (eventually_closedBall_subset ((isOpen_sheetDomain w).mem_nhds hp.1)).filter_mono
      nhdsWithin_le_nhds
  have hx := hp.2.2.1.eventually (gt_mem_nhds hε)
  have hy := hp.2.2.2.eventually (gt_mem_nhds hε)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hsub, hrx, hry⟩ := (hpos.and (he.and (hx.and hy))).exists
  refine ⟨Rectangle.square p r hr, ?_, ?_, ?_⟩
  · rwa [Rectangle.square_closed]
  · rw [Rectangle.integral_eq_average_closed, Rectangle.square_closed]
    refine lt_of_eq_of_lt ?_ hrx
    apply setAverage_congr_fun measurableSet_closedBall
    exact Eventually.of_forall fun q hq => by rw [column_globalSheet hf w (hsub hq)]
  · rw [Rectangle.integral_eq_average_closed, Rectangle.square_closed]
    refine lt_of_eq_of_lt ?_ hry
    apply setAverage_congr_fun measurableSet_closedBall
    exact Eventually.of_forall fun q hq => by rw [column_globalSheet hf w (hsub hq)]

end LocalSquare
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace Segment

def grid (a h : ℝ) (n : ℕ) (hh : 0 < h) (hn : 0 < n) : Segment :=
  ⟨a, a + n * h, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact lt_add_of_pos_right a (mul_pos hn' hh)⟩

def cell (a h : ℝ) (hh : 0 < h) (i : ℕ) : Segment :=
  ⟨a + i * h, a + (↑(i + 1) : ℝ) * h, by push_cast; nlinarith⟩

@[simp] theorem grid_length (a h : ℝ) (n : ℕ) (hh : 0 < h) (hn : 0 < n) :
    (grid a h n hh hn).length = n * h := by simp [grid, length]

@[simp] theorem cell_length (a h : ℝ) (hh : 0 < h) (i : ℕ) :
    (cell a h hh i).length = h := by simp [cell, length]; ring

/-- Exact finite averaging over adjacent equal cells. -/
theorem integral_grid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) {g : ℝ → E}
    (hg : IsBoundedField g) :
    (∫ x, g x ∂(grid a h n hh hn).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ x, g x ∂(cell a h hh i).law := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => a + i * h) (n := n) (f := g) (μ := volume)
    (fun i _ => (cell a h hh i).integrable_iff.mp (hg.integrable _))
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  rw [← Fin.sum_univ_eq_sum_range] at hsum
  simp_rw [integral_eq, grid_length, cell_length]
  rw [← Finset.smul_sum, smul_smul]
  have hs : (n : ℝ)⁻¹ * h⁻¹ = ((n : ℝ) * h)⁻¹ := by ring
  rw [hs]
  congr 1
  exact hsum.symm

end Segment

namespace Rectangle

/-- Exact integration by columns. -/
theorem integral_grid_x {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) (J : Segment) {g : ℝ × ℝ → E}
    (hg : IsBoundedField g) :
    (∫ p, g p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ p, g p ∂(Rectangle.mk (Segment.cell a h hh i) J).law := by
  rw [(Rectangle.mk (Segment.grid a h n hh hn) J).integral_eq g
    (hg.integrable _), Segment.integral_grid a h hh hn (hg.integral_snd J.law)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact ((Rectangle.mk (Segment.cell a h hh i) J).integral_eq g
    (hg.integrable _)).symm

/-- Exact integration by rows. -/
theorem integral_grid_y {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) (I : Segment) {g : ℝ × ℝ → E}
    (hg : IsBoundedField g) :
    (∫ p, g p ∂(Rectangle.mk I (Segment.grid a h n hh hn)).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh i)).law := by
  rw [(Rectangle.mk I (Segment.grid a h n hh hn)).integral_eq_swap g
    (hg.integrable _), Segment.integral_grid a h hh hn (hg.integral_fst I.law)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact ((Rectangle.mk I (Segment.cell a h hh i)).integral_eq_swap g
    (hg.integrable _)).symm

end Rectangle
end
end DoublingHilbert

end

end OAI
