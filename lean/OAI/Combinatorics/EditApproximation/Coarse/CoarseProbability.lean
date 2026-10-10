import OAI.Combinatorics.EditApproximation.Coarse.CoarseAccuracy
import OAI.Combinatorics.EditApproximation.Coarse.CoarseSampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The actual finite coarse randomness

At each internal node, the child thresholds are independent uniform labels.
Recursive subtrees are independent of these labels. This complete probability
space also includes labels below pruned nodes.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u

instance coarseDrawsFintype (B D : ℕ) : Fintype (CoarseThresholdDraws B D) := by
  induction D with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ D ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)))

def coarseCanonicalDraws (B : ℕ) : (D : ℕ) → CoarseThresholdDraws B D
  | 0 => PUnit.unit
  | D + 1 => (id, fun _ => coarseCanonicalDraws B D)

instance coarseDrawsInhabited (B D : ℕ) : Inhabited (CoarseThresholdDraws B D) :=
  ⟨coarseCanonicalDraws B D⟩



instance coarseDrawsMeasurableSingletonClass (B D : ℕ)
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    MeasurableSingletonClass (CoarseThresholdDraws B D) := by
  induction D with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ D ih =>
    let := ih
    exact inferInstanceAs
      (MeasurableSingletonClass ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)))

/-- Literal recursive independent label law, with a deterministic leaf. -/


instance coarseDrawMeasure_isProbabilityMeasure (B D : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    IsProbabilityMeasure (coarseDrawMeasure B D) := by
  induction D with
  | zero =>
    change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit)
    exact Measure.dirac.isProbabilityMeasure
  | succ D ih =>
    let := ih
    change IsProbabilityMeasure
      ((Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).prod
        (Measure.pi fun _ : Fin B => coarseDrawMeasure B D))
    exact Measure.prod.instIsProbabilityMeasure _ _

/-- Symbolic number of internal nodes in a complete coarse tree. -/
def coarseInternalNodes (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | D + 1 => 1 + B * coarseInternalNodes B D

theorem coarseInternalNodes_eq_sum (B D : ℕ) :
    coarseInternalNodes B D = ∑ r ∈ range D, B ^ r := by
  induction D with
  | zero => simp [coarseInternalNodes]
  | succ D ih =>
    rw [coarseInternalNodes, ih, sum_range_succ']
    simp only [pow_zero, pow_succ', ← mul_sum]
    omega

/-- Actual source starts of all children of a literal list traversal. -/
def coarseChildListStart {B D : ℕ} {α : Type u}
    (children : List (CoarseSourceTree B α D)) (start : ℕ) (i : Fin children.length) : ℕ :=
  start + ((children.take i.val).map CoarseSourceTree.word).flatten.length

/-- The literal list recurrence equals its finite sum at the actual starts. -/
theorem coarseChildrenCost_eq_sum {B D : ℕ} {α : Type u}
    (k : ℕ) (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseChildrenCost k value children start shift =
      ∑ i : Fin children.length, univ.inf' univ_nonempty
        (fun next => value children[i.val] (coarseChildListStart children start i) next +
          2 * Nat.dist shift.val next.val) := by
  induction children generalizing start with
  | nil => simp [coarseChildrenCost]
  | cons child rest ih =>
    simp only [List.length_cons]
    rw [coarseChildrenCost, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, coarseChildListStart, List.take_zero,
      List.map_nil, List.flatten_nil, List.length_nil, add_zero, Fin.val_succ,
      List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.flatten_cons,
      List.length_append]
    rw [ih]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp only [coarseChildListStart, Nat.add_assoc]

/-- Integrating a uniform conditional failure bound over the ancestor
labels does not add a union over the possible allowance values. -/
theorem coarse_product_section_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (bad : Set (X × Y)) (hbad : MeasurableSet bad) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hsection : ∀ x, ν.real {y | (x, y) ∈ bad} ≤ failure) :
    (μ.prod ν).real bad ≤ failure := by
  have hENN (x : X) : ν {y | (x, y) ∈ bad} ≤ ENNReal.ofReal failure := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν {y | (x, y) ∈ bad})]
    exact ENNReal.ofReal_le_ofReal (hsection x)
  have hproduct : μ.prod ν bad ≤ ENNReal.ofReal failure := by
    rw [Measure.prod_apply hbad]
    apply (lintegral_mono (fun x => hENN x)).trans_eq
    simp
  exact ENNReal.toReal_le_of_le_ofReal hfailure hproduct

/-- The recursive child coordinates have precisely their own subtree law. -/
theorem coarse_child_projection_probability (B D : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (i : Fin B) (bad : Set (CoarseThresholdDraws B D)) :
    (Measure.pi fun _ : Fin B => coarseDrawMeasure B D).real {below | below i ∈ bad} =
      (coarseDrawMeasure B D).real bad := by
  have hbad : MeasurableSet bad := (Set.toFinite bad).measurableSet
  have hmap := (measurePreserving_eval (μ := fun _ : Fin B => coarseDrawMeasure B D) i).map_eq
  have hpreimage := Measure.map_apply (μ := Measure.pi fun _ : Fin B => coarseDrawMeasure B D)
    (measurable_pi_apply i) hbad
  rw [hmap] at hpreimage
  exact congrArg ENNReal.toReal hpreimage.symm

/-- Source starts attached to the full child metadata list. -/
def coarseDataListStart {B D : ℕ} {α : Type u}
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (start : ℕ) (i : Fin children.length) : ℕ :=
  start + ((children.take i.val).map (fun data => data.1.word)).flatten.length

theorem coarseDescendantEvents_iff {B D : ℕ} {α : Type u}
    (Q lam allowance : ℚ)
    (event : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D)) (start : ℕ) :
    CoarseDescendantEvents Q lam allowance event children start ↔
      ∀ i : Fin children.length, event children[i.val].1 children[i.val].2.2
        (lam * coarseChildThreshold B Q allowance children[i.val].2.1)
        (coarseDataListStart children start i) := by
  induction children generalizing start with
  | nil => simp [CoarseDescendantEvents]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [List.length_cons]
    rw [Fin.forall_fin_succ]
    simp only [CoarseDescendantEvents, Fin.val_zero, List.getElem_cons_zero,
      coarseDataListStart, List.take_zero, List.map_nil, List.flatten_nil, List.length_nil,
      add_zero, Fin.val_succ, List.getElem_cons_succ, List.take_succ_cons,
      List.map_cons, List.flatten_cons, List.length_append]
    rw [ih]
    simp only [coarseDataListStart, Nat.add_assoc]

theorem coarseTrueThresholdSum_eq_sum {B D : ℕ} {α : Type u}
    (k : ℕ) (Q allowance : ℚ) (transform : ℝ → ℝ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseTrueThresholdSum k Q trueValue allowance transform children start shift =
      ∑ i : Fin children.length,
        thresholdContribution (coarseChildThreshold B Q allowance children[i.val].2.1)
          (allowance / Q)
          (transform ((univ.inf' univ_nonempty (fun next =>
            trueValue children[i.val].1 (coarseDataListStart children start i) next +
              2 * Nat.dist shift.val next.val) : ℕ) : ℝ)) := by
  induction children generalizing start with
  | nil => simp [coarseTrueThresholdSum]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [List.length_cons]
    rw [coarseTrueThresholdSum, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, coarseDataListStart, List.take_zero,
      List.map_nil, List.flatten_nil, List.length_nil, add_zero, Fin.val_succ,
      List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.flatten_cons,
      List.length_append]
    rw [ih]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp only [coarseDataListStart, Nat.add_assoc]

def coarseNodeChildStart {B D : ℕ} {α : Type u}
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ) (i : Fin B) : ℕ :=
  start + (((List.ofFn children).take i.val).map CoarseSourceTree.word).flatten.length

def coarseNodeChildCost {B D : ℕ} {α : Type u}
    (k : ℕ) (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (shift : Fin (2 * k + 1)) (i : Fin B) : ℕ :=
  univ.inf' univ_nonempty (fun next => value (children i) (coarseNodeChildStart children start i) next +
    2 * Nat.dist shift.val next.val)

theorem coarseChildrenCost_ofFn {B D : ℕ} {α : Type u}
    (k : ℕ) (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseChildrenCost k value (List.ofFn children) start shift =
      ∑ i : Fin B, coarseNodeChildCost k value children start shift i := by
  rw [coarseChildrenCost_eq_sum]
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := children)))
  intro i
  simp only [List.getElem_ofFn, coarseChildListStart, coarseNodeChildCost, coarseNodeChildStart]
  rfl

theorem coarseDataListStart_ofFn {B D : ℕ} {α : Type u}
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D)
    (start : ℕ) (i : Fin B) :
    coarseDataListStart (List.ofFn fun i => (children i, draws i, below i)) start
        ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩ =
      coarseNodeChildStart children start i := by
  simp only [coarseDataListStart, coarseNodeChildStart, List.map_take, List.map_ofFn,
    Function.comp_def]

theorem coarseTrueThresholdSum_ofFn {B D : ℕ} {α : Type u}
    (k : ℕ) (Q allowance : ℚ) (transform : ℝ → ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseTrueThresholdSum k Q value allowance transform
        (List.ofFn fun i => (children i, draws i, below i)) start shift =
      ∑ i : Fin B, thresholdContribution (coarseChildThreshold B Q allowance (draws i))
        (allowance / Q) (transform (coarseNodeChildCost k value children start shift i)) := by
  rw [coarseTrueThresholdSum_eq_sum]
  apply Fintype.sum_equiv (finCongr (List.length_ofFn
    (f := fun i => (children i, draws i, below i))))
  intro i
  simp only [List.getElem_ofFn, coarseDataListStart, coarseNodeChildCost,
    coarseNodeChildStart, List.map_take, List.map_ofFn, Function.comp_def]
  rfl

theorem coarseChildThreshold_cast (B : ℕ) [NeZero B] (Q allowance : ℚ)
    (hQ : Q ≠ 0) (draw : Fin B) :
    (coarseChildThreshold B Q allowance draw : ℝ) =
      ((allowance : ℝ) / Q) * (draw.val + 1 : ℕ) / B := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne B
  simp only [coarseChildThreshold, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  field_simp

theorem coarseTrueThresholdSum_sample {B D : ℕ} [NeZero B] {α : Type u}
    (k : ℕ) (Q allowance : ℚ) (hQ : Q ≠ 0) (transform : ℝ → ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseTrueThresholdSum k Q value allowance transform
        (List.ofFn fun i => (children i, draws i, below i)) start shift =
      ∑ i : Fin B, coarseThresholdSample ((allowance : ℝ) / Q)
        (transform (coarseNodeChildCost k value children start shift i)) (draws i) := by
  rw [coarseTrueThresholdSum_ofFn]
  apply sum_congr rfl
  intro i hi
  rw [coarseChildThreshold_cast B Q allowance hQ]
  rfl

/-- A finite family of fixed child-cost lists shares the same independent
threshold labels. A union bound needs no independence between the lists. -/
theorem coarse_finite_threshold_simultaneous {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    {I : Type*} [Fintype I]
    (value : I → Fin B → ℝ) (scale allowance Q lam : ℝ)
    (hvalue : ∀ i j, 0 ≤ value i j) (hu : 0 < scale) (ha : 0 < allowance)
    (hQ : Q * scale = allowance) (hscale : scale ≤ allowance / 2)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | ¬ ∀ i, |(∑ j, coarseThresholdSample scale (value i j) (draws j)) -
          ∑ j, value i j| ≤ lam * (∑ j, value i j) + allowance} ≤
      Fintype.card I * (2 * Real.exp (-lam * Q / 12)) := by
  classical
  let μ := Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure
  let bad (i : I) : Set (Fin B → Fin B) :=
    {draws | lam * (∑ j, value i j) + allowance <
      |(∑ j, coarseThresholdSample scale (value i j) (draws j)) - ∑ j, value i j|}
  have hsubset : {draws | ¬ ∀ i, |(∑ j, coarseThresholdSample scale (value i j) (draws j)) -
      ∑ j, value i j| ≤ lam * (∑ j, value i j) + allowance} ⊆ ⋃ i, bad i := by
    intro draws hdraws
    obtain ⟨i, hi⟩ := not_forall.mp hdraws
    exact Set.mem_iUnion.mpr ⟨i, lt_of_not_ge hi⟩
  calc
    _ ≤ μ.real (⋃ i, bad i) := measureReal_mono hsubset
    _ ≤ ∑ i, μ.real (bad i) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _ : I, 2 * Real.exp (-lam * Q / 12) := by
      apply sum_le_sum
      intro i hi
      exact coarse_product_threshold_concentration (value i) scale allowance Q lam
        (hvalue i) hu ha hQ hscale hlam hlamone bernstein
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

/-- The two deterministic cost lists used at a node, simultaneously for
all shifts. The Boolean coordinate selects the lower or upper list. -/
noncomputable def coarseNodeSamplingValue {B D : ℕ} {α : Type u}
    (k : ℕ) (lam : ℚ) (f : ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (index : Fin (2 * k + 1) × Bool) (i : Fin B) : ℝ :=
  if index.2 then
    (coarseNodeChildCost k value children start index.1 i : ℝ) / (f * (1 + (lam : ℝ)))
  else f * coarseNodeChildCost k value children start index.1 i / (1 - (lam : ℝ))

noncomputable def CoarseNodeDeviationEvent {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (draws : Fin B → Fin B) : Prop :=
  ∀ index : Fin (2 * k + 1) × Bool,
    |(∑ i, coarseThresholdSample ((allowance : ℝ) / Q)
        (coarseNodeSamplingValue k lam f value children start index i) (draws i)) -
      ∑ i, coarseNodeSamplingValue k lam f value children start index i| ≤
      (lam : ℝ) * (∑ i, coarseNodeSamplingValue k lam f value children start index i) + allowance

/-- One complete node event costs four scalar Bernstein tails per shift. -/
theorem coarseNodeDeviationEvent_probability {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D) (start : ℕ)
    (hQ : 2 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (ha : 0 < allowance) (hf : 0 < f)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | ¬ CoarseNodeDeviationEvent k Q lam allowance f value children start draws} ≤
      4 * (2 * k + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12) := by
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have har : (0 : ℝ) < allowance := by exact_mod_cast ha
  have hlr : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlone : (lam : ℝ) < 1 := by exact_mod_cast hlamone
  have hvalue (index : Fin (2 * k + 1) × Bool) (i : Fin B) :
      0 ≤ coarseNodeSamplingValue k lam f value children start index i := by
    simp only [coarseNodeSamplingValue]
    split_ifs <;> positivity
  have hscale : (allowance : ℝ) / Q ≤ allowance / 2 := by
    apply div_le_div_of_nonneg_left har.le (by norm_num) hQr
  have hbound := coarse_finite_threshold_simultaneous
    (coarseNodeSamplingValue k lam f value children start)
    ((allowance : ℝ) / Q) allowance Q lam hvalue (div_pos har hQpos) har
    (by field_simp) hscale hlr hlone.le bernstein
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat] at hbound
  unfold CoarseNodeDeviationEvent
  apply hbound.trans_eq
  ring

/-- The deviation event is expressed using only the root labels, yet it
implies the literal true-cost inequalities for every subtree realization. -/
theorem coarseNodeDeviationEvent_bounds {B D : ℕ} [NeZero B] {α : Type u}
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ) (hQ : Q ≠ 0)
    (value : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D) (start : ℕ)
    (hevent : CoarseNodeDeviationEvent k Q lam allowance f value children start draws) :
    ∀ shift,
      (1 - (lam : ℝ)) *
          ((coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
            (f * (1 + (lam : ℝ)))) - allowance ≤
        coarseTrueThresholdSum k Q value allowance
          (fun cost => cost / (f * (1 + (lam : ℝ))))
          (List.ofFn fun i => (children i, draws i, below i)) start shift ∧
      coarseTrueThresholdSum k Q value allowance
          (fun cost => f * cost / (1 - (lam : ℝ)))
          (List.ofFn fun i => (children i, draws i, below i)) start shift ≤
        (1 + (lam : ℝ)) *
          (f * (coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
            (1 - (lam : ℝ))) + allowance := by
  intro shift
  have hlower := (abs_le.mp (hevent (shift, true))).1
  have hupper := (abs_le.mp (hevent (shift, false))).2
  simp only [coarseNodeSamplingValue, Bool.false_eq_true, ↓reduceIte] at hlower hupper
  have hlowerSum : (∑ i : Fin B,
      (coarseNodeChildCost k value children start shift i : ℝ) / (f * (1 + (lam : ℝ)))) =
      (coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
        (f * (1 + (lam : ℝ))) := by
    rw [← sum_div, coarseChildrenCost_ofFn, Nat.cast_sum]
  have hupperSum : (∑ i : Fin B,
      f * (coarseNodeChildCost k value children start shift i : ℝ) / (1 - (lam : ℝ))) =
      f * (coarseChildrenCost k value (List.ofFn children) start shift : ℝ) /
        (1 - (lam : ℝ)) := by
    rw [← sum_div, ← mul_sum, coarseChildrenCost_ofFn, Nat.cast_sum]
  rw [hlowerSum] at hlower
  rw [hupperSum] at hupper
  rw [coarseTrueThresholdSum_sample k Q allowance hQ,
    coarseTrueThresholdSum_sample k Q allowance hQ]
  constructor <;> linarith

/-- Root and actual descendant events suffice for the complete-tree
accuracy event; no approximate child value occurs in the root event. -/
theorem coarseAccuracyEvent_of_node {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam allowance : ℚ) (frame : List (Option α))
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D)
    (start : ℕ) (hQ : Q ≠ 0)
    (hchild : ∀ i, CoarseAccuracyEvent k Q lam frame (children i) (below i)
      (lam * coarseChildThreshold B Q allowance (draws i)) (coarseNodeChildStart children start i))
    (hnode : CoarseNodeDeviationEvent k Q lam allowance (coarseStructuralFactor lam D)
      (fun child => coarseShiftCost k frame child) children start draws) :
    CoarseAccuracyEvent k Q lam frame (.branch children) (draws, below) allowance start := by
  constructor
  · rw [coarseDescendantEvents_iff]
    intro i
    simpa only [List.getElem_ofFn, coarseDataListStart, coarseNodeChildStart,
      List.map_take, List.map_ofFn, Function.comp_def] using
      hchild ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
  · simpa only [List.map_ofFn, Function.comp_def] using
      coarseNodeDeviationEvent_bounds k Q lam allowance (coarseStructuralFactor lam D) hQ
        (fun child => coarseShiftCost k frame child) children draws below start hnode

/-- Simultaneous accuracy for the literal finite recursive estimator.
Every descendant is integrated conditional on its ancestor labels, with a
bound uniform in its resulting positive allowance. -/
theorem coarseAccuracyEvent_failure {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (allowance : ℚ) (start : ℕ)
    (hQ : 2 ≤ Q) (hlam : 0 < lam) (hlamone : lam < 1) (ha : 0 < allowance)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseDrawMeasure B D).real
      {draws | ¬ CoarseAccuracyEvent k Q lam frame tree draws allowance start} ≤
      (coarseInternalNodes B D : ℝ) *
        (4 * (2 * k + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)) := by
  classical
  have hQpos : 0 < Q := by linarith
  induction tree generalizing allowance start with
  | leaf letter => simp only [CoarseAccuracyEvent, not_true_eq_false, Set.ofPred_false,
      measureReal_empty, coarseInternalNodes, Nat.cast_zero, zero_mul, le_refl]
  | @branch D children ih =>
    let μ := Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure
    let ν := Measure.pi fun _ : Fin B => coarseDrawMeasure B D
    let oneFailure := 4 * (2 * k + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)
    let childFailure := (coarseInternalNodes B D : ℝ) * oneFailure
    let nodeBad : Set ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)) :=
      {data | ¬ CoarseNodeDeviationEvent k Q lam allowance (coarseStructuralFactor lam D)
        (fun child => coarseShiftCost k frame child) children start data.1}
    let childBad (i : Fin B) : Set ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)) :=
      {data | ¬ CoarseAccuracyEvent k Q lam frame (children i) (data.2 i)
        (lam * coarseChildThreshold B Q allowance (data.1 i)) (coarseNodeChildStart children start i)}
    have hsubset : {data : (Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D) |
        ¬ CoarseAccuracyEvent k Q lam frame (.branch children) data allowance start} ⊆
        nodeBad ∪ ⋃ i, childBad i := by
      intro data hdata
      by_cases hnode : data ∈ nodeBad
      · exact Or.inl hnode
      · right
        by_contra hchildren
        apply hdata
        obtain ⟨draws, below⟩ := data
        apply coarseAccuracyEvent_of_node k Q lam allowance frame children draws below start hQpos.ne'
        · intro i
          by_contra hi
          exact hchildren (Set.mem_iUnion.mpr ⟨i, hi⟩)
        · exact of_not_not hnode
    have hnodeProbability : (μ.prod ν).real nodeBad ≤ oneFailure := by
      have hnodeSet : nodeBad =
          {draws | ¬ CoarseNodeDeviationEvent k Q lam allowance (coarseStructuralFactor lam D)
            (fun child => coarseShiftCost k frame child) children start draws} ×ˢ Set.univ := by
        ext data
        simp only [nodeBad, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
      rw [hnodeSet, measureReal_prod_prod, probReal_univ, mul_one]
      exact coarseNodeDeviationEvent_probability k Q lam allowance (coarseStructuralFactor lam D)
        (fun child => coarseShiftCost k frame child) children start hQ hlam.le hlamone ha
        (lt_of_lt_of_le zero_lt_one (coarseStructuralFactor_one_le lam D hlam.le hlamone)) bernstein
    have hchildProbability (i : Fin B) : (μ.prod ν).real (childBad i) ≤ childFailure := by
      apply coarse_product_section_bound μ ν (childBad i) (Set.toFinite _).measurableSet
        childFailure (by dsimp [childFailure, oneFailure]; positivity)
      intro draws
      change ν.real {below | below i ∈ {childDraws |
        ¬ CoarseAccuracyEvent k Q lam frame (children i) childDraws
          (lam * coarseChildThreshold B Q allowance (draws i))
          (coarseNodeChildStart children start i)}} ≤ childFailure
      rw [coarse_child_projection_probability]
      exact ih i _ _ (mul_pos hlam (coarseChildThreshold_pos (draws i) hQpos ha))
    change (μ.prod ν).real _ ≤ _
    calc
      _ ≤ (μ.prod ν).real (nodeBad ∪ ⋃ i, childBad i) := measureReal_mono hsubset
      _ ≤ (μ.prod ν).real nodeBad + (μ.prod ν).real (⋃ i, childBad i) := measureReal_union_le _ _
      _ ≤ oneFailure + ∑ i, (μ.prod ν).real (childBad i) :=
        add_le_add hnodeProbability (measureReal_iUnion_fintype_le childBad)
      _ ≤ oneFailure + ∑ _ : Fin B, childFailure :=
        add_le_add_right (sum_le_sum (fun i _ => hchildProbability i)) _
      _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, coarseInternalNodes,
          Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        dsimp [childFailure, oneFailure]
        push_cast
        ring

end EditApproximation

end OAI
