import OAI.Probability.InvariantIsing.Fields.FieldFiniteDomain

namespace OAI

/-! The rough field cap estimate used in the finite-dimensional upper comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

/-- The finite constant coming from the positive exponents of a fixed trial partition. -/
def fieldPartitionConstant (h : FieldStep) : ℝ :=
  ∑ i : Fin h.depth, Real.log 2 / (fieldIncrement h i.succ).1

def gaussianAbsoluteMean : ℝ := ∫ z : ℝ, |z| ∂gaussianReal 0 1

lemma gaussianAbsoluteMean_nonneg : 0 ≤ gaussianAbsoluteMean :=
  integral_nonneg (fun _ => abs_nonneg _)

lemma gaussianOperator_fold_abs (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2) (z : ℝ) :
    (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
      (fun x => Real.log (Real.cosh x))) z ≤ |z| +
        (L.map (fun av => av.1 * av.2 / 2 + Real.log 2 / av.1)).sum := by
  induction L generalizing z with
  | nil =>
    simpa using (le_abs_self (Real.log (Real.cosh z))).trans
      (IsingPerceptron.abs_log_cosh_le z)
  | cons av L ih =>
    have htail : ∀ bv ∈ L, 0 < bv.1 ∧ 0 ≤ bv.2 :=
      fun bv hb => hL bv (List.mem_cons_of_mem _ hb)
    have hav := hL av (List.mem_cons_self)
    have hT := gaussianOperator_fold_growth L (fun bv hb => (htail bv hb).1)
      IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
    let c := (L.map (fun bv => bv.1 * bv.2 / 2 + Real.log 2 / bv.1)).sum
    have hm : gaussianOperator av.1 av.2
        (L.foldr (fun bv f => gaussianOperator bv.1 bv.2 f)
          (fun x => Real.log (Real.cosh x))) z ≤
        gaussianOperator av.1 av.2 (fun x => c + |x|) z := by
      apply gaussianOperator_mono hT.1 (measurable_const.add measurable_id.abs)
        hT.2 (linearGrowth_const_add IsingPerceptron.abs_linearGrowth c) _ hav.1.le
      intro x
      simpa only [c, Pi.add_apply, id_eq, add_comm] using ih htail x
    rw [gaussianOperator_const_add (F := fun x : ℝ => |x|) measurable_id.abs IsingPerceptron.abs_linearGrowth] at hm
    have hc : gaussianOperator av.1 av.2 (fun x : ℝ => |x|) z ≤
        |z| + av.1 * av.2 / 2 + Real.log 2 / av.1 := by
      rw [gaussianOperator_eq_transform]
      exact IsingPerceptron.gaussianTransform_abs_bound hav.2 hav.1 z
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    dsimp only [c] at hm
    linarith

lemma gaussianOperator_zero_abs (v : ℝ) :
    gaussianOperator 0 v (fun x : ℝ => |x|) 0 = Real.sqrt v * gaussianAbsoluteMean := by
  simp only [gaussianOperator, ite_true, zero_add, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg v), integral_const_mul, gaussianAbsoluteMean]

lemma fieldValue_abs_sum (h : FieldStep) :
    fieldValue h 0 ≤ Real.sqrt (h.height 0) * gaussianAbsoluteMean +
      (∑ i : Fin h.depth,
        ((fieldIncrement h i.succ).1 * (fieldIncrement h i.succ).2 / 2 +
          Real.log 2 / (fieldIncrement h i.succ).1)) - h.height (Fin.last h.depth) / 2 := by
  let L := List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)
  have hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2 := by
    intro av hav
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
    exact ⟨fieldIncrement_tail_positive h i, fieldIncrement_nonneg h i.succ⟩
  have hT := gaussianOperator_fold_growth L (fun av hav => (hL av hav).1)
    IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
  let c := (L.map (fun av => av.1 * av.2 / 2 + Real.log 2 / av.1)).sum
  have hm := gaussianOperator_mono hT.1 (measurable_const.add measurable_id.abs)
    hT.2 (linearGrowth_const_add IsingPerceptron.abs_linearGrowth c)
    (fun x => by simpa only [c, Pi.add_apply, id_eq, add_comm] using gaussianOperator_fold_abs L hL x)
    (show 0 ≤ (0 : ℝ) from le_rfl) (h.height 0) 0
  change gaussianOperator 0 (h.height 0)
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun x => Real.log (Real.cosh x))) 0 ≤
    gaussianOperator 0 (h.height 0) (fun x : ℝ => c + |x|) 0 at hm
  rw [gaussianOperator_const_add (F := fun x : ℝ => |x|) measurable_id.abs IsingPerceptron.abs_linearGrowth,
    gaussianOperator_zero_abs] at hm
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    simp [fieldIncrement, h.first]
  simp only [fieldValue, List.ofFn_succ, List.foldr_cons, hroot]
  change gaussianOperator 0 (h.height 0)
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun x => Real.log (Real.cosh x))) 0 - h.height (Fin.last h.depth) / 2 ≤ _
  have hc : c = ∑ i : Fin h.depth,
      ((fieldIncrement h i.succ).1 * (fieldIncrement h i.succ).2 / 2 +
        Real.log 2 / (fieldIncrement h i.succ).1) := by
    simp only [c, L, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  rw [hc] at hm
  linarith

/-- The field value has a linear negative cost in its integrated height and
only a square-root positive cost at the root.  This is sufficient to make
the upper-comparison field cap inactive for a fixed trial partition. -/
lemma fieldValue_cap_estimate (h : FieldStep) :
    fieldValue h 0 ≤ -(∫ s, fieldFunction h s ∂pathMeasure) / 2 +
      Real.sqrt (h.height 0) * gaussianAbsoluteMean + fieldPartitionConstant h := by
  have harea := integral_fieldFunction_eq_increment_sum h
  have hs := fieldIncrement_sum h
  have hz : (fieldIncrement h 0).1 = 0 := by simp [fieldIncrement, h.first]
  have hcut : (∑ i : Fin (h.depth + 1),
      (fieldIncrement h i).1 * (fieldIncrement h i).2) =
      h.height (Fin.last h.depth) - ∫ s, fieldFunction h s ∂pathMeasure := by
    rw [harea, ← hs, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change h.cut i.castSucc * (fieldIncrement h i).2 = _
    ring
  rw [Fin.sum_univ_succ, hz, zero_mul, zero_add] at hcut
  have hv := fieldValue_abs_sum h
  rw [Finset.sum_add_distrib] at hv
  have hc : (∑ i : Fin h.depth,
      (fieldIncrement h i.succ).1 * (fieldIncrement h i.succ).2 / 2) =
      (h.height (Fin.last h.depth) - ∫ s, fieldFunction h s ∂pathMeasure) / 2 := by
    rw [← Finset.sum_div, hcut]
  rw [hc] at hv
  change fieldValue h 0 ≤ _ + (_ + fieldPartitionConstant h) - _ at hv
  linarith

lemma integral_fieldFunction_ge_last (h : FieldStep) :
    (1 - h.cut (Fin.last h.depth).castSucc) * h.height (Fin.last h.depth) ≤
      ∫ s, fieldFunction h s ∂pathMeasure := by
  rw [integral_fieldFunction]
  have hm : h.cut (Fin.last h.depth).succ = 1 := h.last
  rw [← hm]
  apply Finset.single_le_sum (f := fun i : Fin (h.depth + 1) =>
    (h.cut i.succ - h.cut i.castSucc) * h.height i) _ (Finset.mem_univ (Fin.last h.depth))
  intro i _
  exact mul_nonneg (sub_nonneg.mpr (h.ordered_cut.monotone (Fin.castSucc_le_succ i)))
    (h.nonneg i)

/-- With a trial uniformly below one, the negative last-height term dominates
all fields on that fixed partition. -/
lemma fieldValue_add_pairing_cap (p : OverlapPath) {d : ℝ} (hd : 0 ≤ d)
    (hp : ∀ᵐ s ∂pathMeasure, p s ≤ 1 - d) (h : FieldStep) :
    fieldValue h 0 + fieldPairing p h / 2 ≤
      -(d * (1 - h.cut (Fin.last h.depth).castSucc) / 2) *
          h.height (Fin.last h.depth) +
        gaussianAbsoluteMean * Real.sqrt (h.height (Fin.last h.depth)) +
        fieldPartitionConstant h := by
  have hv := fieldValue_cap_estimate h
  have hq := fieldPairing_le_const_integral p h (1 - d) hp
  have ha := integral_fieldFunction_ge_last h
  have hn := mul_le_mul_of_nonneg_left ha hd
  have hr := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (h.ordered_height (Fin.zero_le (Fin.last h.depth)))) gaussianAbsoluteMean_nonneg
  nlinarith

/-- The elementary square-root-versus-linear estimate needed to choose the
field cap. -/
lemma exists_linear_sqrt_cap {e : ℝ} (he : 0 < e) (C K B : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ x : ℝ, H ≤ x → -e * x + C * Real.sqrt x + K ≤ B := by
  let A := C ^ 2 / (2 * e) + |K| + |B| + 1
  let H := 2 * A / e
  have hA : 0 < A := by
    have ht : 0 ≤ C ^ 2 / (2 * e) := div_nonneg (sq_nonneg _) (by positivity)
    dsimp only [A]
    linarith [abs_nonneg K, abs_nonneg B]
  have hH : 0 < H := div_pos (mul_pos (by norm_num) hA) he
  refine ⟨H, hH, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := hH.le.trans hx
  have hsq := sq_nonneg (e * Real.sqrt x - C)
  have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  rw [sub_sq, mul_pow, hs] at hsq
  have hroot : C * Real.sqrt x ≤ e * x / 2 + C ^ 2 / (2 * e) := by
    calc
      _ ≤ (e ^ 2 * x + C ^ 2) / (2 * e) :=
        (le_div_iff₀ (show 0 < 2 * e by positivity)).2 (by nlinarith)
      _ = _ := by field_simp
  have hxe : 2 * A ≤ e * x := by
    change 2 * A / e ≤ x at hx
    have hh := (div_le_iff₀ he).1 hx
    nlinarith
  dsimp only [A] at hxe
  nlinarith [le_abs_self K, neg_le_abs B]

end InvariantIsing

end

end OAI
