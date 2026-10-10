import OAI.Probability.InvariantIsing.Magnetic.MagneticHeightOrder
import OAI.Probability.InvariantIsing.Magnetic.MagneticRadialHessian
import OAI.Probability.InvariantIsing.Fields.FieldHessianAlgebra

namespace OAI

/-! The mixed sign of the constrained height Hessian follows from the
actual positive coordinate variation. Together with radial monotonicity,
it gives the negative quadratic-form sign. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

private lemma deriv_nonpos_of_right_order {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [hf, self_mem_nhdsWithin] with t ht hpos
  simpa only [zero_add, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hpos.le) (sub_nonpos.mpr ht)

private lemma update_eq_coordinate_line {n : ℕ} (r : Fin n → ℝ)
    (j : Fin n) (t : ℝ) :
    Function.update r j (r j + t) = r + t • Pi.single j (1 : ℝ) := by
  classical
  funext k
  by_cases hkj : k = j
  · subst k
    simp
  · simp [Function.update_of_ne hkj, Pi.single_eq_of_ne hkj]

private lemma heightLevel_update (h : FieldStep) {s : ℝ}
    (r : Fin (h.depth + 1) → ℝ) (hrs : r ∈ fieldStrictHeightCone h.depth)
    (j : Fin (h.depth + 1)) (t : ℝ)
    (ht : Function.update r j (r j + t) ∈ fieldStrictHeightCone h.depth)
    (i : Fin (h.depth + 1)) :
    magneticHeightLevel h s (r + t • Pi.single j (1 : ℝ)) i =
      magneticFieldLevel (fieldStepOfStrictHeights (fieldStepOfStrictHeights h r hrs)
        (Function.update r j (r j + t)) ht) s i := by
  rw [← update_eq_coordinate_line, magneticHeightLevel, dite_eq_left ht]
  rfl

lemma magneticHeightLevel_coordinate_right_order (h : FieldStep) {s : ℝ}
    (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hrs : r ∈ fieldStrictHeightCone h.depth)
    (i j : Fin (h.depth + 1)) (hij : i < j) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      magneticHeightLevel h s (r + t • Pi.single j (1 : ℝ)) i ≤
        magneticHeightLevel h s r i := by
  let k := fieldStepOfStrictHeights h r hrs
  have hbase : magneticHeightLevel h s r i = magneticFieldLevel k s i := by
    rw [magneticHeightLevel, dite_eq_left hrs]
  have hq : ContinuousAt (fun t : ℝ => Function.update r j (r j + t)) 0 := by
    apply continuousAt_pi.2
    intro l
    by_cases hlj : l = j
    · subst l
      simp only [Function.update_self]
      fun_prop
    · simpa only [Function.update_of_ne hlj] using continuousAt_const
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ),
      Function.update r j (r j + t) ∈ fieldStrictHeightCone h.depth :=
    hq.eventually ((isOpen_fieldStrictHeightCone _).mem_nhds (by simpa using hrs))
  revert hij hn
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij hn
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hpos
    rw [heightLevel_update h r hrs _ t ht i, hbase]
    exact magneticFieldLevel_terminal_update_le k hpos.le ht hs i hij
  · intro hij hn
    have hj : 0 < j.val := by change i.val < j.val at hij; omega
    have hgap : 0 < (fieldIncrement k j.succ).2 := hrs j.succ
    have hb : ∀ᶠ t in 𝓝 (0 : ℝ), t < (fieldIncrement k j.succ).2 :=
      Iio_mem_nhds hgap
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,
      hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hbound hpos
    rw [heightLevel_update h r hrs _ t ht i, hbase]
    exact magneticFieldLevel_interior_update_le k j hj hpos.le hbound.le ht hs i hij

theorem magneticHeightSchur_mixed_nonneg (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ I) (hrs : r ∈ fieldStrictHeightCone h.depth)
    (i j : Fin (h.depth + 1)) (hij : i < j) :
    0 ≤ magneticHeightSchur h F s r i j := by
  have hd := hasDerivAt_magneticHeightLevel_line h F hI hU hs r
    (Pi.single j 1) hr hrs i
  have hn := deriv_nonpos_of_right_order hd
    (by simpa only [zero_smul, add_zero] using
      magneticHeightLevel_coordinate_right_order h hs r hrs i j hij)
  have he : (∑ k, magneticHeightSchur h F s r i k * (Pi.single j (1 : ℝ) : Fin (h.depth + 1) → ℝ) k) =
      magneticHeightSchur h F s r i j := by
    classical
    simp [Pi.single_apply]
  rw [he] at hn
  have hw : 0 < h.cut i.succ - h.cut i.castSucc :=
    sub_pos.mpr (h.ordered_cut i.castSucc_lt_succ)
  have hc : -2 / (h.cut i.succ - h.cut i.castSucc) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hw
  nlinarith

theorem magneticHeightSchur_quadratic_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ I) (hrs : r ∈ fieldStrictHeightCone h.depth)
    (x : Fin (h.depth + 1) → ℝ) :
    ∑ i, ∑ j, magneticHeightSchur h F s r i j * x i * x j ≤ 0 := by
  let M := fun i j => -magneticHeightSchur h F s r i j
  have hsym : ∀ i j, M i j = M j i := fun i j =>
    congrArg Neg.neg (magneticHeightSchur_symmetric h F s r hr i j)
  have hoff : ∀ i j, i ≠ j → M i j ≤ 0 := by
    intro i j hij
    apply neg_nonpos.mpr
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact magneticHeightSchur_mixed_nonneg h F hI hU hs r hr hrs i j hlt
    · rw [magneticHeightSchur_symmetric h F s r hr i j]
      exact magneticHeightSchur_mixed_nonneg h F hI hU hs r hr hrs j i hgt
  have hpos : ∀ i, 0 < r i := by
    intro i
    have h0 : 0 < r 0 := by simpa [fieldHeightIncrement] using hrs 0
    exact h0.trans_le ((fieldStrictHeightCone_strictMono hrs).monotone (Fin.zero_le i))
  have hrow : ∀ i, 0 ≤ ∑ j, M i j * r j := by
    intro i
    have he := magneticHeight_radial_hessian_nonpos h F hI hU hs r hr hrs i
    simpa only [M, neg_mul, Finset.sum_neg_distrib, neg_nonneg] using he
  have hq := field_quadratic_nonneg_of_positive_scaling M r hsym hoff hpos hrow x
  simpa only [M, neg_mul, Finset.sum_neg_distrib, neg_nonneg] using hq

end InvariantIsing

end

end OAI
