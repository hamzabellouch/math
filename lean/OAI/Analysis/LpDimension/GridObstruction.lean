import OAI.Analysis.LpDimension.Parallelogram

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uA uE uI uJ

namespace SubpolynomialLp

section Grid
variable {I : Type uI} [Fintype I] [DecidableEq I]

def rowVector (i : I) : I × I → ℝ := fun ab => if ab.1 = i then 1 else 0
def colVector (j : I) : I × I → ℝ := fun ab => if ab.2 = j then 1 else 0
abbrev GridIndex (I : Type uI) := Option ((I ⊕ I) × Bool)
def gridVector : GridIndex I → I × I → ℝ
  | none => 0
  | some (Sum.inl i, false) => rowVector i
  | some (Sum.inl i, true) => -rowVector i
  | some (Sum.inr j, false) => colVector j
  | some (Sum.inr j, true) => -colVector j

omit [Fintype I] in
lemma row_disjoint (i i' : I) (hne : i ≠ i') (ab : I × I) :
    rowVector i ab = 0 ∨ rowVector i' ab = 0 := by
  by_cases h : ab.1 = i
  · right
    simp [rowVector, h, hne]
  · left; simp [rowVector, h]

omit [Fintype I] in
lemma col_disjoint (j j' : I) (hne : j ≠ j') (ab : I × I) :
    colVector j ab = 0 ∨ colVector j' ab = 0 := by
  by_cases h : ab.2 = j
  · right
    simp [colVector, h, hne]
  · left; simp [colVector, h]

omit [Fintype I] in
lemma row_col_not_disjoint (i j : I) :
    ¬ (∀ ab, rowVector i ab = 0 ∨ colVector j ab = 0) := by
  intro h
  simpa [rowVector, colVector] using h (i,j)

lemma grid_dimension_obstruction {E : Type uE} [Fintype E] (p : ℝ)
    (hp : 1 < p) (hp2 : p ≠ 2) (f : GridIndex I → E → ℝ)
    (hf0 : f none = 0)
    (hf : ∀ i j, lpPower p (f i-f j) = lpPower p (gridVector i-gridVector j)) :
    (Fintype.card I)^2 ≤ Fintype.card E := by
  let r : I → E → ℝ := fun i => f (some (Sum.inl i, false))
  let c : I → E → ℝ := fun j => f (some (Sum.inr j, false))
  have hn (i : GridIndex I) : lpPower p (f i) = lpPower p (gridVector i) := by
    simpa only [hf0, gridVector, sub_zero] using hf i none
  have hneg (i : I ⊕ I) : gridVector (some (i,true)) = -gridVector (some (i,false)) := by
    cases i <;> rfl
  have hant (i : I ⊕ I) : f (some (i,true)) = -f (some (i,false)) := by
    apply antipodes_of_lpPower p hp
    · rw [hn, hn, hneg, lpPower_neg]
    · have hh := hf (some (i,false)) (some (i,true))
      have he : gridVector (some (i,false)) - gridVector (some (i,true)) =
          (2:ℝ) • gridVector (some (i,false)) := by
        rw [hneg]
        module
      rw [he, lpPower_smul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      rw [hn]
      exact hh
  have hd (i j : I ⊕ I) :
      (∀ a, f (some (i,false)) a = 0 ∨ f (some (j,false)) a = 0) ↔
      (∀ a, gridVector (some (i,false)) a = 0 ∨ gridVector (some (j,false)) a = 0) := by
    rw [← lpPower_disjointness p (by linarith) hp2, ← lpPower_disjointness p (by linarith) hp2]
    have he : gridVector (some (j,true)) = -gridVector (some (j,false)) := by
      cases j <;> rfl
    have hs : lpPower p (f (some (i,false)) + f (some (j,false))) =
        lpPower p (gridVector (some (i,false)) + gridVector (some (j,false))) := by
      have hh := hf (some (i,false)) (some (j,true))
      simpa only [hant, he, sub_neg_eq_add] using hh
    rw [hs, hf, hn, hn]
  apply le_trans _ (disjoint_rows_columns_card r c ?_ ?_ ?_)
  · simp [sq]
  · intro i i' hh
    exact (hd (Sum.inl i) (Sum.inl i')).mpr (row_disjoint i i' hh)
  · intro j j' hh
    exact (hd (Sum.inr j) (Sum.inr j')).mpr (col_disjoint j j' hh)
  · intro i j
    have hh : ¬ (∀ a, r i a = 0 ∨ c j a = 0) := by
      intro ha
      exact row_col_not_disjoint i j ((hd (Sum.inl i) (Sum.inr j)).mp ha)
    push Not at hh
    exact hh

end Grid

section FiniteLp
variable {I : Type uI} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma finite_memLp (p : ℝ) (x : I → ℝ) : MemLp x (ENNReal.ofReal p) Measure.count := by
  exact eLpNorm_count_lt_top_of_lt (fun i => by simp)

def finiteToLp (p : ℝ) (x : I → ℝ) : Lp ℝ (ENNReal.ofReal p) (Measure.count : Measure I) :=
  (finite_memLp p x).toLp x

lemma finiteToLp_sub (p : ℝ) (x y : I → ℝ) :
    finiteToLp p (x-y) = finiteToLp p x - finiteToLp p y := by
  exact (finite_memLp p x).toLp_sub (finite_memLp p y)

lemma finiteToLp_injective (p : ℝ) : Function.Injective (finiteToLp (I := I) p) := by
  intro x y hh
  have h := (finite_memLp p x).coeFn_toLp.symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ (ENNReal.ofReal p) Measure.count =>
        (f : I → ℝ)) hh)).trans (finite_memLp p y).coeFn_toLp)
  exact funext ((Measure.ae_count_iff).mp h)

lemma finiteToLp_norm (p : ℝ) (hp : 0 < p) (x : I → ℝ) :
    ‖finiteToLp p x‖ = (∑ i, |x i|^p)^(1/p) := by
  rw [finiteToLp, Lp.norm_toLp, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
      (finite_memLp p x).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, integral_count]
  simp only [Real.norm_eq_abs, one_div]

lemma finiteToLp_infinite [Nonempty I] (p : ℝ) :
    Infinite (Lp ℝ (ENNReal.ofReal p) (Measure.count : Measure I)) := by
  apply Infinite.of_injective (fun a : ℝ => finiteToLp p (fun _ : I => a))
  intro a b he
  have hh := finiteToLp_injective p he
  exact congrFun hh (Classical.arbitrary I)

lemma finite_extend_card {A : Type uA} [Infinite A] (t : Finset A) (n : ℕ) (h : t.card ≤ n) :
    ∃ s : Finset A, t ⊆ s ∧ s.card = n := by
  classical
  obtain ⟨u, hu⟩ := Finset.exists_card_eq (α := A) n
  have hn : n ≤ (t ∪ u).card := hu.symm.trans_le (Finset.card_le_card Finset.subset_union_right)
  obtain ⟨s, hts, _, hs⟩ := Finset.exists_subsuperset_card_eq Finset.subset_union_left h hn
  exact ⟨s, hts, hs⟩


end FiniteLp

lemma GoodDimension.finite_family {p D : ℝ} {n d : ℕ} (h : GoodDimension.{u} p n D d)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [Infinite (Lp ℝ (ENNReal.ofReal p) μ)] {J : Type uJ} [Fintype J]
    (x : J → Lp ℝ (ENNReal.ofReal p) μ) (hJ : Fintype.card J ≤ n) :
    ∃ (y : J → Fin d → ℝ) (s : ℝ), 0 < s ∧
      ∀ i j, s * ‖x i-x j‖ ≤ coordinateDistance p (y i) (y j) ∧
        coordinateDistance p (y i) (y j) ≤ D*s*‖x i-x j‖ := by
  classical
  let t := Finset.univ.image x
  have ht : t.card ≤ n := (Finset.card_image_le).trans (by simpa using hJ)
  obtain ⟨S, hS, hc⟩ := finite_extend_card t n ht
  let e : S ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hc)
  let z : Fin n → Lp ℝ (ENNReal.ofReal p) μ := fun i => (e.symm i).val
  have hz : Function.Injective z := Subtype.val_injective.comp e.symm.injective
  obtain ⟨y, s, hs, hy⟩ := h Ω inferInstance μ z hz
  let j : J → S := fun i => ⟨x i, hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  refine ⟨fun i => y (e (j i)), s, hs, ?_⟩
  intro a b
  simpa only [z, Equiv.symm_apply_apply, j] using hy (e (j a)) (e (j b))

lemma coordinateDistance_rpow (p : ℝ) (hp : 0 < p) {d : ℕ} (x y : Fin d → ℝ) :
    coordinateDistance p x y ^ p = lpPower p (x-y) := by
  unfold coordinateDistance
  rw [one_div, Real.rpow_inv_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne']
  rfl

lemma finiteToLp_norm_rpow (p : ℝ) (hp : 0 < p) {I : Type uI} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (x : I → ℝ) :
    ‖finiteToLp p x‖^p = lpPower p x := by
  rw [finiteToLp_norm p hp, one_div, Real.rpow_inv_rpow]
  · rfl
  · exact lpPower_nonneg p x
  · exact hp.ne'

lemma exact_lower_of_goodDimension (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2)
    (n d : ℕ) (hn : 9 ≤ n) (hd : GoodDimension.{u} p n 1 d) :
    ((n-1)/4)^2 ≤ d := by
  classical
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let k := (n-1)/4
  have hk : 0 < k := by dsimp [k]; omega
  have : NeZero k := ⟨by omega⟩
  let Ω := ULift.{u} (Fin k × Fin k)
  let : MeasurableSpace Ω := ⊤
  have : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  let X : GridIndex (Fin k) → Ω → ℝ := fun i a => gridVector i a.down
  let x : GridIndex (Fin k) → Lp ℝ (ENNReal.ofReal p) (Measure.count : Measure Ω) :=
    fun i => finiteToLp p (X i)
  have := finiteToLp_infinite (I := Ω) p
  have hJ : Fintype.card (GridIndex (Fin k)) ≤ n := by
    simp only [GridIndex, Fintype.card_option, Fintype.card_prod, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_bool]
    dsimp [k]
    omega
  obtain ⟨y,s,hs,hy⟩ := hd.finite_family Measure.count x hJ
  have hxy (i j) : lpPower p (y i-y j) = s^p * lpPower p (gridVector i-gridVector j) := by
    have he : coordinateDistance p (y i) (y j) = s * ‖x i-x j‖ :=
      (hy i j).2.trans_eq (by ring) |>.antisymm (hy i j).1
    have hpow := congrArg (fun a : ℝ => a^p) he
    rw [coordinateDistance_rpow p (by linarith), Real.mul_rpow hs.le (norm_nonneg _)] at hpow
    have hnrm : ‖x i-x j‖^p = lpPower p (gridVector i-gridVector j) := by
      change ‖finiteToLp p (X i)-finiteToLp p (X j)‖^p = _
      rw [← finiteToLp_sub, finiteToLp_norm_rpow p (by linarith)]
      simp only [lpPower, Pi.sub_apply, X]
      exact (Equiv.ulift : Ω ≃ Fin k × Fin k).sum_comp (fun a => |gridVector i a - gridVector j a|^p)
    rwa [hnrm] at hpow
  let f : GridIndex (Fin k) → Fin d → ℝ := fun i => s⁻¹ • (y i-y none)
  have hf0 : f none = 0 := by simp [f]
  have hf (i j) : lpPower p (f i-f j) = lpPower p (gridVector i-gridVector j) := by
    have he : f i-f j = s⁻¹ • (y i-y j) := by dsimp [f]; module
    rw [he, lpPower_smul, abs_inv, abs_of_pos hs, Real.inv_rpow hs.le, hxy,
      inv_mul_cancel_left₀ (Real.rpow_pos_of_pos hs p).ne']
  have hh := grid_dimension_obstruction p hp hp2 f hf0 hf
  simpa only [Fintype.card_fin] using hh

end SubpolynomialLp

end

end OAI
