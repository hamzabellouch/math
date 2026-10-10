import OAI.Probability.ContinuumTransition.TailComparison

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def blockCut (q : ℕ) (V : Space → Space → ℝ) (x y : Space) : ℝ :=
  if gridIndex ((q : ℝ)/4) x = gridIndex ((q : ℝ)/4) y then V x y else 0

noncomputable def deletedCore (t : ℝ) (σ τ R : ℕ → ℝ) (q : ℕ) (x y : Space) : ℝ :=
  blockCut q (fun x y => coreProfile t ‖x-y‖) x y-
    attraction t σ R ‖x-y‖-attraction t τ R ‖x-y‖

noncomputable def cutReference (t : ℝ) (σ τ R : ℕ → ℝ) (q : ℕ) (x y : Space) : ℝ :=
  blockCut q (fun x y => physicalProfile t σ R ‖x-y‖) x y-attraction t τ R ‖x-y‖

theorem measurable_gridIndex (u : ℝ) : Measurable (gridIndex u) := by
  apply Measurable.of_eval
  intro i
  exact ((EuclideanSpace.proj i).continuous.measurable.div_const u).floor

theorem measurable_blockCut (q : ℕ) {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) : Measurable (Function.uncurry (blockCut q V)) := by
  apply hV.ite ?_ measurable_const
  exact measurableSet_eq_fun ((measurable_gridIndex _).comp measurable_fst)
    ((measurable_gridIndex _).comp measurable_snd)

theorem blockCut_symm (q : ℕ) {V : Space → Space → ℝ} (hV : ∀ x y, V x y = V y x) :
    ∀ x y, blockCut q V x y = blockCut q V y x := by
  intro x y
  simp only [blockCut, eq_comm, hV x y]

theorem measurable_deletedCore (t : ℝ) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (q : ℕ) :
    Measurable (Function.uncurry (deletedCore t σ τ R q)) :=
  ((measurable_blockCut q (V := fun x y => coreProfile t ‖x-y‖) ((measurable_coreProfile t).comp
    ((measurable_fst.sub measurable_snd).norm))).sub
    ((continuous_attraction t hσ hR hs).measurable.comp
      ((measurable_fst.sub measurable_snd).norm))).sub
    ((continuous_attraction t hτ hR hτs).measurable.comp
      ((measurable_fst.sub measurable_snd).norm))

theorem measurable_cutReference (t : ℝ) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (q : ℕ) :
    Measurable (Function.uncurry (cutReference t σ τ R q)) :=
  (measurable_blockCut q (V := fun x y => physicalProfile t σ R ‖x-y‖) (measurable_physical_interaction t hσ hR hs)).sub
    ((continuous_attraction t hτ hR hτs).measurable.comp
      ((measurable_fst.sub measurable_snd).norm))

theorem deletedCore_symm (t : ℝ) (σ τ R : ℕ → ℝ) (q : ℕ) :
    ∀ x y, deletedCore t σ τ R q x y = deletedCore t σ τ R q y x := by
  intro x y
  unfold deletedCore
  rw [blockCut_symm q (fun x y => by rw [norm_sub_rev x y]), norm_sub_rev x y]

theorem cutReference_symm (t : ℝ) (σ τ R : ℕ → ℝ) (q : ℕ) :
    ∀ x y, cutReference t σ τ R q x y = cutReference t σ τ R q y x := by
  intro x y
  unfold cutReference
  rw [blockCut_symm q (fun x y => by rw [norm_sub_rev x y]), norm_sub_rev x y]

theorem deletedCore_lower {t : ℝ} (ht : 0 ≤ t) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (q : ℕ) :
    CellLowerBound t (fun n => σ n+τ n) R (deletedCore t σ τ R q) := by
  have ha := masked_physical_cellLowerBound ht (fun n => add_nonneg (hσ n) (hτ n)) hR
    (hs.add hτs) (fun x y => if gridIndex ((q : ℝ)/4) x = gridIndex ((q : ℝ)/4) y then 1 else 0)
    (fun _ _ => 1) (fun _ _ => by split_ifs <;> norm_num)
    (fun x y hxy => ite_eq_left (gridIndex_eq_of_cellIndex_eq q hxy)) (fun _ _ => le_refl 1)
  intro x y
  specialize ha x y
  dsimp only at ha
  rw [attraction_add t hσ hτ hR hs hτs] at ha
  simpa only [deletedCore, blockCut, ite_mul, one_mul, zero_mul, sub_sub] using ha

theorem deletedCore_le_cutReference {t : ℝ} (ht : 0 ≤ t) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (q : ℕ) (x y : Space) :
    deletedCore t σ τ R q x y ≤ cutReference t σ τ R q x y := by
  unfold deletedCore cutReference blockCut physicalProfile
  split_ifs
  · rfl
  · linarith only [attraction_nonneg ht hσ hR ‖x-y‖]

theorem deletedCore_le_physical (t : ℝ) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (q : ℕ) (x y : Space) :
    deletedCore t σ τ R q x y ≤ physicalProfile t (fun n => σ n+τ n) R ‖x-y‖ := by
  unfold deletedCore blockCut physicalProfile
  rw [attraction_add t hσ hτ hR hs hτs]
  split_ifs <;> linarith only [coreProfile_nonneg t ‖x-y‖]

theorem cutReference_diff (t : ℝ) (σ τ R : ℕ → ℝ) (q : ℕ) (x y : Space) :
    cutReference t σ τ R q x y-deletedCore t σ τ R q x y =
      if gridIndex ((q : ℝ)/4) x = gridIndex ((q : ℝ)/4) y then 0 else attraction t σ R ‖x-y‖ := by
  unfold cutReference deletedCore blockCut physicalProfile
  split_ifs <;> ring

theorem attraction_finite_range (t : ℝ) {σ R : ℕ → ℝ} (hR : ∀ n, 1 ≤ R n)
    {R₀ r : ℝ} (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀) (hr : R₀ ≤ r) :
    attraction t σ R r = 0 := by
  unfold attraction
  have he (n : ℕ) : σ n*scaledKernelProfile (R n) r = 0 := by
    by_cases hn : σ n = 0
    · rw [hn, zero_mul]
    · rw [scaledKernelProfile_zero (lt_of_lt_of_le zero_lt_one (hR n)) ((hbound n hn).trans hr), mul_zero]
  simp only [he, tsum_zero, mul_zero]

theorem cutReference_boundary_bound {t : ℝ} (ht : 0 ≤ t) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    {m q : ℕ} (hq : 0 < q) {x y : Space} (hx : x ∈ cube ((m : ℝ)*(q : ℝ)/2)) :
    cutReference t σ τ R q x y-deletedCore t σ τ R q x y ≤
      if cellIndex x ∈ boundaryIndices m q (cellRadius R₀).toNat then
        physicalCoupling t σ R (cellIndex x) (cellIndex y) else 0 := by
  rw [cutReference_diff]
  by_cases hc : gridIndex ((q : ℝ)/4) x = gridIndex ((q : ℝ)/4) y
  · rw [ite_eq_left hc]
    split_ifs
    · exact physicalCoupling_nonneg ht hσ hR _ _
    · rfl
  rw [ite_eq_right hc]
  by_cases hd : ‖x-y‖ ≤ R₀
  · have hh := cellIndex_mem_nearCells hd
    have he : cellIndex x ∈ boundaryIndices m q (cellRadius R₀).toNat := by
      apply boundary_of_close_crossing hq hx ?_ hc
      intro i
      rw [Int.toNat_of_nonneg (cellRadius_nonneg hR₀)]
      simpa only [abs_sub_comm] using (mem_nearCells_iff.mp hh i)
    rw [ite_eq_left he]
    exact attraction_le_mixedEnvelope ht hσ hR hs x y
  · rw [attraction_finite_range t hR hbound (le_of_not_ge hd)]
    split_ifs
    · exact physicalCoupling_nonneg ht hσ hR _ _
    · rfl

end ContinuumTemperature
end

end OAI
