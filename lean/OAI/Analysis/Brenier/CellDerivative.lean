import OAI.Analysis.Brenier.CellMeasure
import OAI.Analysis.Brenier.CutDerivative
import OAI.Analysis.Brenier.Interfaces
import OAI.Analysis.Brenier.SurfaceCoordinates

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators

namespace Problem358

open TangentNormalCoordinates

/-- The signed variation of one interface of a positive-mass affine cell.
Compactness, convexity, injectivity, and positive cell masses now discharge
all analytic bounds and all exceptional-face hypotheses. Other cuts may move
independently, as required by the finite-intersection telescoping formula. -/
theorem hasDerivAt_positive_cell_cut_remainder
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : ⟪z, y i⟫_ℝ + c i = ⟪z, y j⟫_ℝ + c j)
    (w : E d → ℝ) (hw : Continuous w) (v : E d) (r : ℝ)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    (ell : ℝ → ι → E d → ℝ)
    (hell : ∀ k ∈ J, Continuous (fun p : ℝ × E d => ell p.1 k p.2))
    (hell0 : ∀ k ∈ J, ∀ x, ell 0 k x = (⟪x, y i⟫_ℝ + c i) - (⟪x, y k⟫_ℝ + c k)) :
    HasDerivAt (fun h : ℝ => ∫ x,
      (K.indicator w x * ∏ k ∈ J, MovingCellTrace.cutIndicator (ell h k x)) *
        ((if 0 ≤ ⟪y i - y j + h • v, x⟫_ℝ + (c i - c j + h * r)
          then (1 : ℝ) else 0) -
          (if 0 ≤ ⟪y i - y j, x⟫_ℝ + (c i - c j) then (1 : ℝ) else 0)))
      (∫ a : Tangent (y i - y j),
        ((r + ⟪v, z + (a : E d)⟫_ℝ) / ‖y i - y j‖) *
          (K.indicator w (z + (a : E d)) *
            ∏ k ∈ J, MovingCellTrace.cutIndicator (ell 0 k (z + (a : E d))))) 0 := by
  let n := y i - y j
  have hn : n ≠ 0 := sub_ne_zero.mpr (hy.ne hij)
  let u : E d := (‖n‖⁻¹ : ℝ) • n
  let base : Tangent n → E d := fun a => z + (a : E d)
  let P : E d → Tangent n := fun x =>
    (WithLp.ofLp ((normalEquiv n hn).symm (x - z))).2
  have hbase : Continuous base := by fun_prop
  have hP : Continuous P := by
    unfold P
    fun_prop
  have hprojection : ∀ (a : Tangent n) (t : ℝ), P (base a + t • u) = a := by
    intro a t
    have heq : base a + t • u - z = normalMap n (t, a) := by
      simp only [base, u, normalMap]
      abel
    change (WithLp.ofLp ((normalEquiv n hn).symm (base a + t • u - z))).2 = a
    rw [heq, ← normalEquiv_apply n hn, LinearIsometryEquiv.symm_apply_apply]
  have hchart : MeasurePreserving
      (fun p : Tangent n × ℝ => base p.1 + p.2 • u) (volume.prod volume) volume := by
    convert measurePreserving_tangentMap n hn z using 1
    funext p
    simp [base, u, TangentNormalCoordinates.tangentMap, affineMap, normalMap,
      add_assoc, add_comm]
  have hface : ∀ a : Tangent n, ⟪n, base a⟫_ℝ + (c i - c j) = 0 := by
    intro a
    have ha : ⟪n, (a : E d)⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp a.property
    rw [show base a = z + (a : E d) from rfl, inner_add_right, ha, add_zero]
    dsimp [n]
    rw [inner_sub_left]
    have htie' : ⟪y i, z⟫_ℝ + c i = ⟪y j, z⟫_ℝ + c j := by
      simpa only [real_inner_comm] using htie
    linarith
  have hregular : ∀ᵐ a : Tangent n,
      base a ∉ frontier K ∧ ∀ k ∈ J, ell 0 k (base a) ≠ 0 := by
    filter_upwards [CellGeometry.ae_regular_interface hρ hK.isClosed hconv
      y c hy hpos hij hz htie volume] with a ha
    refine ⟨ha.1, ?_⟩
    intro k hk
    rw [hell0 k hk]
    exact sub_ne_zero.mpr (ha.2 k (hJ k hk).1 (hJ k hk).2)
  have hd := hasDerivAt_compact_affine_cut_remainder hK w hw base hbase
    n u v (c i - c j) r hchart P hP hprojection hface
    (inner_unitNormal_pos n hn) J ell hell hregular
  simpa only [n, u, base, inner_unitNormal _ hn] using hd

end Problem358

end

noncomputable section

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace BigOperators

namespace Problem358.PositiveCellFullDerivative

open TangentNormalCoordinates MovingCellTrace

lemma prod_sub_prod_ordered {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (a b : ι → ℝ) :
    (∏ k ∈ s, a k) - (∏ k ∈ s, b k) =
      ∑ j ∈ s, (a j - b j) *
        ∏ k ∈ s.erase j, if k < j then a k else b k := by
  classical
  have h := Finset.prod_add_ordered s b (fun k => a k - b k)
  simp only [add_sub_cancel] at h
  rw [sub_eq_iff_eq_add]
  rw [h, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.prod_ite]
  have hleft : {k ∈ s.erase j | k < j} = {k ∈ s | k < j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hk⟩, hkj⟩
      exact ⟨hk, hkj⟩
    · rintro ⟨hk, hkj⟩
      exact ⟨⟨ne_of_lt hkj, hk⟩, hkj⟩
  have hright : {k ∈ s.erase j | ¬ k < j} = {k ∈ s | j < k} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hk⟩, hkj⟩
      exact ⟨hk, lt_of_le_of_ne (le_of_not_gt hkj) (Ne.symm hne)⟩
    · rintro ⟨hk, hjk⟩
      exact ⟨⟨ne_of_gt hjk, hk⟩, not_lt_of_ge hjk.le⟩
  rw [hleft, hright]
  ring

lemma cutIndicator_eq_ite (r : ℝ) :
    cutIndicator r = if 0 ≤ r then 1 else 0 := by
  simp only [cutIndicator, Set.indicator_apply, Set.mem_Ici]

lemma norm_cutIndicator_sub_le_one (a b : ℝ) :
    ‖cutIndicator a - cutIndicator b‖ ≤ 1 := by
  rw [cutIndicator_eq_ite, cutIndicator_eq_ite]
  split_ifs <;> norm_num

/-- Ordered single-cut derivatives reassemble into the actual product integral.
The order is used only for the proof, not in the resulting derivative. -/
theorem hasDerivAt_cut_product_integral
    {ι X : Type*} [LinearOrder ι] [MeasurableSpace X]
    {μ : Measure X} (s : Finset ι) (ell : ℝ → ι → X → ℝ)
    (hell : ∀ t j, Measurable (ell t j))
    {w : X → ℝ} (hw : Integrable w μ) (D : ι → ℝ)
    (hd : ∀ j ∈ s, HasDerivAt (fun t : ℝ => ∫ x,
      (w x * ∏ k ∈ s.erase j,
        cutIndicator (if k < j then ell t k x else ell 0 k x)) *
          (cutIndicator (ell t j x) - cutIndicator (ell 0 j x)) ∂μ) (D j) 0) :
    HasDerivAt (fun t : ℝ => ∫ x,
      w x * ∏ j ∈ s, cutIndicator (ell t j x) ∂μ) (∑ j ∈ s, D j) 0 := by
  classical
  let term : ℝ → ι → X → ℝ := fun t j x =>
    (w x * ∏ k ∈ s.erase j,
      cutIndicator (if k < j then ell t k x else ell 0 k x)) *
        (cutIndicator (ell t j x) - cutIndicator (ell 0 j x))
  have hrem (t : ℝ) (j : ι) : Measurable (fun x =>
      ∏ k ∈ s.erase j, cutIndicator (if k < j then ell t k x else ell 0 k x)) := by
    apply measurable_cut_product
    intro k _
    split_ifs <;> exact hell _ _
  have hterm (t : ℝ) (j : ι) : Integrable (term t j) μ := by
    apply (hw.mul_bdd (hrem t j).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_cut_product_le_one _ _)).mul_bdd
      ((measurable_cutIndicator.comp (hell t j)).sub
        (measurable_cutIndicator.comp (hell 0 j))).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_cutIndicator_sub_le_one _ _)
  have hint (t : ℝ) : Integrable (fun x =>
      w x * ∏ j ∈ s, cutIndicator (ell t j x)) μ :=
    hw.mul_bdd (measurable_cut_product s (fun j _ => hell t j)).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_cut_product_le_one _ _)
  have heq (t : ℝ) :
      (∫ x, w x * ∏ j ∈ s, cutIndicator (ell t j x) ∂μ) -
        (∫ x, w x * ∏ j ∈ s, cutIndicator (ell 0 j x) ∂μ) =
      ∑ j ∈ s, ∫ x, term t j x ∂μ := by
    rw [← integral_sub (hint t) (hint 0), ← integral_finsetSum _ (fun j _ => hterm t j)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [← mul_sub, prod_sub_prod_ordered, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    simp only [apply_ite]
    ring
  have hs : HasDerivAt (fun t : ℝ => ∑ j ∈ s, ∫ x, term t j x ∂μ)
      (∑ j ∈ s, D j) 0 := HasDerivAt.fun_sum hd
  have hs' := hs.const_add (∫ x, w x * ∏ j ∈ s, cutIndicator (ell 0 j x) ∂μ)
  apply hs'.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro t
  dsimp only
  linarith [heq t]

lemma prod_cutIndicator_eq_indicator {ι X : Type*} (s : Finset ι)
    (ell : ι → X → ℝ) (x : X) :
    (∏ j ∈ s, cutIndicator (ell j x)) =
      {x | ∀ j ∈ s, 0 ≤ ell j x}.indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : ∀ j ∈ s, 0 ≤ ell j x
  · rw [Set.indicator_of_mem (s := {x | ∀ j ∈ s, 0 ≤ ell j x}) hx]
    apply Finset.prod_eq_one
    intro j hj
    simp [cutIndicator_eq_ite, hx j hj]
  · rw [Set.indicator_of_notMem (s := {x | ∀ j ∈ s, 0 ≤ ell j x}) hx]
    push Not at hx
    obtain ⟨j, hj, hneg⟩ := hx
    apply Finset.prod_eq_zero hj
    simp [cutIndicator_eq_ite, not_le_of_gt hneg]

/-- The signed face integral in a full affine-cell variation. -/
def faceVariation {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set (E d)) (y v : ι → E d) (c r : ι → ℝ)
    (w : E d → ℝ) (i j : ι) (z : E d) : ℝ :=
  ∫ a : Tangent (y i - y j),
    ((r i - r j + ⟪v i - v j, z + (a : E d)⟫_ℝ) / ‖y i - y j‖) *
      (K.indicator w (z + (a : E d)) *
        ∏ k ∈ (Finset.univ.erase i).erase j,
          cutIndicator ((⟪z + (a : E d), y i⟫_ℝ + c i) -
            (⟪z + (a : E d), y k⟫_ℝ + c k)))

/-- Full scalar weighted-cell derivative. Only actual compact convex positive-cell
geometry is assumed: all trace, domination, and signed-cut limits are proved. -/
theorem hasDerivAt_closedCell_integral
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y v : ι → E d) (c r : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    (w : E d → ℝ) (hw : Continuous w) (i : ι) (z : ι → E d)
    (hz : ∀ j, j ≠ i → z j ∈ interior K)
    (htie : ∀ j, j ≠ i → ⟪z j, y i⟫_ℝ + c i = ⟪z j, y j⟫_ℝ + c j) :
    HasDerivAt (fun t : ℝ => ∫ x in
      CellGeometry.closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i,
      w x)
      (∑ j ∈ Finset.univ.erase i, faceVariation K y v c r w i j (z j)) 0 := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let s : Finset ι := Finset.univ.erase i
  let ell : ℝ → ι → E d → ℝ := fun t j x =>
    ⟪y i - y j + t • (v i - v j), x⟫_ℝ + (c i - c j + t * (r i - r j))
  have hell (t : ℝ) (j : ι) : Measurable (ell t j) := by
    dsimp [ell]
    fun_prop
  have hell0 (j : ι) (x : E d) : ell 0 j x =
      (⟪x, y i⟫_ℝ + c i) - (⟪x, y j⟫_ℝ + c j) := by
    simp only [ell, zero_smul, add_zero, zero_mul, inner_sub_right, real_inner_comm]
    ring
  have hwK : Integrable (K.indicator w) (volume : Measure (E d)) :=
    (hw.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hd : HasDerivAt (fun t : ℝ => ∫ x,
      K.indicator w x * ∏ j ∈ s, cutIndicator (ell t j x))
      (∑ j ∈ s, faceVariation K y v c r w i j (z j)) 0 := by
    apply hasDerivAt_cut_product_integral s ell hell hwK
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    let mixed : ℝ → ι → E d → ℝ := fun t k x =>
      if k < j then ell t k x else ell 0 k x
    have hJ : ∀ k ∈ s.erase j, k ≠ i ∧ k ≠ j := by
      intro k hk
      exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,
        (Finset.mem_erase.mp hk).1⟩
    have hmix : ∀ k ∈ s.erase j, Continuous (fun p : ℝ × E d => mixed p.1 k p.2) := by
      intro k _
      dsimp [mixed]
      split_ifs <;> dsimp [ell] <;> fun_prop
    have hmix0 : ∀ k ∈ s.erase j, ∀ x, mixed 0 k x =
        (⟪x, y i⟫_ℝ + c i) - (⟪x, y k⟫_ℝ + c k) := by
      intro k _ x
      simp only [mixed, ite_self, hell0]
    have hsingle := hasDerivAt_positive_cell_cut_remainder hρ hK hconv y c hy hpos
      hji.symm (hz j hji) (htie j hji) w hw (v i - v j) (r i - r j)
      (s.erase j) hJ mixed hmix hmix0
    have hface : (∫ a : Tangent (y i - y j),
        ((r i - r j + ⟪v i - v j, z j + (a : E d)⟫_ℝ) / ‖y i - y j‖) *
          (K.indicator w (z j + (a : E d)) *
            ∏ k ∈ s.erase j, cutIndicator (mixed 0 k (z j + (a : E d))))) =
        faceVariation K y v c r w i j (z j) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro a
      dsimp only [faceVariation]
      congr 2
      apply Finset.prod_congr rfl
      intro k hk
      rw [hmix0 k hk]
    rw [hface] at hsingle
    apply hsingle.congr_of_eventuallyEq
    apply Eventually.of_forall
    intro t
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    simp only [mixed, ell, cutIndicator_eq_ite, zero_smul, zero_mul, add_zero]
    congr 2
    apply Finset.prod_congr
    · ext k; simp
    · intro k _; rfl
  have heq (t : ℝ) : (∫ x in
      CellGeometry.closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i,
      w x) = ∫ x, K.indicator w x * ∏ j ∈ s, cutIndicator (ell t j x) := by
    rw [← integral_indicator (CellGeometry.isClosed_closedCell hK.isClosed _ _ i).measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [prod_cutIndicator_eq_indicator]
    have hmem : x ∈ CellGeometry.closedCell K
        (fun j => y j + t • v j) (fun j => c j + t * r j) i ↔
        x ∈ K ∧ ∀ j ∈ s, 0 ≤ ell t j x := by
      constructor
      · rintro ⟨hxK, hx⟩
        refine ⟨hxK, ?_⟩
        intro j _
        have hj := hx j
        simp only [ell, inner_add_left, inner_smul_left, inner_sub_left,
          inner_add_right, inner_smul_right, real_inner_comm, starRingEnd_apply, star_trivial] at hj ⊢
        nlinarith
      · rintro ⟨hxK, hx⟩
        refine ⟨hxK, ?_⟩
        intro j
        by_cases hji : j = i
        · subst j; exact le_rfl
        have hj := hx j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
        simp only [ell, inner_add_left, inner_smul_left, inner_sub_left,
          inner_add_right, inner_smul_right, real_inner_comm, starRingEnd_apply, star_trivial] at hj ⊢
        nlinarith
    by_cases hxK : x ∈ K <;> by_cases hx : ∀ j ∈ s, 0 ≤ ell t j x <;>
      simp [Set.indicator_apply, hmem, hxK, hx]
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall heq

end Problem358.PositiveCellFullDerivative

end

/-! Actual vector moment and real mass differentials for positive affine cells.
This specializes the proved scalar moving-cell formula, not an assumed derivative. -/

noncomputable section
open MeasureTheory Set
open scoped Topology InnerProductSpace BigOperators

namespace Problem358.PositiveCellFullDerivative

/-- The genuine vector first-moment derivative, written in coordinates of the
signed intrinsic face integrals. All scalar differentiation hypotheses are
discharged by the full-cell calculus. -/
theorem hasDerivAt_uniform_closedCell_moment
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y v : ι → E d) (c r : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    (i : ι) (z : ι → E d)
    (hz : ∀ j, j ≠ i → z j ∈ interior K)
    (htie : ∀ j, j ≠ i → ⟪z j, y i⟫_ℝ + c i = ⟪z j, y j⟫_ℝ + c j) :
    HasDerivAt (fun t : ℝ => ∫ x in
      CellGeometry.closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i,
      x ∂uniformMeasure K)
      ((volume K).toReal⁻¹ • (WithLp.toLp 2 fun k : Fin d =>
        ∑ j ∈ Finset.univ.erase i, faceVariation K y v c r (fun x => x k) i j (z j))) 0 := by
  apply CellVectorDerivative.hasDerivAt_uniform_cellMoment_of_coordinates hK
    (fun t j => y j + t • v j) (fun t j => c j + t * r j) i
  intro k
  exact hasDerivAt_closedCell_integral hρ hK hconv y v c r hy hpos
    (fun x => x k) (by fun_prop) i z hz htie

/-- The true real mass derivative of a positive cell under the probability
source, with normalization by the source volume. -/
theorem hasDerivAt_uniform_closedCell_mass
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y v : ι → E d) (c r : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    (i : ι) (z : ι → E d)
    (hz : ∀ j, j ≠ i → z j ∈ interior K)
    (htie : ∀ j, j ≠ i → ⟪z j, y i⟫_ℝ + c i = ⟪z j, y j⟫_ℝ + c j) :
    HasDerivAt (fun t : ℝ => (uniformMeasure K).real
      (CellGeometry.closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i))
      ((∑ j ∈ Finset.univ.erase i, faceVariation K y v c r (fun _ => 1) i j (z j)) /
        (volume K).toReal) 0 := by
  apply CellVectorDerivative.hasDerivAt_uniform_cellMass hK
    (fun t j => y j + t • v j) (fun t j => c j + t * r j) i
  simpa only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
    Measure.real_def] using
    hasDerivAt_closedCell_integral hρ hK hconv y v c r hy hpos
      (fun _ => 1) continuous_const i z hz htie

end Problem358.PositiveCellFullDerivative

end

end OAI
