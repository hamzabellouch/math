import OAI.Analysis.Brenier.CellDerivative
import OAI.Analysis.Brenier.SurfaceMeasure

namespace OAI

/-! Canonical first-moment coefficients of common affine-cell faces. -/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- A common cell face is exactly one closed cell restricted to the tie plane. -/
theorem mem_commonFace_iff (K : Set (E d)) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) (x : E d) :
    x ∈ closedCell K y c i ∩ closedCell K y c j ↔
      x ∈ closedCell K y c i ∧ ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j := by
  constructor
  · intro hx
    exact ⟨hx.1, le_antisymm (hx.2.2 i) (hx.1.2 j)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, hx.1, fun k => heq ▸ hx.2 k⟩

/-- On the tie plane only the other branches constrain the common face. -/
theorem mem_commonFace_iff_of_tie (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i j : ι) {x : E d}
    (htie : ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j) :
    x ∈ closedCell K y c i ∩ closedCell K y c j ↔
      x ∈ K ∧ ∀ k, k ≠ i → k ≠ j → ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i := by
  rw [mem_commonFace_iff]
  constructor
  · rintro ⟨hx, _⟩
    exact ⟨hx.1, fun k _ _ => hx.2 k⟩
  · rintro ⟨hx, hother⟩
    refine ⟨⟨hx, fun k => ?_⟩, htie⟩
    by_cases hki : k = i
    · subst k
      exact le_rfl
    by_cases hkj : k = j
    · subst k
      exact htie.ge
    exact hother k hki hkj

/-- The vector face coefficient used by both mass site-motion and stationary
first-moment differentiation. The diagonal is zero by the normal-length factor. -/
def faceMoment (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i j : ι) : E d :=
  ((volume K).toReal * ‖y i - y j‖)⁻¹ •
    ∫ x in closedCell K y c i ∩ closedCell K y c j, x
      ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)

theorem faceMoment_symm (K : Set (E d)) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) : faceMoment K y c i j = faceMoment K y c j i := by
  exact (IntrinsicSurface.normalized_face_integral_swap (y i) (y j)
    (c i) (c j) (volume K).toReal (closedCell K y c i)
    (closedCell K y c j) (fun x => x)).symm

@[simp] theorem faceMoment_self (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i : ι) : faceMoment K y c i i = 0 := by
  simp [faceMoment]

/-- A tie-plane chart gives the same canonical normalized first moment. -/
theorem faceMoment_eq_chart (K : Set (E d)) (y : ι → E d) (c : ι → ℝ)
    {i j : ι} (hy : y i ≠ y j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j) :
    faceMoment K y c i j = ((volume K).toReal * ‖y i - y j‖)⁻¹ •
      ∫ w : (ℝ ∙ (y i - y j))ᗮ in
        {w : (ℝ ∙ (y i - y j))ᗮ |
          z + (w : E d) ∈ closedCell K y c i ∩ closedCell K y c j},
        z + (w : E d) := by
  unfold faceMoment
  rw [IntrinsicSurface.interfaceMeasure_setIntegral_of_tie hy
    (by simpa only [real_inner_comm] using htie)]

end Problem358.CellGeometry

end

/-! Identification of the cut-product trace with the genuine common cell face. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- On an equality plane the remaining cut indicators describe exactly the
common face, including its boundary. -/
theorem commonFace_indicator_eq_cut_product (K : Set (E d))
    (y : ι → E d) (c : ι → ℝ) (i j : ι) (J : Finset ι)
    (hJ : ∀ k, k ∈ J ↔ k ≠ i ∧ k ≠ j) (f : E d → ℝ) {x : E d}
    (htie : ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j) :
    (closedCell K y c i ∩ closedCell K y c j).indicator f x =
      K.indicator f x * ∏ k ∈ J,
        MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k)) := by
  classical
  have hcut (k : ι) :
      MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k)) =
        if ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i then 1 else 0 := by
    have hle : 0 ≤ ⟪x, y i - y k⟫ + (c i - c k) ↔
        ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i := by
      rw [inner_sub_right]
      constructor <;> intro h <;> linarith
    simp only [MovingCellTrace.cutIndicator, Set.indicator_apply, Set.mem_Ici, hle]
  by_cases hx : x ∈ closedCell K y c i ∩ closedCell K y c j
  · have hp : (∏ k ∈ J,
        MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k))) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      rw [hcut, ite_eq_left (hx.1.2 k)]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.1.1, hp, mul_one]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxK : x ∈ K
    · have hnot : ¬ ∀ k ∈ J, ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i := by
        intro hall
        apply hx
        apply (mem_commonFace_iff_of_tie K y c i j htie).2
        exact ⟨hxK, fun k hki hkj => hall k ((hJ k).2 ⟨hki, hkj⟩)⟩
      push Not at hnot
      obtain ⟨k, hk, hbad⟩ := hnot
      have hp : (∏ k ∈ J,
          MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k))) = 0 := by
        apply Finset.prod_eq_zero hk
        rw [hcut, ite_eq_right (not_le_of_gt hbad)]
      rw [hp, mul_zero]
    · rw [Set.indicator_of_notMem hxK, zero_mul]

/-- Translating a tangent vector preserves the affine equality. -/
theorem tie_on_tangent_chart (y : ι → E d) (c : ι → ℝ) (i j : ι)
    {z : E d} (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (w : (ℝ ∙ (y i - y j))ᗮ) :
    ⟪z + (w : E d), y i⟫ + c i = ⟪z + (w : E d), y j⟫ + c j := by
  have hw : ⟪y i - y j, (w : E d)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  have hw' : ⟪(w : E d), y i⟫ - ⟪(w : E d), y j⟫ = 0 := by
    rw [← inner_sub_right, real_inner_comm]
    exact hw
  simp only [inner_add_left]
  linarith

/-- The scalar face integral in a moving-cut formula is the canonical intrinsic
integral over the common cell face. No boundary or third-tie exception is needed
for this exact identification. -/
theorem interface_integral_eq_cut_trace {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) {i j : ι} (hy : y i ≠ y j)
    (J : Finset ι) (hJ : ∀ k, k ∈ J ↔ k ≠ i ∧ k ≠ j)
    (f : E d → ℝ) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j) :
    (∫ x in closedCell K y c i ∩ closedCell K y c j, f x
      ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)) =
      ∫ w : (ℝ ∙ (y i - y j))ᗮ,
        K.indicator f (z + (w : E d)) * ∏ k ∈ J,
          MovingCellTrace.cutIndicator
            (⟪z + (w : E d), y i - y k⟫ + (c i - c k)) := by
  classical
  rw [IntrinsicSurface.interfaceMeasure_setIntegral_of_tie hy
    (by simpa only [real_inner_comm] using htie)]
  have hmeas : MeasurableSet {w : (ℝ ∙ (y i - y j))ᗮ |
      z + (w : E d) ∈ closedCell K y c i ∩ closedCell K y c j} := by
    apply ((isClosed_closedCell hK y c i).inter
      (isClosed_closedCell hK y c j)).measurableSet.preimage
    fun_prop
  rw [← integral_indicator hmeas]
  apply integral_congr_ae
  filter_upwards [] with w
  have h := commonFace_indicator_eq_cut_product K y c i j J hJ f
    (tie_on_tangent_chart y c i j htie w)
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h

end Problem358.CellGeometry

/-! The actual moving-cut derivative expressed by canonical intrinsic faces. -/

namespace Problem358.PositiveCellFullDerivative

open CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cut derivative is intrinsically defined and independent of the chosen
tie-plane basepoint. This identity holds for every scalar weight. -/
theorem faceVariation_eq_intrinsic {K : Set (E d)} (hK : IsClosed K)
    (y v : ι → E d) (c r : ι → ℝ) (w : E d → ℝ)
    {i j : ι} (hy : y i ≠ y j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j) :
    faceVariation K y v c r w i j z =
      ∫ x in closedCell K y c i ∩ closedCell K y c j,
        ((r i - r j + ⟪v i - v j, x⟫) / ‖y i - y j‖) * w x
        ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j) := by
  rw [interface_integral_eq_cut_trace hK y c hy ((Finset.univ.erase i).erase j)
    (by intro k; simp only [Finset.mem_erase, Finset.mem_univ, and_true]; tauto)
    _ htie]
  unfold faceVariation
  apply integral_congr_ae
  filter_upwards [] with a
  have hscore (k : ι) :
      ⟪z + (a : E d), y i - y k⟫ + (c i - c k) =
        (⟪z + (a : E d), y i⟫ + c i) -
          (⟪z + (a : E d), y k⟫ + c k) := by
    rw [inner_sub_right]
    ring
  simp_rw [hscore]
  by_cases ha : z + (a : E d) ∈ K
  · simp only [Set.indicator_of_mem ha]
    ring
  · simp only [Set.indicator_of_notMem ha, zero_mul, mul_zero]

/-- The mass face contribution equals the scalar and first-moment coefficients
with the exact source-volume normalization. No positive-volume cancellation is
needed in this algebraic identity. -/
theorem normalized_faceVariation_one {K : Set (E d)} (hK : IsCompact K)
    (y v : ι → E d) (c r : ι → ℝ) {i j : ι} (hy : y i ≠ y j)
    {z : E d} (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j) :
    (volume K).toReal⁻¹ * faceVariation K y v c r (fun _ => 1) i j z =
      (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
        (closedCell K y c i ∩ closedCell K y c j)).toReal /
          ((volume K).toReal * ‖y i - y j‖) * (r i - r j) +
        ⟪faceMoment K y c i j, v i - v j⟫ := by
  let S := closedCell K y c i ∩ closedCell K y c j
  let μ := IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
  have hS : IsCompact S := (isCompact_closedCell hK y c i).inter
    (isCompact_closedCell hK y c j)
  have hid : IntegrableOn (fun x : E d => x) S μ :=
    IntrinsicSurface.integrableOn_interfaceMeasure _ _ _ _ hS continuous_id.continuousOn
  have hc : IntegrableOn (fun _ : E d => r i - r j) S μ :=
    IntrinsicSurface.integrableOn_interfaceMeasure _ _ _ _ hS continuous_const.continuousOn
  rw [faceVariation_eq_intrinsic hK.isClosed y v c r (fun _ => 1) hy htie]
  simp only [mul_one]
  change (volume K).toReal⁻¹ *
      (∫ x in S, (r i - r j + ⟪v i - v j, x⟫) / ‖y i - y j‖ ∂μ) = _
  rw [integral_div, integral_add hc (hid.const_inner (v i - v j)),
    integral_const, integral_inner hid]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  unfold faceMoment
  rw [inner_smul_left, real_inner_comm (v i - v j)]
  simp only [starRingEnd_apply, star_trivial]
  dsimp only [S, μ]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

end Problem358.PositiveCellFullDerivative

end

end OAI
