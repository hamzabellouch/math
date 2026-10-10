import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDerivativeBounds

namespace OAI

/-! # Continuity of the actual polynomial at a varying torus scale

The coefficient-preserving identification intertwines the exact Fourier
products and conjugation.  Thus the varying-scale nonlinearity is conjugate
to the already smooth radius-one polynomial.
-/

open scoped ComplexConjugate

namespace DefocusingNLS

private theorem coefficient_injective (a k L : ℝ) (hL : 1 ≤ L) :
    Function.Injective (expandingFourierCoefficient a k L) := by
  intro f g h
  ext n
  simpa only [weight_mul_expandingFourierCoefficient a k L hL] using
    congrArg (fun z : ℂ => (expandingSobolevWeight a k L n : ℂ) * z) (congrFun h n)

theorem expandingScaleTransfer_product (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) :
    expandingScaleTransfer a k 1 L ha hk le_rfl hL
        (expandingProduct a k 1 ha ha1 hk le_rfl f g) =
      expandingProduct a k L ha ha1 hk hL
        (expandingScaleTransfer a k 1 L ha hk le_rfl hL f)
        (expandingScaleTransfer a k 1 L ha hk le_rfl hL g) := by
  apply coefficient_injective a k L hL
  funext n
  rw [expandingScaleTransfer_coefficient, expandingProduct_coefficient,
    expandingProduct_coefficient]
  unfold expandingProductCoefficient
  apply tsum_congr
  intro j
  rw [expandingScaleTransfer_coefficient, expandingScaleTransfer_coefficient]

theorem expandingScaleTransfer_conjugate (a k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    expandingScaleTransfer a k 1 L ha hk le_rfl hL (fourierConjugate f) =
      fourierConjugate (expandingScaleTransfer a k 1 L ha hk le_rfl hL f) := by
  apply coefficient_injective a k L hL
  funext n
  rw [expandingScaleTransfer_coefficient, expandingFourierCoefficient_conjugate,
    expandingFourierCoefficient_conjugate, expandingScaleTransfer_coefficient]

theorem expandingScaleTransfer_oddPower (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (f : FourierL2) :
    expandingScaleTransfer a k 1 L ha hk le_rfl hL
        (expandingOddPower a k 1 ha ha1 hk le_rfl m f) =
      expandingOddPower a k L ha ha1 hk hL m
        (expandingScaleTransfer a k 1 L ha hk le_rfl hL f) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [expandingOddPower, expandingScaleTransfer_product,
        expandingScaleTransfer_conjugate, ih]

private theorem transfer_inverse_apply (a k L : ℝ) (ha : 0 < a) (hk : 8 < k)
    (hL : 1 ≤ L) (f : FourierL2) :
    expandingScaleTransfer a k 1 L ha hk le_rfl hL
      (expandingInverseTransfer a k L ha hk hL f) = f := by
  have h := (expandingWeightUnit a k L ha hk hL).val_inv
  exact congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A f) h

/-- Exact conjugation of the actual polynomial by the weight identification. -/
theorem expandingOddPower_transport (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (f : FourierL2) :
    expandingOddPower a k L ha ha1 hk hL m f =
      expandingScaleTransfer a k 1 L ha hk le_rfl hL
        (expandingOddPower a k 1 ha ha1 hk le_rfl m
          (expandingInverseTransfer a k L ha hk hL f)) := by
  rw [expandingScaleTransfer_oddPower, transfer_inverse_apply]

/-- The polynomial is jointly continuous in scale and input in the exact norms. -/
theorem continuous_expandingOddPower_scale (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) :
    Continuous (fun p : {L : ℝ // 1 ≤ L} × FourierL2 =>
      expandingOddPower a k p.1.1 ha ha1 hk p.1.2 m p.2) := by
  have heq : (fun p : {L : ℝ // 1 ≤ L} × FourierL2 =>
      expandingOddPower a k p.1.1 ha ha1 hk p.1.2 m p.2) =
      (fun p => expandingScaleTransfer a k 1 p.1.1 ha hk le_rfl p.1.2
        (expandingOddPower a k 1 ha ha1 hk le_rfl m
          (expandingInverseTransfer a k p.1.1 ha hk p.1.2 p.2))) :=
    funext (fun p => expandingOddPower_transport a k p.1.1 ha ha1 hk p.1.2 m p.2)
  rw [heq]
  exact ((continuous_expandingScaleTransfer_from_one a k ha hk).comp continuous_fst).clm_apply
    ((contDiff_expandingOddPower a k 1 ha ha1 hk le_rfl m).continuous.comp
      (((continuous_expandingInverseTransfer a k ha hk).comp continuous_fst).clm_apply
        continuous_snd))

/-- The linearization is the derivative of the same conjugated polynomial. -/
theorem fderiv_expandingOddPower_transport (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (q v : FourierL2) :
    fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q v =
      expandingScaleTransfer a k 1 L ha hk le_rfl hL
        (fderiv ℝ (expandingOddPower a k 1 ha ha1 hk le_rfl m)
          (expandingInverseTransfer a k L ha hk hL q)
          (expandingInverseTransfer a k L ha hk hL v)) := by
  let T := (expandingScaleTransfer a k 1 L ha hk le_rfl hL).restrictScalars ℝ
  let S := (expandingInverseTransfer a k L ha hk hL).restrictScalars ℝ
  have hN := (contDiff_expandingOddPower a k 1 ha ha1 hk le_rfl m).differentiable
    (by simp) (S q)
  have h := T.hasFDerivAt.comp q (hN.hasFDerivAt.comp q S.hasFDerivAt)
  have heq : (fun x => T (expandingOddPower a k 1 ha ha1 hk le_rfl m (S x))) =
      expandingOddPower a k L ha ha1 hk hL m := by
    funext x
    exact (expandingOddPower_transport a k L ha ha1 hk hL m x).symm
  simp only [Function.comp_def] at h
  rw [heq] at h
  exact congrArg (fun A : FourierL2 →L[ℝ] FourierL2 => A v) h.fderiv

/-- Joint strong continuity of the actual linearized potential in scale, profile and input. -/
theorem continuous_expandingLinearization_scale (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) :
    Continuous (fun p : {L : ℝ // 1 ≤ L} × (FourierL2 × FourierL2) =>
      fderiv ℝ (expandingOddPower a k p.1.1 ha ha1 hk p.1.2 m) p.2.1 p.2.2) := by
  have heq : (fun p : {L : ℝ // 1 ≤ L} × (FourierL2 × FourierL2) =>
      fderiv ℝ (expandingOddPower a k p.1.1 ha ha1 hk p.1.2 m) p.2.1 p.2.2) =
      (fun p => expandingScaleTransfer a k 1 p.1.1 ha hk le_rfl p.1.2
        (fderiv ℝ (expandingOddPower a k 1 ha ha1 hk le_rfl m)
          (expandingInverseTransfer a k p.1.1 ha hk p.1.2 p.2.1)
          (expandingInverseTransfer a k p.1.1 ha hk p.1.2 p.2.2))) :=
    funext (fun p => fderiv_expandingOddPower_transport a k p.1.1 ha ha1 hk p.1.2 m p.2.1 p.2.2)
  rw [heq]
  have hT := (continuous_expandingScaleTransfer_from_one a k ha hk).comp
    (continuous_fst : Continuous (fun p : {L : ℝ // 1 ≤ L} × (FourierL2 × FourierL2) => p.1))
  have hS := (continuous_expandingInverseTransfer a k ha hk).comp
    (continuous_fst : Continuous (fun p : {L : ℝ // 1 ≤ L} × (FourierL2 × FourierL2) => p.1))
  exact hT.clm_apply
    ((((contDiff_expandingOddPower a k 1 ha ha1 hk le_rfl m).continuous_fderiv
      (by simp)).comp (hS.clm_apply (continuous_fst.comp continuous_snd))).clm_apply
        (hS.clm_apply (continuous_snd.comp continuous_snd)))

end DefocusingNLS

end OAI
