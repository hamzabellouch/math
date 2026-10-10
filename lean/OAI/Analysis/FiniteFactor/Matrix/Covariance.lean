import OAI.Analysis.FiniteFactor.Matrix.Entries

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceCommutantRotation_basis (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    sourceCommutantRotation θ n (sourceBasis m) = sourceBasis (m+n) := by
  apply Lp.ext
  have hb := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae
    (sourceBasis_coe m)
  filter_upwards [sourceTransport_apply_ae θ n n (sourceBasis m), hb,
    sourceBasis_coe (m+n)] with z ht hb he
  change (sourceTransport θ n n (sourceBasis m)) z = _
  rw [ht, hb, he]
  simp only [sourceTransportIndex]
  simp only [sub_eq_iff_eq_add]

/-- Matrix form of H(sigma^r x) = S^(-r) H(x) S^r, for the original
regular representation and every integer power of the base rotation. -/
theorem sourceMatrixEntry_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (r n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  have he : H (sourceBasis (n+r)) = sourceCommutantRotation θ r (H (sourceBasis n)) := by
    rw [← sourceCommutantRotation_basis θ r n]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis n)) (sourceAlgebra_commutes_rotation θ hH r)).symm
  have ht := source_ae_all_fibers (sourceTransport_apply_ae θ r r (H (sourceBasis n)))
  filter_upwards [ht] with x hx k
  unfold sourceMatrixEntry
  rw [he]
  change _ = (sourceTransport θ r r (H (sourceBasis n))) (x,k+r)
  rw [hx]
  simp [sourceTransportIndex]

/-- All countably many covariance identities hold on one conull base set. -/
theorem sourceMatrixEntry_covariance_all (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  rw [ae_all_iff]
  intro r
  rw [ae_all_iff]
  exact sourceMatrixEntry_covariance θ hH r

/-- Matrix entries of the actual multiplication generators. -/
theorem sourceMatrixEntry_pi (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourcePi θ g) k n x =
        if k = n then g.toFun (coordinateRotate θ n x) else 0 := by
  filter_upwards [source_ae_all_fibers (sourcePi_apply_ae θ g (sourceBasis n)),
    source_ae_all_fibers (sourceBasis_coe n)] with x hp hb k
  unfold sourceMatrixEntry
  rw [hp, hb]
  by_cases hk : k = n <;> simp [hk, sourcePiSymbol]

/-- Matrix entries of the original fiber shift. -/
theorem sourceMatrixEntry_shift (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourceShift SourceCoordinate) k n x =
        if k = n+1 then 1 else 0 := by
  have hb := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourceBasis_coe n)
  filter_upwards [source_ae_all_fibers (sourceShift_apply_ae (sourceBasis n)),
    source_ae_all_fibers hb] with x hs hb k
  unfold sourceMatrixEntry
  rw [hs, hb]
  simp only [sourceShiftIndex]
  simp only [sub_eq_iff_eq_add]

end
end FiniteFactor

end OAI
