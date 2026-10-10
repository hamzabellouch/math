import OAI.Combinatorics.Progressions.Estimates.PreparedShortLateFloorCertifiedBadProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

private theorem lateTolerance_base_bounds {Bstruct Pscale pRadius : ℝ}
    (hBstruct : 0 ≤ Bstruct) (hPscale : 0 ≤ Pscale) (hpRadius : 0 ≤ pRadius) :
    0 ≤ Bstruct + Pscale + pRadius ∧
      Bstruct ≤ Bstruct + Pscale + pRadius ∧
      pRadius ≤ Bstruct + Pscale + pRadius ∧
      Pscale ≤ Bstruct + Pscale + pRadius := by
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

private theorem lateTolerance_larger_bounds
    {Bstruct pRadius Pscale Pseed Qw Pmin Elog Vlog Bcert : ℝ}
    (hBstruct : 0 ≤ Bstruct) (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hcert : 1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + Elog + Vlog ≤ Bcert) :
    1 ≤ Bcert ∧ Bstruct ≤ Bcert ∧ pRadius ≤ Bcert ∧ Pscale ≤ Bcert ∧
      Elog ≤ Bcert ∧ Vlog ≤ Bcert ∧ Pseed + Pmin ≤ Bcert ∧ Qw ≤ Bcert := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedShortCertifiedSameScaleBadProductInterface_of_lateTolerance
    {Bstruct pRadius Pscale Pseed Qw Pmin Elog Vlog : ℝ} (Q : ℕ)
    (hBstruct : 0 ≤ Bstruct) (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hM : (M : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedShortCertifiedSameScaleBadProductInterface prep U b S
      (1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + Elog + Vlog) Elog Vlog Q := by
  obtain ⟨hbase, hstruct, hradius, hscale⟩ := lateTolerance_base_bounds hBstruct hPscale hpRadius
  exact preparedShortCertifiedSameScaleBadProductInterface_of_late_parameters
    (nX := nX) (M := M) prep U b S
    (Pbase := Bstruct + Pscale + pRadius) (Elog := Elog) (Vlog := Vlog)
    (Pseed := Pseed) (Qw := Qw) (Pmin := Pmin) Q
    hbase (hM.trans hstruct) (hnX.trans hstruct) hElog hVlog hQ hQexp hmpos hCoord
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hradius))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hscale))
    hPseed hQw hPmin hS hprincipal

theorem preparedShortCertifiedSameScaleBadProductInterface_of_lateTolerance_larger
    {Bstruct pRadius Pscale Pseed Qw Pmin Elog Vlog : ℝ} (Q : ℕ)
    (hBstruct : 0 ≤ Bstruct) (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hM : (M : ℝ) ≤ Bstruct) (hnX : (nX : ℝ) ≤ Bstruct)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hS : (S.value : ℝ) ≤ Real.exp
      (allocatedWitnessScaleLog Pseed Qw + (1 + Pseed ^ 2) * Pmin))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    ∀ Bcert : ℝ,
      1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + Elog + Vlog ≤ Bcert →
      PreparedShortCertifiedSameScaleBadProductInterface prep U b S Bcert Elog Vlog Q := by
  intro Bcert hcert
  obtain ⟨hB, hstruct, hradius, hscale, hEB, hVB, hseedFloor, hQwB⟩ :=
    lateTolerance_larger_bounds hBstruct hpRadius hPscale hPseed hQw hPmin hElog hVlog hcert
  exact preparedShortCertifiedSameScaleBadProductInterface_of_lateFloor
    (nX := nX) (M := M) prep U b S
    (B0 := Bcert) (Elog := Elog) (Vlog := Vlog)
    (Pseed := Pseed) (Qw := Qw) (Pmin := Pmin) Q
    hB (hM.trans hstruct) (hnX.trans hstruct) ⟨hElog, hEB⟩ ⟨hVlog, hVB⟩
    hQ hQexp hmpos hCoord
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hradius))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hscale))
    hPseed hQw hPmin hseedFloor hQwB hS hprincipal

end Erdos3.VectorPolynomial

end

end OAI
