import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeCoordinateRegions
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredProbeRegions

namespace OAI

/-! # Measured ideal and Cartan regions for fixed exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

theorem exists_measured_probe_regions_from_coordinates
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v)))
    (hzeroQ : chartQ (Q.equiv 0) = 1)
    (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
      ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
    (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
      cartanRootIdeal H)
    (hlift : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ιI : I.carrier →* F.N.carrier) (hιI : Topology.IsClosedEmbedding ιI)
    (hrange : range ιI = (πQ.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ιI (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (hbijD : Function.Bijective F.ExpD)
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (scale S RD : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hS0 : ∀ n, 0 ≤ S n) (hRD0 : ∀ n, 0 ≤ RD n)
    (hS : HasSubexponentialUpperBoundSeq scale S)
    (hRD : HasSubexponentialUpperBoundSeq scale RD)
    (μQ : Measure Q.carrier) (RQ : ℕ → Set Q.carrier)
    (hRQ : ∀ n, μQ (RQ n) ≠ ⊤)
    (hRQvol : HasSubexponentialUpperBoundSeq scale (fun n => (μQ (RQ n)).toReal)) :
    let μK := Measure.map (kernelRealization πQ ιI hιI hrange) μI
    let P := ∑ j, M.coneIdealWordCost C s (β.val j)
    ∃ R : MeasuredProbeRegions πQ μQ μK ν scale P,
      R.quotientRegion = RQ ∧ ∀ n u d,
        (∃ (i : M.coneWordIdeal C) (q : cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule),
          u = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
          ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD n →
        quotientSectionResidual πQ R.sectionMap R.section_rightInverse u ∈ R.idealRegion n ∧
          d ∈ R.cartanRegion n := by
  dsimp only
  have hregions := M.exists_ideal_cartan_probe_regions F C Q chartN hchartN chartQ πQ
    hπQ hzeroQ bQ lift hlift I ExpI hExpI haarI ιI hιI hrange hIExp μI ν haarD hbijD
    s β scale S RD hscale hS0 hRD0 hS hRD
  let σ := Classical.choose hregions
  have hr₁ := Classical.choose_spec hregions
  let hσ := Classical.choose hr₁
  have hr₂ := Classical.choose_spec hr₁
  let RI := Classical.choose hr₂
  have hr₃ := Classical.choose_spec hr₂
  let BD := Classical.choose hr₃
  have hr₄ := Classical.choose_spec hr₃
  let V := Classical.choose hr₄
  have hregion := Classical.choose_spec hr₄
  have hfinite := hregion.1
  have hV := hregion.2.1
  have hV0 := hregion.2.2.1
  have hDvol := hregion.2.2.2.1
  have hIvol := hregion.2.2.2.2.1
  have hcoord := hregion.2.2.2.2.2
  let R : MeasuredProbeRegions πQ μQ
      (Measure.map (kernelRealization πQ ιI hιI hrange) μI) ν scale
      (∑ j, M.coneIdealWordCost C s (β.val j)) :=
    { sectionMap := σ
      section_rightInverse := hσ
      quotientRegion := RQ
      idealRegion := RI
      cartanRegion := BD
      idealLoss := V
      quotient_finite := hRQ
      ideal_finite := fun n => (hfinite n).1
      cartan_finite := fun n => (hfinite n).2
      quotient_subexponential := hRQvol
      ideal_subexponential := hV
      idealLoss_nonneg := hV0
      cartan_subexponential := hDvol
      ideal_volume := hIvol }
  exact ⟨R, rfl, hcoord⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
