import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorLogVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanKernelRegionVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealBoxCalculus
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel

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

theorem exists_ideal_cartan_probe_regions
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
    (hRD : HasSubexponentialUpperBoundSeq scale RD) :
    let μK := Measure.map (kernelRealization πQ ιI hιI hrange) μI
    ∃ (σ : C(Q.carrier, F.N.carrier)) (hσ : ∀ q, πQ (σ q) = q)
      (RI : ℕ → Set πQ.ker) (BD : ℕ → Set F.D.carrier) (V : ℕ → ℝ),
      (∀ n, μK (RI n) ≠ ⊤ ∧ ν (BD n) ≠ ⊤) ∧
      HasSubexponentialUpperBoundSeq scale V ∧ (∀ n, 0 ≤ V n) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => (ν (BD n)).toReal) ∧
      (∀ n, (μK (RI n)).toReal = V n *
        Real.exp ((∑ j, M.coneIdealWordCost C s (β.val j)) * scale n)) ∧
      ∀ n u d,
        (∃ (i : M.coneWordIdeal C) (q : cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule),
          u = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
            F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
          ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n) →
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD n →
        quotientSectionResidual πQ σ hσ u ∈ RI n ∧ d ∈ BD n := by
  dsimp only
  let RI := fun n => exponentialIdealKernelRegion (M.coneWordIdeal C) πQ
    (F.ExpN ∘ F.N.equiv) {i | ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n}
  let BD := fun n => {d : F.D.carrier |
    ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD d)‖ ≤ RD n}
  obtain ⟨V, hV0, hV, hIvol⟩ := M.exists_cone_kernel_box_volumes F C πQ
    I ExpI hExpI haarI ιI hιI hrange hIExp μI s β scale S hscale hS0 hS
  have hBDvol := F.log_regions_volume haarD hbijD ν scale RD hscale hRD0 hRD
  have hBD := hBDvol.1
  have hDvol := hBDvol.2
  let σ := exponentialQuotientSection (M.coneWordIdeal C) bQ lift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ
  have hσ : ∀ q, πQ (σ q) = q :=
    exponentialQuotientSection_rightInverse (M.coneWordIdeal C) bQ lift hlift
      F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ πQ hπQ
  refine ⟨σ, hσ, RI, BD, V, fun n => ⟨(hIvol n).1, hBD n⟩,
    hV, hV0, hDvol, fun n => (hIvol n).2, ?_⟩
  rintro n u d ⟨i, q, he, hi⟩ hd
  refine ⟨?_, hd⟩
  have he' : u = chartN (F.N.equiv (i : cartanRootIdeal H)) *
      chartN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) := by
    simpa only [hchartN] using he
  have hr := exponential_section_residual_mem (M.coneWordIdeal C) bQ lift hlift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ πQ hπQ hzeroQ
    {i : M.coneWordIdeal C | ‖(M.coneIdealBoxBasis C s β (scale n)).equivFun i‖ ≤ S n}
    ⟨i, hi, q, he'⟩
  simpa only [RI, σ, Function.comp_def, hchartN, LieEquiv.coe_toLinearEquiv] using hr

end PolycyclicRecognition.CartanWordModel

end

end OAI
