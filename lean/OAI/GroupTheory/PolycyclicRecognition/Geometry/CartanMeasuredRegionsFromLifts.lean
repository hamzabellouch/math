import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredRegionsFromCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredProbeRegions
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeRestrictionComposition

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

theorem measured_probe_regions_of_uniform_lifts
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
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (π : G →* Multiplicative W) (act : G →* Equiv.Perm Q.carrier)
    (cell : Set (F.N.carrier × F.D.carrier)) (E₁ E₂ : Set W)
    (μQ : Measure Q.carrier) (δ₀ : ℝ)
    (hdata : ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop →
        (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ (RQ : ℕ → Set Q.carrier) (S RD : ℕ → ℝ),
        (∀ n, μQ (RQ n) ≠ ⊤) ∧
        HasSubexponentialUpperBoundSeq scale (fun n => (μQ (RQ n)).toReal) ∧
        (∀ n, 0 ≤ S n) ∧ (∀ n, 0 ≤ RD n) ∧
        HasSubexponentialUpperBoundSeq scale S ∧ HasSubexponentialUpperBoundSeq scale RD ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, ∀ (base anchor first second : G)
          (path₁ : Path (1 : G) (base⁻¹ * first))
          (path₂ : Path (1 : G) (anchor⁻¹ * second)),
          PathMetricBound path₁ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          PathMetricBound path₂ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₁, ‖(π (path₁ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          (∀ t, ∃ w ∈ E₂, ‖(π (path₂ t)).toAdd - scale n • w‖ ≤
            2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
          ‖(π (anchor⁻¹ * second)).toAdd‖ ≤ δ * scale n →
          dist second first ≤ δ * scale n →
          ∃ (u : F.N.carrier) (d : F.D.carrier),
            F.inclusionN u * F.inclusionD d = anchor⁻¹ * first ∧
            ∀ z ∈ cell,
              act (base⁻¹ * (first * (F.inclusionN z.1 * F.inclusionD z.2))) 1 ∈ RQ n ∧
              (∃ (i : M.coneWordIdeal C)
                (q : (cartanRootIdeal H) ⧸ (M.coneWordIdeal C).toSubmodule),
                u * F.action d z.1 = F.ExpN (F.N.equiv (i : cartanRootIdeal H)) *
                  F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) bQ lift q)) ∧
                ‖(M.coneIdealBoxBasis C
                  s β (scale n)).equivFun i‖ ≤ S n) ∧
              ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
                hbijD (d * z.2))‖ ≤ RD n) :
    ∀ (scale η : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ R : MeasuredProbeRegions πQ μQ (Measure.map (kernelRealization πQ ιI hιI hrange) μI) ν scale (∑ j, M.coneIdealWordCost C s (β.val j)),
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell E₁ E₂ η A B δ n := by
  intro scale η hmono hscale hscale1 hη0 hη A B hA hB
  obtain ⟨RQ, S, RD, hRQ, hRQvol, hS0, hRD0, hS, hRD, hrestrict⟩ :=
    hdata scale η hmono hscale hscale1 hη0 hη A B hA hB
  obtain ⟨R, hRQeq, hcoord⟩ :=
    M.exists_measured_probe_regions_from_coordinates F C Q chartN hchartN chartQ πQ
      hπQ hzeroQ bQ lift hlift I ExpI hExpI haarI ιI hιI hrange hIExp μI ν haarD hbijD
      s β scale S RD hscale hS0 hRD0 hS hRD
      μQ RQ hRQ hRQvol
  refine ⟨R, ?_⟩
  intro δ hδ hδle
  filter_upwards [hrestrict δ hδ hδle] with n hn
  intro base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist
  exact map_cell_lift_conditions
    (hn base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist)
    (fun u d z _ hz => ⟨by simpa only [hRQeq] using hz.1,
      hcoord n (u * F.action d z.1) (d * z.2) hz.2.1 hz.2.2⟩)

end PolycyclicRecognition.CartanWordModel

end

end OAI
