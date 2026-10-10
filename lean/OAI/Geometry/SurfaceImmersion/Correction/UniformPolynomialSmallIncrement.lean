import OAI.Geometry.SurfaceImmersion.Correction.ProfiledPolynomialSmallIncrement
import OAI.Geometry.SurfaceImmersion.Correction.UniformPolynomialAtlasMeanData
import OAI.Geometry.SurfaceImmersion.Atlas.UniformNearbyAtlasSmallIncrement

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance uniformPolynomialSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformPolynomialSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformPolynomialSmallDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformPolynomialSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformPolynomialSmallSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformPolynomialSmallSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_polynomial_atlas_small_increment
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (Ql : A.centers → Fin 3 → Fin nq → Expression)
    (hQl : ∀ i k l, (Ql i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Ql)
    (hlin : A.PolynomialLinearRepresentation Pol Ql)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (Ω U K : A.centers → Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ i j, IsOpen (Ω i j)) (hU : ∀ i j, IsOpen (U i j))
    (hK : ∀ i j, IsCompact (K i j))
    (hUK : ∀ i j, U i j ⊆ K i j) (hKΩ : ∀ i j, K i j ⊆ Ω i j)
    (hImm : ∀ i j x, x ∈ Ω i j → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ Ω i j →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (hsupport : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j)
    (U₀ : A.centers → Set JetPolynomial.Base) (hU₀ : ∀ i, IsOpen (U₀ i))
    (K₀ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hU₀K : ∀ i, U₀ i ⊆ K₀ i)
    (hSU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (hmargin : ∀ i j x, x ∈ U i j →
      ρ + ‖(Q i).Q j‖*r₁ ≤ (Q i).Q j (A.tensorPlaneRead i reference x) ∧
      (Q i).Q j (A.tensorPlaneRead i reference x) ≤ R - ‖(Q i).Q j‖*r₁)
    (hImmQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgoodQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x))
    (Ωp : A.centers → Set JetPolynomial.Base) (hΩp : ∀ i, IsOpen (Ωp i))
    (KΩp : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩpK : ∀ i, Ωp i ⊆ KΩp i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ωp i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ωp i)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (hPF : ∀ m, A.ShiftedBound 2 m 1 (P m) F) (q : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Ql i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η₀ → 0 < δ → δ ≤ τ →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Ql i)))
            (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))))^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  classical
  obtain ⟨ρd,hρd,halldata⟩ := A.uniform_polynomial_atlas_phase_mean_data_all_profiles Ql hQl F hF Q w hw Ω U K
    hΩ hU hK hUK hKΩ hImm hgood hsupport U₀ hU₀ K₀ hU₀K hSU₀
    (fun i => A.tensorPlaneRead i reference) hmargin
  obtain ⟨p,hdata⟩ := halldata P hP
  have hzero : A.WeightedBound 1 2 0 (F-F) := by
    simp only [sub_self]
    intro i
    have he : localize (i : M) (A.weight i) (0 : M → Space) =
        (fun _ : JetPolynomial.Base => (0 : Space)) := by
      funext x
      simp [localize]
    rw [he]
    exact weightedBound_zero (univ : Set JetPolynomial.Base) 1 2
  obtain ⟨d₀,_,_,hphase₀,_,hlinear₀,_,_,_⟩ := hdata F hF 0 le_rfl hρd hzero
    1 zero_lt_one le_rfl hPF 1 0 r₁ le_rfl zero_lt_one le_rfl le_rfl zero_le_one
  have hφ₀ : (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) =
      A.linearAtlasPhase Q w := by
    funext a
    unfold freeGlobalPhase linearAtlasPhase
    rw [hphase₀ a.1]
  have hgoodQ' : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)) x) := by
    simpa only [hφ₀] using hgoodQ
  obtain ⟨r,D₀,hr,hD₀,hDr,hsmall⟩ := A.profiled_polynomial_atlas_small_increment Pol hPol Ql hQl hquad hlin
    F hF hr₁ hρ reference href p d₀ Q w hw hlinear₀ hImmQ hgoodQ' Ωp hΩp KΩp hΩpK hweight houter P hP q
  refine ⟨r,hr,?_⟩
  intro C hC
  obtain ⟨ρs,η₀,B,T,hρs,hη₀,hη₁,hB,hT,hstep⟩ := hsmall C hC
  refine ⟨min ρd ρs,η₀,B,T,lt_min hρd hρs,hη₀,hη₁,hB,hT,?_⟩
  intro G hG b hb hbr hclose s hs hs1 hp H hH hsym hnear hHC τ δ ε hτ hτs hε hε1 hη hδ hδτ
  have hrealize := hstep G hG b hb (hbr.trans_le (min_le_right _ _)) hclose
    s hs hs1 hp H hH hsym hnear hHC
  obtain ⟨d,hfit,hmap,hphase,hsupport',_,hcut,hform,hsup⟩ :=
    hdata G hG b hb (hbr.trans_le (min_le_left _ _)) hclose s hs hs1 hp τ ε (D₀*r) hDr hτ hτs hε hε1
  have hph (i) : (d i).phase = (d₀ i).phase := (hphase i).trans (hphase₀ i).symm
  have hK' (i j) : (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    rw [hsupport' i]
  exact hrealize τ δ ε hτ hτs hε hε1 hη hδ hδτ d hfit hph hmap hcut hform hsup hK'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
