import OAI.Geometry.SurfaceImmersion.Correction.InputPolynomialSmallIncrement
import OAI.Geometry.SurfaceImmersion.Correction.ProfiledAtlasAdjustedMean

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance profiledPolynomialSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance profiledPolynomialSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance profiledPolynomialSmallDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance profiledPolynomialSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance profiledPolynomialSmallSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledPolynomialSmallSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem profiled_polynomial_atlas_small_increment
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (P : A.centers → Fin 3 → Fin nq → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol P)
    (hlin : A.PolynomialLinearRepresentation Pol P)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i))
    (d₀ : ∀ i, ChartedMeanFamilyData (P i) 0 1 1 r₁ ρ R (A.tensorPlaneRead i reference))
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase₀ : ∀ i j, coordinatePhase ((d₀ i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)) x))
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) :
    ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧ D₀*r ≤ r₁ ∧
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (D m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η₀ → 0 < δ → δ ≤ τ →
      ∀ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
        (∀ i, (d i).Fits (p i)) →
        (∀ i, (d i).phase = (d₀ i).phase) →
        (∀ i, (d i).G = A.jetChartMap i G) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) →
        (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) →
        (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
          (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
            (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))))^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  obtain ⟨r,D₀,hr,hD₀,hDr,β,κ,hmean⟩ := A.profiled_atlas_adjusted_mean
    p hr₁ hρ reference href Q w hw q
  refine ⟨r,D₀,hr,hD₀,hDr,?_⟩
  intro C hC
  let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
  let Cu := fun m => max 1 (sizeBound L C β q m)
  let E := fun m => max 1 (differenceBound L C β κ q m)
  have hCu (m) : 0 ≤ Cu m := zero_le_one.trans (le_max_left _ _)
  have hE (m) : 0 ≤ E m := zero_le_one.trans (le_max_left _ _)
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_polynomial_small_increment_fixed_phase Pol hPol P hP hquad hlin F hF
    (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2)
    (fun a => A.freeGlobalPhase_smooth d₀ a.1 a.2) hImm hgood Ω hΩ KΩ hΩK hweight houter
  obtain ⟨B,T,hB,hT,hsmall⟩ := hall p hρ (fun _ => D₀*r)
    (fun i => A.tensorPlaneRead i reference) D hD Cu E hCu hE q
  obtain ⟨η₀,hη₀,hη₁,hmeanUniform⟩ := hmean C hC q
  refine ⟨ρ₀,η₀,B,T,hρ₀,hη₀,hη₁,hB,hT,?_⟩
  intro G hG b hb hbρ hclose s hs hs1 hd H hH hsym hnear hbC τ δ ε hτ hτs hε hε1 hη hδ hδτ d hfit hphase hmap hcut hform hsup hK
  have hbuild := hmeanUniform s hs hs1 H hH hsym hnear hbC
  have hphase' (i j) : coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j) := by
    rw [hphase i]
    exact hphase₀ i j
  let lossP := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
  let loss := max lossP (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))
  let η := τ/s+ε/τ^loss
  have hηP : τ/s+ε/τ^lossP ≤ η := by
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    exact pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (le_max_left _ _)
  have hη0 : 0 ≤ η := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hηP0 : 0 ≤ τ/s+ε/τ^lossP := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  obtain ⟨u,hu,_,_,hball,hsize,herror⟩ := hbuild ε τ hτ hτs hε hε1 (hηP.trans hη)
    d hfit hphase' hcut hform hsup δ hδ q le_rfl
  have hbu (m) : A.TensorWeightedBound s m (Cu m) u :=
    fun k => (hsize m k).mono_const (le_max_right _ _)
  have hmu (m) : A.TensorWeightedBound τ m (E m*δ^2*η^(q+1))
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) := by
    intro k
    have hh := (herror m k).shrink_scale hτ.le hτs
    apply hh.mono_const
    have hp := pow_le_pow_left₀ hηP0 hηP (q+1)
    calc
      δ^2*(differenceBound L C β κ q m*(τ/s+ε/τ^lossP)^(q+1)) ≤
          δ^2*(E m*η^(q+1)) := mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hηP0 _)).trans
              (mul_le_mul_of_nonneg_left hp (hE m))) (sq_nonneg δ)
      _ = _ := by ring
  apply hsmall G hG b hb hbρ hclose d hfit _ hmap hτ hs hτs hs1 hε hε1 η hη0 (hη.trans hη₁)
    le_rfl hd hK δ hδ hδτ u H hu hH hball hbu hmu
  intro a
  unfold freeGlobalPhase
  rw [hphase a.1]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
