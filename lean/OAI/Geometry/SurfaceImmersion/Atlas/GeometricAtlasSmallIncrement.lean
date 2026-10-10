import OAI.Geometry.SurfaceImmersion.Atlas.FixedAtlasSmallIncrement
import OAI.Geometry.SurfaceImmersion.Correction.GeometricAtlasAdjustedMean

namespace OAI

/-! The finite mean iteration supplies the actual unperturbed small increment. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance geometricSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance geometricSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance geometricSmallDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance geometricSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance geometricSmallSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance geometricSmallSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem geometric_atlas_small_increment
    {n : A.centers → ℕ} {P : (k : A.centers) → Fin 3 → Fin (n k) → JetPolynomial.Expression}
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (d₀ : ∀ i, ChartedMeanFamilyData (P i) 0 1 1 r₁ ρ R (A.tensorPlaneRead i reference))
    (hG₀ : ∀ i, (d₀ i).G = A.jetChartMap i F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase₀ : ∀ i j, coordinatePhase ((d₀ i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hcut₀ : ∀ i j x, x ∈ ((d₀ i).solver j).e.source →
      ((d₀ i).data j).cutoff (((d₀ i).solver j).e x) = A.planeWeight i x / w i j)
    (hform₀ : ∀ i j x, x ∈ ((d₀ i).solver j).e.source →
      ((d₀ i).data j).form (((d₀ i).solver j).e x) = (Q i).Q j)
    (hsup₀ : ∀ i j, tsupport (A.planeWeight i) ⊆ ((d₀ i).solver j).e.source)
    (hK₀ : ∀ i j, (modeSupport ((d₀ i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (c₀ : ∀ k l, PolynomialSolveData (P k) 0 (A.jetChartMap k F)
      (A.jetChartMap_smooth k hF)
      (A.globalQuadraticPhase (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) 1 1)
    (I : A.centers → RealModes.QuadraticLabel (A.centers × Fin 3) → ℕ → ℝ)
    (hI : ∀ k l m, 1 ≤ I k l m)
    (hi : ∀ k l m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c₀ k l).e.target,
      ‖iteratedFDerivWithin ℝ j (c₀ k l).e.symm (c₀ k l).e.target x‖ ≤ I k l m)
    (q : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) → (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ ∃ B T : ℕ → ℝ,
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
        ∀ τ δ : ℝ, 0 < τ → τ ≤ s → τ/s ≤ η₀ → 0 < δ → δ ≤ τ →
        ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
          (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
          (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
            (inducedTensor (F+X) - inducedTensor F - δ^2 • H)) := by
  obtain ⟨r,D₀,hr,hD₀,p,β,κ,hmean⟩ := A.geometric_atlas_adjusted_mean
    (fun i j => (d₀ i).solver j) hr₁ hρ reference href (fun i j => (d₀ i).data j)
    Q w hw hphase₀ hcut₀ hform₀ hsup₀ q
  refine ⟨r,hr,?_⟩
  intro s hs hs1 H hH hsym hnear C hC hbC
  let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
  let Cu := fun m => max 1 (sizeBound L C β q m)
  let E := fun m => max 1 (differenceBound L C β κ q m)
  have hCu (m) : 0 ≤ Cu m := zero_le_one.trans (le_max_left _ _)
  have hE (m) : 0 ≤ E m := zero_le_one.trans (le_max_left _ _)
  obtain ⟨B,T,hB,hT,hsmall⟩ := A.fixed_atlas_small_increment F hF p hρ
    (fun _ => D₀*r) (fun _ => r₁) (fun i => A.tensorPlaneRead i reference)
    d₀ c₀ I hI hi Cu E hCu hE q
  obtain ⟨η₀,hη₀,hη₁,hbuild⟩ := hmean s hs hs1 H hH hsym hnear C hC hbC q
  refine ⟨η₀,hη₀,hη₁,B,T,hB,hT,?_⟩
  intro τ δ hτ hτs hη hδ hδτ
  obtain ⟨d,hfit,hgeom,htrial⟩ := hbuild 0 τ hτ hτs (le_refl 0) (by norm_num)
    (by simpa only [zero_div,add_zero] using hη)
  obtain ⟨u,hu,_,_,hball,hsize,herror⟩ := htrial δ hδ q le_rfl
  have hK (i j) : (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    rw [(hgeom i).2.2]
    exact hK₀ i j
  have hbu (m) : A.TensorWeightedBound s m (Cu m) u :=
    fun k => (hsize m k).mono_const (le_max_right _ _)
  have hmu (m) : A.TensorWeightedBound τ m (E m*δ^2*(τ/s)^(q+1))
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) := by
    intro k
    have hh := (herror m k).shrink_scale hτ.le hτs
    simp only [zero_div,add_zero] at hh
    apply hh.mono_const
    calc
      δ^2*(differenceBound L C β κ q m*(τ/s)^(q+1)) ≤
          δ^2*(E m*(τ/s)^(q+1)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (div_nonneg hτ.le hs.le) _)) (sq_nonneg δ)
      _ = _ := by ring
  exact hsmall d hfit (fun i => (hgeom i).2.1)
    (fun i => (hgeom i).1.trans (hG₀ i)) hτ hs hτs hs1 hK δ hδ.le hδτ u H hu hH hball hbu hmu

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
