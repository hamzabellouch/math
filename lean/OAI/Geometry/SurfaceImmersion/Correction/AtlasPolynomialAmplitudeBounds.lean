import OAI.Geometry.SurfaceImmersion.Correction.AtlasGlobalFreeModes
import OAI.Geometry.SurfaceImmersion.Atlas.ChartedUniformSeed
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds

namespace OAI

/-! Uniform slow-scale bounds on every chart reading of the actual complex amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance ampReadPolynomialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance ampReadPolynomialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance ampReadPolynomialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance ampReadPolynomialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance ampReadPolynomialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance ampReadPolynomialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_polynomial_atlas_amplitude_reads
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
    (q m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → (∀ i, τ/s+ε/τ^tensorLoss (P i) ≤ 1) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      A.TensorWeightedBound s N C u →
      ∀ k i j, WeightedEstimates.WeightedBound univ s m (B*(δ*τ))
        (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u i j)) := by
  classical
  dsimp only
  let N := Finset.univ.sup (fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m)
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i
    (PolynomialSolveData.inputOrder (P := P i) q m)
  let C' := fun i => max 1 (D i*C)
  choose B hB hb using fun (i : A.centers) (j : Fin 3) =>
    uniform_charted_seed_bound (R := R) (p i j) hρ q m (C' i)
  choose E hE he using fun k i : A.centers =>
    A.localize_outer_restore_bound (V := Fin 4 → ℂ) k i m
  let Q := fun a : A.centers × A.centers × Fin 3 => E a.1 a.2.1 * B a.2.1 a.2.2
  have hQ (a) : 0 ≤ Q a := mul_nonneg (hE a.1 a.2.1) (zero_le_one.trans (hB a.2.1 a.2.2))
  have htotal : 0 ≤ ∑ a, Q a := Finset.sum_nonneg (fun a _ => hQ a)
  refine ⟨1+∑ a, Q a,by linarith,?_⟩
  intro ε τ s d hd hτ hs hτs hs1 hε hsmall δ hδ u hu hball hbu k i j
  have horder : PolynomialSolveData.inputOrder (P := P i) q m ≤ N := Finset.le_sup
    (f := fun i : A.centers => PolynomialSolveData.inputOrder (P := P i) q m) (Finset.mem_univ i)
  have hlocal := (hread i u s C hs hs1 hC hu (fun k => (hbu k).mono_order horder)).mono_const
    (le_max_right 1 (D i*C))
  have hseed := hb i j ((d i).data j) (hd i j) hτ hs hτs hs1 hε (hsmall i) δ hδ
    (A.tensorPlaneRead i u) (zero_le_one.trans (le_max_left _ _))
    (A.tensorPlaneRead_smooth i hu) (hball i) hlocal
  have hout := he k i ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u)) s
    (B i j*(δ*τ)) hs hs1 (mul_nonneg (zero_le_one.trans (hB i j)) (mul_nonneg hδ hτ.le))
    (((d i).data j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)).contDiff hseed
  have hplane := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth k (A.freeGlobalAmplitude_smooth d hρ δ q u i j)) hout
  change WeightedEstimates.WeightedBound univ s m (E k i*(B i j*(δ*τ)))
    (A.vectorPlaneRead k (A.freeGlobalAmplitude d hρ δ q u i j)) at hplane
  apply hplane.mono_const
  have ht : E k i*B i j ≤ ∑ a, Q a :=
    Finset.single_le_sum (fun a _ => hQ a) (Finset.mem_univ (k,i,j))
  calc
    E k i*(B i j*(δ*τ)) = (E k i*B i j)*(δ*τ) := by ring
    _ ≤ (1+∑ a, Q a)*(δ*τ) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hδ hτ.le)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
