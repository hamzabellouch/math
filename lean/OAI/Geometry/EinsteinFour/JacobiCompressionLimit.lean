import OAI.Geometry.EinsteinFour.ContinuousRadialComparison
import Mathlib.Analysis.Matrix.Order

namespace OAI

/-! Positivity of the actual first-mode compression survives the mesh limit. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Filter
open scoped Matrix.Norms.Frobenius

noncomputable section

theorem reference_compression_posSemidef {N : ℕ} (hN : 0 < N) (t : ℝ)
    (A : Fin N → NormalMatrix) (hfirst : 0 < firstEigenvalue t N)
    (hK : (curvatureDirichlet t A).PosDef) :
    ((1 : NormalMatrix) - ((t / (N + 1)) ^ 2 / firstEigenvalue t N) •
      (∑ i, unitFirstSineVector N i ^ 2 • A i)).PosSemidef := by
  let L := referenceMatrix t N
  let G := scalarNormalizer L
  let w := unitFirstSineVector N
  let a := t / (N + 1)
  let g := 1 / Real.sqrt (firstEigenvalue t N)
  have hL : L.PosDef := scalarDirichlet_posDef N _ hfirst
  have hn : G * L * G = 1 := scalarNormalizer_normalizes hL
  have hsym : Gᵀ = G := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (scalarNormalizer_posSemidef L).isHermitian.eq
  have hlift : (scalarLift G)ᴴ = scalarLift G := by
    ext ⟨u, i⟩ ⟨v, j⟩
    change (1 : NormalMatrix) v u * G j i = (1 : NormalMatrix) u v * G i j
    rw [show G j i = G i j from congrFun (congrFun hsym i) j]
    simp only [Matrix.one_apply, eq_comm]
  have hp := hK.posSemidef.conjTranspose_mul_mul_same (scalarLift G)
  rw [hlift] at hp
  have hc := hp.conjTranspose_mul_mul_same (modeEmbedding w)
  have heigen : G *ᵥ w = g • w :=
    scalarNormalizer_eigenvector hL hfirst (unitFirstSineVector_eigenvector N _)
  have hcomp := normalized_mode_compression G L A w a g
    (unitFirstSineVector_norm hN) hsym hn heigen
  change ((modeEmbedding w)ᴴ *
    (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) *
    modeEmbedding w).PosSemidef at hc
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hcomp] at hc
  have hcoef : (a * g) ^ 2 = a ^ 2 / firstEigenvalue t N := by
    dsimp [g]
    simp only [mul_pow, div_pow, one_pow, Real.sq_sqrt hfirst.le]
    ring
  rwa [hcoef] at hc

theorem continuous_radial_compression_posSemidef {t : ℝ}
    (ht : 0 ≤ t) (htπ : t < Real.pi) (A : ℝ → NormalMatrix)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • A s))
    (hLip : ∀ s r, ‖Averages.sineWeight s • A s - Averages.sineWeight r • A r‖ ≤
      L * |s - r|)
    (hpos : ∀ᶠ N in atTop, (curvatureDirichlet t (sampledCurvature A N)).PosDef) :
    ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
      (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s)).PosSemidef := by
  have hmode := modeAverage_tendsto hL hc hLip
  have hconv : Tendsto (fun N : ℕ => (1 : NormalMatrix) -
      ((t / (N + 1)) ^ 2 / firstEigenvalue t N) • modeAverage A N) atTop
      (nhds ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s))) := tendsto_const_nhds.sub
    ((first_mode_coefficient_tendsto ht htπ).smul hmode)
  apply Matrix.posSemidef_is_closed.mem_of_tendsto hconv
  filter_upwards [hpos, firstEigenvalue_eventually_pos ht htπ,
    eventually_gt_atTop (0 : ℕ)] with N hN heig hNpos
  exact reference_compression_posSemidef hNpos t (sampledCurvature A N) heig hN

end

end PositiveEinsteinFour.Jacobi

end OAI
