import OAI.Probability.InvariantIsing.Cavity.CavityFiniteTestComparison
import OAI.Probability.InvariantIsing.Cavity.CavityTestLimit

namespace OAI

/-! Averaging the actual full/base cutoff comparison over the coupled
spectral geometry. No uniformity in the unbounded interaction energy is
needed: the explicit error depends only on the geometric cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def cavityBaseCutoffReplicaMean {N n m depth r : ℕ}
    (U : Rotation (N + n)) (V : Rotation N)
    (J : Fin m → Finset (Fin N)) (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (D : ℝ)
    (ν : Measure {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D})
    (Φ : (Fin r → {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D}) → ℝ) : ℝ :=
  cavityCylinderReplicaMean ν
    (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.val.1.1 +
      t * (rotatedEnergy eig U (cavityJoinedSpin x.val.1) - rotatedEnergy eig₀ V x.val.1.1))
    (fun x => cavityPerturbationCoefficients V J u depth (x.val.1.1, x.val.2)) Φ

def cavityFullCutoffReplicaMean {N n m depth r : ℕ}
    (U : Rotation (N + n)) (I : Fin m → Finset (Fin (N + n)))
    (eig : Fin (N + n) → ℝ) (v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (D : ℝ)
    (ν : Measure {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D})
    (Φ : (Fin r → {x : (Spin N × Spin n) × LabeledLeaf depth // w x.1 ≤ D}) → ℝ) : ℝ :=
  cavityCylinderReplicaMean ν
    (fun x => rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.val.1))
    (fun x => cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.val.1, x.val.2)) Φ

theorem cavity_disorder_cutoff_test_comparison {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {N n m depth r : ℕ} (hN : 0 < N)
    (U : Ω → Rotation (N + n)) (V : Ω → Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (w : Ω → Spin N × Spin n → ℝ) (hw : ∀ ω x, 1 ≤ w ω x)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (herr : ∀ ω x y a, |projectedOverlap (U ω) (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap (V ω) (J a) x.1 y.1| ≤ C / N * (w ω x + w ω y))
    (ν : (ω : Ω) → Measure {x : (Spin N × Spin n) × LabeledLeaf depth // w ω x.1 ≤ D})
    [∀ ω, IsProbabilityMeasure (ν ω)]
    (Φ : (ω : Ω) → (Fin r → {x : (Spin N × Spin n) × LabeledLeaf depth // w ω x.1 ≤ D}) → ℝ)
    {B s : ℝ} (hB : 0 ≤ B) (hΦ : ∀ ω σ, |Φ ω σ| ≤ B) (hs : 0 < s) :
    |∫ ω, cavityBaseCutoffReplicaMean (U ω) (V ω) J eig eig₀ v u t (w ω) D (ν ω) (Φ ω) -
      cavityFullCutoffReplicaMean (U ω) I eig v u t (w ω) D (ν ω) (Φ ω) ∂P| ≤
      (2 * (r : ℝ)^2 * (cavityCovarianceRate n C N * (2 * D)) +
        2 * r * (cavityCovarianceRate n C N * (2 * D)) +
        2 * r * (cavityDeterministicRate n m (2 * C) N * D)) / s + B^2 * s / 2 := by
  have hb := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => cavityBaseCutoffReplicaMean (U ω) (V ω) J eig eig₀ v u t (w ω) D (ν ω) (Φ ω) -
      cavityFullCutoffReplicaMean (U ω) I eig v u t (w ω) D (ν ω) (Φ ω))
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact cavity_finite_cutoff_test_comparison hN (U ω) (V ω) I J eig eig₀ v hv u hu t
        (w ω) (hw ω) hC hD (herr ω) (ν ω) (Φ ω) hB (hΦ ω) hs)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

end InvariantIsing

end

end OAI
