import Mathlib

namespace OAI

/-! Cotangent forms, exact Lagrangian embeddings and Hamiltonian isotopies. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian

abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
abbrev Base (n : ℕ) := Sphere 9 × Sphere n
abbrev BaseVector (n : ℕ) := EuclideanSpace ℝ (Fin 9) × EuclideanSpace ℝ (Fin n)
abbrev baseModel (n : ℕ) := (𝓡 9).prod (𝓡 n)
abbrev Cotangent (n : ℕ) :=
  Bundle.TotalSpace (BaseVector n →L[ℝ] ℝ)
    (fun q : Base n => TangentSpace (baseModel n) q →L[ℝ] ℝ)
abbrev CotangentVector (n : ℕ) := BaseVector n × (BaseVector n →L[ℝ] ℝ)
abbrev cotangentModel (n : ℕ) :=
  (baseModel n).prod 𝓘(ℝ, BaseVector n →L[ℝ] ℝ)

def projection {n : ℕ} (z : Cotangent n) : Base n := z.proj

def zeroSection {n : ℕ} (q : Base n) : Cotangent n := ⟨q, 0⟩

def liouville {n : ℕ} (z : Cotangent n) :
    TangentSpace (cotangentModel n) z →L[ℝ] ℝ :=
  z.snd.comp (mfderiv (cotangentModel n) (baseModel n) projection z)

def liouvilleInChart {n : ℕ} (z : Cotangent n) (x : CotangentVector n) :
    CotangentVector n →L[ℝ] ℝ :=
  (liouville ((extChartAt (cotangentModel n) z).symm x)).comp
    (mfderiv 𝓘(ℝ, CotangentVector n) (cotangentModel n)
      (extChartAt (cotangentModel n) z).symm x)

def symplecticForm {n : ℕ} (z : Cotangent n)
    (u v : TangentSpace (cotangentModel n) z) : ℝ :=
  let c := extChartAt (cotangentModel n) z
  let dc := mfderiv (cotangentModel n) 𝓘(ℝ, CotangentVector n) c z
  let dlam := fderiv ℝ (liouvilleInChart z) (c z)
  dlam (dc u) (dc v) - dlam (dc v) (dc u)

def IsClosedExactLagrangian {n : ℕ} (i : Base n → Cotangent n) : Prop :=
  Manifold.IsSmoothEmbedding (baseModel n) (cotangentModel n) ∞ i ∧
  IsCompact (Set.range i) ∧
  (∀ q (u v : TangentSpace (baseModel n) q),
    symplecticForm (i q)
      (mfderiv (baseModel n) (cotangentModel n) i q u)
      (mfderiv (baseModel n) (cotangentModel n) i q v) = 0) ∧
  ∃ f : Base n → ℝ,
    ContMDiff (baseModel n) 𝓘(ℝ, ℝ) ∞ f ∧
    ∀ q (u : TangentSpace (baseModel n) q),
      liouville (i q) (mfderiv (baseModel n) (cotangentModel n) i q u) =
        mfderiv (baseModel n) 𝓘(ℝ, ℝ) f q u

abbrev CotangentDiffeomorph (n : ℕ) :=
  Diffeomorph (cotangentModel n) (cotangentModel n) (Cotangent n) (Cotangent n) ∞

def IsCompactHamiltonianIsotopy {n : ℕ} (H : ℝ → Cotangent n → ℝ)
    (φ : ℝ → CotangentDiffeomorph n) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ).prod (cotangentModel n)) 𝓘(ℝ, ℝ) ∞
    (fun tz : ℝ × Cotangent n => H tz.1 tz.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
  ContMDiffOn (𝓘(ℝ, ℝ).prod (cotangentModel n)) (cotangentModel n) ∞
    (fun tz : ℝ × Cotangent n => φ tz.1 tz.2) (Icc (0 : ℝ) 1 ×ˢ univ) ∧
  (∃ K : Set (Cotangent n), IsCompact K ∧
    ∀ t ∈ Icc (0 : ℝ) 1, Function.support (H t) ⊆ K) ∧
  (∀ z, φ 0 z = z) ∧
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ z (v : TangentSpace (cotangentModel n) (φ t z)),
    symplecticForm (φ t z)
      (mfderivWithin 𝓘(ℝ, ℝ) (cotangentModel n) (fun s => φ s z) (Icc 0 1) t 1) v =
      -(mfderiv (cotangentModel n) 𝓘(ℝ, ℝ) (H t) (φ t z) v)

def IsHamiltonianImage {n : ℕ} (i : Base n → Cotangent n) : Prop :=
  ∃ H : ℝ → Cotangent n → ℝ, ∃ φ : ℝ → CotangentDiffeomorph n,
    IsCompactHamiltonianIsotopy H φ ∧
    Set.range (fun q : Base n => φ 1 (zeroSection q)) = Set.range i

def MainStatement : Prop :=
  ∃ m : ℕ, 20 ≤ m ∧ ∃ i : Base (2 * m - 1) → Cotangent (2 * m - 1),
    IsClosedExactLagrangian i ∧ ¬ IsHamiltonianImage i

end NearbyLagrangian

end

end OAI
