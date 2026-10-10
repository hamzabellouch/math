import OAI.Probability.InvariantIsing.Cavity.CavityFiniteReplicaLaw
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianCoordinateMap
import OAI.Probability.InvariantIsing.Cavity.CavityGroupBlockGaussian

namespace OAI

/-! Selecting the assigned special axes from the Gaussian spectral-group
block gives precisely the finite cavity field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityFiniteReplicaSpectralBlock {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (σ : Fin r → LabeledLeaf n) : SpectralBlock m r :=
  cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
    (cavityCanonicalLabel rho lam hrho hsum p)
    (fun i j => q (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j))))

def cavitySelectedGroupIndex {m d r k : ℕ} (e : Fin d → Fin m × Fin k)
    (u : Fin r × Fin d) : Fin m × (Fin r × Fin k) :=
  ((e u.2).1, (u.1, (e u.2).2))

lemma cavity_finite_group_covariance_posSemidef {m n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (σ : Fin r → LabeledLeaf n) :
    (cavityGroupBlockCovariance k rho
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)).PosSemidef := by
  classical
  let v₀ : LabeledLeaf n := Classical.choice inferInstance
  let σ' := Function.extend Fin.val σ (fun _ => v₀)
  have hs (i : Fin r) : σ' i = σ i := Fin.val_injective.extend_apply σ (fun _ => v₀) i
  have hq' : Monotone (fun i => q (cavityFiniteLevel n i)) :=
    hq.comp (cavityFiniteLevel_monotone n)
  have hG (a : Fin m) := cavity_cascade_transformed_gram n hq'
    (cavityCanonicalCoordinate rho lam hrho hsum p a)
    (cavityCanonicalCoordinate_monotone rho lam hrho hsum p a)
    (cavityCanonicalCoordinate_nonneg rho lam hrho hsum p a _)
    (cavityCanonicalCoordinate_le_diagonal rho lam hrho hsum p a _) σ' r
  apply cavityGroupReplicaCovariance_posSemidef
  intro a
  have hh := (hG a).smul (inv_nonneg.mpr (hrho a).le)
  have heq : (fun i j : Fin r =>
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ i j a : ℝ) / rho a) =
      (rho a)⁻¹ • (fun i j : Fin r => if i = j then spectralGroupDiagonal rho lam hrho hsum p a
        else cavityCanonicalCoordinate rho lam hrho hsum p a
          (cascadeScalarArray n (fun i => q (cavityFiniteLevel n i)) σ' i j)) := by
    funext i j
    simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock,
      cavityCanonicalDiagonal, cavityCanonicalLabel, cascadeScalarArray, hs,
      Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    by_cases hij : i = j <;> simp [hij, mul_comm]
  rw [heq]
  exact hh

lemma cavity_selected_group_covariance {m d n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin k)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (σ : Fin r → LabeledLeaf n) :
    (cavityGroupBlockCovariance k rho
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)).submatrix
        (cavitySelectedGroupIndex e) (cavitySelectedGroupIndex e) =
      cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ := by
  classical
  ext u v
  have haxes : (e u.2).1 = (e v.2).1 ∧ (e u.2).2 = (e v.2).2 ↔ u.2 = v.2 := by
    constructor
    · intro h
      exact he (Prod.ext h.1 h.2)
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
  change (if (e u.2).1 = (e v.2).1 ∧ (e u.2).2 = (e v.2).2 then
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ u.1 v.1 (e u.2).1 : ℝ) /
        rho (e u.2).1 else 0) = _
  simp only [haxes]
  by_cases huv : u.2 = v.2
  · by_cases hij : u.1 = v.1 <;>
      simp [cavityFiniteCanonicalReplicaCovariance, huv, cavityFiniteReplicaSpectralBlock,
        cavitySynchronizedBlock, cavityCanonicalDiagonal, cavityCanonicalLabel, heg, hij]
  · simp [cavityFiniteCanonicalReplicaCovariance, huv]

/-- The physical selected coordinates have exactly the covariance of
root-plus-forest cavity replicas. Unselected axes integrate out. -/
theorem cavity_selected_group_gaussian_law {m d n r k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (e : Fin d → Fin m × Fin k)
    (he : Function.Injective e) (heg : ∀ a, (e a).1 = g a)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (σ : Fin r → LabeledLeaf n) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m × (Fin r × Fin k)))
      (cavityGroupBlockCovariance k rho
        (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ))).map
      (cavityGaussianCoordinateMap (cavitySelectedGroupIndex e)) =
      multivariateGaussian 0 (cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ) := by
  have hh := cavity_gaussian_coordinate_law _
    (cavity_finite_group_covariance_posSemidef rho lam hrho hsum p q hq σ)
    (cavitySelectedGroupIndex e)
  rwa [cavity_selected_group_covariance rho lam hrho hsum g e he heg p q σ] at hh

end InvariantIsing

end

end OAI
