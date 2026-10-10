import OAI.Probability.InvariantIsing.Cavity.CavityFiniteReplicaCovariance

namespace OAI

/-! The exact Gaussian law used on the finite spectral side of the
physical replica comparison, with every covariance fixed by the overlap path. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityFiniteCanonicalReplicaCovariance {m d n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (σ : Fin r → LabeledLeaf n) : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  fun u v => if u.2 = v.2 then
    (if u.1 = v.1 then spectralGroupDiagonal rho lam hrho hsum p (g u.2) else
      cavityCanonicalCoordinate rho lam hrho hsum p (g u.2)
        (q (cavityFiniteLevel n (labeledCommonDepth n (σ u.1) (σ v.1))))) / rho (g u.2)
      else 0

variable {m d n r : ℕ}
variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hcut hfirst hlast hq hp htop in
lemma cavity_finite_replica_covariance_eq (σ : Fin r → LabeledLeaf n) :
    cavityReplicaGaussianCovariance n
      (cavityFiniteRootCovariance rho lam hrho hsum g p q)
      (cavityFiniteCovariancePath rho lam hrho hsum g p q n)
      (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q) σ =
      cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ := by
  ext u v
  have he := cavity_finite_replica_covariance_canonical rho lam hrho hsum g p cut hcut
    hfirst hlast q hq hp htop σ u.1 v.1 u.2 v.2
  apply (mul_left_cancel₀ (hrho (g u.2)).ne')
  rw [he]
  dsimp only [cavityFiniteCanonicalReplicaCovariance]
  by_cases huv : u.2 = v.2
  · simp only [huv, ite_true]
    field_simp [(hrho (g v.2)).ne']
  · simp only [huv, ite_false, mul_zero]

include hcut hfirst hlast hq hp htop in
/-- The finite cavity root, actual independent forest, and replica-specific
ordinary residuals have the canonical spectral Gaussian block law. -/
theorem cavity_finite_replica_field_law (T : LabeledTree n) (σ : Fin r → LabeledLeaf n) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (cavityFiniteRootCovariance rho lam hrho hsum g p q)).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d))
        (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d))
            (cavityFiniteCovariancePath rho lam hrho hsum g p q n)))).map
      (fun z => WithLp.toLp 2 (fun u : Fin r × Fin d =>
        (cavityLeafSum n z.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n z.1.2) (σ u.1)) + z.2 u.1) u.2)) =
      multivariateGaussian 0 (cavityFiniteCanonicalReplicaCovariance rho lam hrho hsum g p q σ) := by
  have hS₀ := cavityFiniteCovariance_root_posSemidef rho lam hrho hsum g
    (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop 0)
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1
  have hR := (cavityFiniteCovariancePath_posDef rho lam hrho hsum g p cut hfirst hlast
    q hq hp htop n).posSemidef
  have hS := cavityFiniteNoiseCovariance_posSemidef rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop
  have he := cavity_replica_gaussian_field_law n
    (cavityFiniteRootCovariance rho lam hrho hsum g p q)
    (cavityFiniteCovariancePath rho lam hrho hsum g p q n)
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q) hS₀ hR hS T σ
  rw [cavity_finite_replica_covariance_eq rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop σ] at he
  exact he

end InvariantIsing

end

end OAI
