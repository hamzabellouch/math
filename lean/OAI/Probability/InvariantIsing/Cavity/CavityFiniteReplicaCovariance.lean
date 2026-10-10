import OAI.Probability.InvariantIsing.Cavity.CavityReplicaNodeCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteSpectralEntries
import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalLabels

namespace OAI

/-! The actual finite cavity Gaussian replica covariance is the canonical
spectral covariance, with its full diagonal including the ordinary residual. -/

noncomputable section
open MeasureTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

variable {m d n r : ℕ}
variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hcut hfirst hlast hq hp htop in
lemma cavity_finite_replica_covariance_prefix (σ : Fin r → LabeledLeaf n)
    (i j : Fin r) (a b : Fin d) :
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let R := cavityFiniteCovariancePath rho lam hrho hsum g p q n
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    rho (g a) * cavityReplicaGaussianCovariance n S₀ R S σ (i, a) (j, b) =
      if a = b then
        (∫ t in 0..q (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j))),
          spectralPathDensity rho lam hrho hsum p (g a) t) +
        (if i = j then projectedResolvent rho lam hrho hsum (g a)
          (deficit p (q (Fin.last n))) else 0) else 0 := by
  dsimp only
  have hx (l : Fin (n + 1)) : 0 < deficit p (q l) :=
    finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last _))
  have hR : rho (g a) * cavityFiniteCovariancePath rho lam hrho hsum g p q n a b =
      if a = b then projectedResolvent rho lam hrho hsum (g a)
        (deficit p (q (Fin.last n))) else 0 := by
    simpa only [cavityFiniteCovariancePath, cavityFiniteDeficitPath, cavityFiniteLevel_last]
      using cavity_finite_covariance_weighted_entry rho lam hrho hsum g (hx (Fin.last n)) a b
  rw [cavityReplicaGaussianCovariance_entry, mul_add, mul_add, Finset.mul_sum]
  simp_rw [mul_ite, mul_zero, cavity_finite_root_weighted_entry rho lam hrho hsum g p q (hx 0),
    cavity_finite_noise_weighted_entry rho lam hrho hsum g p cut q hx, hR]
  by_cases hab : a = b
  · subst b
    simp only [ite_true]
    have hl : (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j)) : ℕ) =
        labeledCommonDepth n (σ i) (σ j) :=
      min_eq_left (labeledCommonDepth_le n (σ i) (σ j))
    rw [finite_overlap_spectral_prefix rho lam hrho hsum p cut hcut hfirst hlast q hq hp htop]
    simp only [hl]
  · simp [hab]

include hcut hfirst hlast hq hp htop in
lemma cavity_finite_replica_covariance_canonical (σ : Fin r → LabeledLeaf n)
    (i j : Fin r) (a b : Fin d) :
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let R := cavityFiniteCovariancePath rho lam hrho hsum g p q n
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    rho (g a) * cavityReplicaGaussianCovariance n S₀ R S σ (i, a) (j, b) =
      if a = b then
        (if i = j then spectralGroupDiagonal rho lam hrho hsum p (g a) else
          cavityCanonicalCoordinate rho lam hrho hsum p (g a)
            (q (cavityFiniteLevel n (labeledCommonDepth n (σ i) (σ j))))) else 0 := by
  dsimp only
  rw [cavity_finite_replica_covariance_prefix rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop]
  by_cases hab : a = b
  · subst b
    simp only [ite_true]
    by_cases hij : i = j
    · subst j
      simp only [labeledCommonDepth_self, cavityFiniteLevel_last, ite_true]
      have ht := integral_spectralPathDensity_tail rho lam hrho hsum p (g a) htop.le
        ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        ((continuous_spectralPathDensity rho lam hrho hsum p (g a)).intervalIntegrable 0 (q (Fin.last n)))
        ((continuous_spectralPathDensity rho lam hrho hsum p (g a)).intervalIntegrable (q (Fin.last n)) 1)
      rw [ht] at hadd
      exact hadd
    · simp only [hij, ite_false, add_zero, cavityCanonicalCoordinate]
      rw [Set.projIcc_of_mem zero_le_one
        (finite_overlap_value_mem_unit p cut hcut q hp _)]
  · simp only [hab, ite_false]

end InvariantIsing

end

end OAI
