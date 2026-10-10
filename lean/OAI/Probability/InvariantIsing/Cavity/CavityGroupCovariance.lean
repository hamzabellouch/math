import OAI.Probability.InvariantIsing.Cavity.CavityGroupProjection

namespace OAI

/-! Covariance identification for the joint spectral-group projection.
Off-group and off-axis covariances vanish, while replica covariances are
the normalized Gram matrices in each eigenspace. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityGroupProjectionMatrix_covariance {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (i j : Fin m × (Fin r × Fin q)) :
    (cavityGroupProjectionMatrix (q := q) v * (cavityGroupProjectionMatrix (q := q) v).transpose) i j =
      if i.1 = j.1 ∧ i.2.2 = j.2.2 then
        (∑ k, v i.1 i.2.1 k * v i.1 j.2.1 k) / (N i.1 : ℝ) else 0 := by
  classical
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    have he : (cavityGroupProjectionMatrix (q := q) v * (cavityGroupProjectionMatrix (q := q) v).transpose)
        (a, i) (a, j) =
        (cavityProjectionMatrix (q := q) (v a) * (cavityProjectionMatrix (q := q) (v a)).transpose) i j := by
      simp only [Matrix.mul_apply, Fintype.sum_sigma, cavityGroupProjectionMatrix,
        Matrix.transpose_apply, ite_and]
      simp only [ite_mul_ite, mul_zero]
      simp [cavityProjectionMatrix]
    rw [he, cavityProjectionMatrix_covariance]
    simp
  · rw [Matrix.mul_apply, Fintype.sum_sigma]
    have hz (c : Fin m) (k : Fin (N c) × Fin q) :
        cavityGroupProjectionMatrix (q := q) v (a, i) ⟨c, k⟩ *
          (cavityGroupProjectionMatrix (q := q) v).transpose ⟨c, k⟩ (b, j) = 0 := by
      by_cases hac : a = c
      · have hbc : b ≠ c := fun h => hab (hac.trans h.symm)
        simp [cavityGroupProjectionMatrix, Matrix.transpose_apply, hbc]
      · simp [cavityGroupProjectionMatrix, hac]
    simp only [hz, Finset.sum_const_zero]
    simp [hab]

def cavityGroupReplicaCovariance {m r : ℕ} (q : ℕ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ :=
  fun i j => if i.1 = j.1 ∧ i.2.2 = j.2.2 then Q i.1 i.2.1 j.2.1 else 0

lemma cavityGroupProjection_covariance_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k a i j => (∑ l, v k a i l * v k a j l) / (N k a : ℝ))
      atTop (𝓝 Q)) :
    Tendsto (fun k => cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose) atTop
      (𝓝 (cavityGroupReplicaCovariance q Q)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [cavityGroupProjectionMatrix_covariance, cavityGroupReplicaCovariance]
  by_cases hij : i.1 = j.1 ∧ i.2.2 = j.2.2
  · simp only [ite_eq_left hij]
    exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ i.1) i.2.1)) j.2.1
  · simp only [ite_eq_right hij]
    exact tendsto_const_nhds

/-- All spectral groups converge jointly to the Gaussian array prescribed
by their replica Gram limits, including singular limiting arrays. -/
theorem cavityGroupFrameProjection_tendsto_of_replicaGram {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k a i j => (∑ l, v k a i l * v k a j l) / (N k a : ℝ))
      atTop (𝓝 Q)) :
    TendstoInDistribution (fun k => cavityGroupFrameProjection (q := q) (v k)) atTop id
      (fun _ => cavityGroupGaussianRows m q)
      (multivariateGaussian 0 (cavityGroupReplicaCovariance q Q)) := by
  have hcov := cavityGroupProjection_covariance_tendsto (q := q) N v Q hQ
  have hS : (cavityGroupReplicaCovariance q Q).PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hcov (Eventually.of_forall (fun k => by
      simpa using Matrix.posSemidef_self_mul_conjTranspose
        (cavityGroupProjectionMatrix (q := q) (v k))))
  exact cavityGroupFrameProjection_tendstoInDistribution N hN v _ hS hcov

end InvariantIsing

end

end OAI
