import OAI.Probability.InvariantIsing.Cavity.CavityBaseGroups
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalGram
import OAI.Probability.InvariantIsing.Cavity.CavityGroupCovariancePositive
import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaLaw

namespace OAI

/-! The vectors used by the fresh group frames have exactly the
physical projected-overlap covariance divided by the group density. -/

noncomputable section
open IsingPerceptron
open scoped Matrix

namespace InvariantIsing

def cavityGroupSetEquiv {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) :
    Fin (k a) ≃ ↥(cavitySpectralGroup (fun i => (e.symm i).1) a) :=
  (cavityGroupIndexEquiv k e a).trans (Equiv.subtypeEquivRight (by
    intro i
    simp only [cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and]))

lemma cavityGroupSetEquiv_apply {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) (j : Fin (k a)) :
    ((cavityGroupSetEquiv k e a) j : Fin N)=e ⟨a,j⟩ := rfl

lemma cavityGroupSpinCoordinates_physical {N m r : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (V : Orthogonal N) (σ : Fin r → Spin N) :
    (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) =
    cavityPhysicalReplicaVectors (matrixRotation V⁻¹)
      (cavitySpectralGroup (fun i => (e.symm i).1)) k (cavityGroupSetEquiv k e) σ := by
  funext a i j
  rw [cavityPhysicalReplicaVectors, cavityGroupSetEquiv_apply]
  rfl

lemma cavityGroupSpinCoordinates_gram {N m r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N) (a : Fin m) (i j : Fin r) :
    cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) a i j =
      projectedOverlap (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1) a) (σ i) (σ j) / ((k a : ℝ)/N) := by
  rw [cavityGroupSpinCoordinates_physical]
  exact cavityPhysicalReplicaVectors_gram hN _ _ _ _ _ a i j

lemma cavityGroupSpinCoordinates_covariance {N m r depth : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N × LabeledLeaf depth) (q : ℕ) :
    cavityGroupReplicaCovariance q
      (cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i).1)) =
    cavitySpectralBlockCovariance q (fun a => (k a : ℝ)/N)
      (fun i j => spectralJointEntry (matrixRotation V⁻¹)
        (cavitySpectralGroup (fun i => (e.symm i).1)) depth (σ i) (σ j)) := by
  unfold cavitySpectralBlockCovariance
  congr 1
  funext a i j
  rw [cavityGroupSpinCoordinates_gram hN, spectralJointEntry_spectral]

lemma cavityGroupSpinCoordinates_gram_bound {N m r : ℕ} (hN : 0 < N)
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (V : Orthogonal N) (σ : Fin r → Spin N) {c : ℝ} (hc : 0 < c)
    (hk : ∀ a, c ≤ (k a : ℝ)/N) :
    ∀ a i j, |cavityGroupReplicaGram (fun a i => cavityGroupSpinCoordinates k e V a (σ i)) a i j|
      ≤ 1/c := by
  rw [cavityGroupSpinCoordinates_physical]
  exact cavityPhysicalReplicaVectors_gram_bound hN _ _ _ _ _ c hc hk

end InvariantIsing

end

end OAI
