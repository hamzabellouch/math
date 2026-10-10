import OAI.Probability.InvariantIsing.Cavity.CavityBlockMarkedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityHaarStrictCascade

namespace OAI

/-! The actual finite strict-cascade law with its recalculated Gaussian
marks, including the spectral block labels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def cavityPathReplicaBlock {m r : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    JointArray → SpectralBlock m r :=
  fun x => cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hsum p)
    (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x)

lemma continuous_cavityPathReplicaBlock {m r : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    Continuous (cavityPathReplicaBlock (r := r) ρ eig hρ hsum p) :=
  (continuous_cavitySynchronizedBlock _ _ (continuous_cavityCanonicalLabel ρ eig hρ hsum p)).comp
    (by unfold arrayBlock spinArray; fun_prop)

def cavityStrictMarkedLaw {m r q : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) (n : ℕ) :
    ProbabilityMeasure (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :=
  cavityBlockMarkedLaw
    (cascadeCompactLaw n (chainExponent (uniformCut n))
      (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i))) ρ
    (cavityPathReplicaBlock ρ eig hρ hsum (cavityStrictUniformPath p n))

lemma cavityStrictMarkedLaw_integral {m r q : ℕ} (ρ eig : Fin m → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1) (p : OverlapPath) (n : ℕ)
    (f : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) → ℝ)
    (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ z, f z ∂(cavityStrictMarkedLaw (r := r) (q := q) ρ eig hρ hsum p n : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))) =
      ∫ x, ∫ y, f (cavityPathReplicaBlock ρ eig hρ hsum (cavityStrictUniformPath p n) x,y)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ
          (cavityPathReplicaBlock ρ eig hρ hsum (cavityStrictUniformPath p n) x))
        ∂(cascadeCompactLaw n (chainExponent (uniformCut n))
          (fun i => cavityStrictUniformLevels p n (cavityFiniteLevel n i)) : Measure JointArray) :=
  cavityBlockMarkedLaw_integral _ _ _
    (continuous_cavityPathReplicaBlock _ _ _ _ _).measurable f hf hbound

end InvariantIsing

end

end OAI
