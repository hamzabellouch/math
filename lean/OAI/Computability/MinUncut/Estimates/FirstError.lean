import Mathlib
import OAI.Computability.MinUncut.Analysis.GradientEnergyFirstTables
import OAI.Computability.MinUncut.Analysis.LowGradient

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

def firstError (f : FoldedProof A) (σ η : ℝ) : ℝ :=
  𝔼 B : FaceArray A m n, ∫ c, firstRejection f B σ η c ∂gauss (Point m n)

def secondError (f : FoldedProof A) (a σ η : ℝ) : ℝ :=
  𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
    RowNoise.density a B C*(∫ c, secondRejection f B C σ η c ∂gauss (Point m n))

lemma gaussian_tail_of_cutoff (f : FoldedProof A) (hn : 0 < n)
    {σ ε : ℝ} (hσ : σ≠0) (hε : 0≤ε) (η : ℝ) (s : ℕ)
    (hs : ∀ k : ℕ, s+2≤k → (k:ℝ)*(smoothingRho σ)^(2*k)≤ε) :
    averagedEnergy (m := m) (n := n)
      (fun B c x => gradient f B σ η c x-gaussianProject s f B σ η c x) ≤ ε := by
  have he (B : FaceArray A m n) :
      (∫ c, spatialEnergy (fun x => gradient f B σ η c x-gaussianProject s f B σ η c x)
        ∂gauss (Point m n)) ≤ ε := by
    rw [gaussian_residual_energy s f B hn hσ]
    exact convolution_gradient_tail (ne_of_gt (smoothingRho_pos σ)) hσ
      (smoothingRho_rotation σ) hε s hs (measurable_tableSmooth f B η)
      (tableSmooth_abs_le f B η)
  simpa [averagedEnergy] using Finset.expect_le_expect (s := Finset.univ) (fun B _ => he B)

theorem lowGradient_energy_lower (f : FoldedProof A) (hn : 0 < n)
    {σ η a ε : ℝ} (hσ : σ≠0) (hη : η≠0) (ha : 0≤a) (ha1 : a≤1) (hε : 0≤ε)
    (D s : ℕ) (hD : ∀ k : ℕ, D<k → 1≤(k:ℝ)*a)
    (hs : ∀ k : ℕ, s+2≤k → (k:ℝ)*(smoothingRho σ)^(2*k)≤ε) :
    1-4*firstError (m := m) (n := n) f σ η-
      8*σ⁻¹^2*secondError (m := m) (n := n) f a σ η-2*ε ≤
      averagedEnergy (lowGradient (m := m) (n := n) D s f σ η) := by
  have h1 := gradient_energy_first_tables (m := m) f hn hσ hη
  have h2 := gradient_row_tail_average (m := m) f hn hσ ha ha1 η D hD
  have hc := gaussian_tail_of_cutoff (m := m) f hn hσ hε η s hs
  have he := lowGradient_residual_le (m := m) (n := n) D s f hσ η
  have hi := lowGradient_energy_identity (m := m) (n := n) D s f hσ η
  change 1-4*firstError (m := m) (n := n) f σ η ≤
    averagedEnergy (m := m) (n := n) (fun B c => gradient f B σ η c) at h1
  change averagedEnergy (m := m) (n := n) (fun B c x =>
    gradient f B σ η c x-rowProjectedGradient D f σ η B c x) ≤
    4*σ⁻¹^2*secondError (m := m) (n := n) f a σ η at h2
  linarith
end MinUncut.Inner

end

end OAI
