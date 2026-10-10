import Mathlib
import OAI.Computability.MinUncut.Estimates.FirstError

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
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

theorem lowGradient_energy_lower_weighted (w : Ξ → ℝ) (hw : ∀ ξ, 0≤w ξ)
    (hw1 : ∑ ξ, w ξ=1) (f : ∀ ξ, FoldedProof (A ξ)) (hn : 0 < n)
    {σ η a ε : ℝ} (hσ : σ≠0) (hη : η≠0) (ha : 0≤a) (ha1 : a≤1) (hε : 0≤ε)
    (D s : ℕ) (hD : ∀ k : ℕ, D<k → 1≤(k:ℝ)*a)
    (hs : ∀ k : ℕ, s+2≤k → (k:ℝ)*(smoothingRho σ)^(2*k)≤ε) :
    1-4*(∑ ξ, w ξ*firstError (m := m) (n := n) (f ξ) σ η)-
      8*σ⁻¹^2*(∑ ξ, w ξ*secondError (m := m) (n := n) (f ξ) a σ η)-2*ε ≤
      ∑ ξ, w ξ*averagedEnergy (lowGradient (m := m) (n := n) D s (f ξ) σ η) := by
  calc
    _ = ∑ ξ, w ξ*(1-4*firstError (m := m) (n := n) (f ξ) σ η-
        8*σ⁻¹^2*secondError (m := m) (n := n) (f ξ) a σ η-2*ε) := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
      simp_rw [show ∀ ξ, w ξ*(4*firstError (m := m) (n := n) (f ξ) σ η) =
        4*(w ξ*firstError (m := m) (n := n) (f ξ) σ η) by intro ξ; ring,
        show ∀ ξ, w ξ*(8*σ⁻¹^2*secondError (m := m) (n := n) (f ξ) a σ η) =
        (8*σ⁻¹^2)*(w ξ*secondError (m := m) (n := n) (f ξ) a σ η) by intro ξ; ring,
        show ∀ ξ, w ξ*(2*ε) = (2*ε)*w ξ by intro ξ; ring]
      rw [← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hw1,mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left
      (lowGradient_energy_lower (m := m) (f ξ) hn hσ hη ha ha1 hε D s hD hs) (hw ξ))

open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniform_gaussian_cutoff {σ ε : ℝ} (hσ : σ≠0) (hε : 0<ε) :
    ∃ s : ℕ, ∀ (V A : Type*) [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
      [Fintype A] (m n : ℕ) (_hn : 0<n) (f : FoldedProof A) (η : ℝ),
      averagedEnergy (m := m) (n := n)
        (fun B c x => gradient f B σ η c x-gaussianProject s f B σ η c x) ≤ ε := by
  obtain ⟨s,hs⟩ := exists_cutoff (smoothingRho_lt_one hσ) hε
  refine ⟨s, fun V A _ _ _ _ m n hn f η => ?_⟩
  exact gaussian_tail_of_cutoff f hn hσ hε.le η s hs
end MinUncut.Inner

end

end OAI
