import Mathlib
import OAI.Analysis.WeakInfiniteness.OrthogonalPerturbation
import OAI.Analysis.WeakInfiniteness.UniversePerturbation

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem selfadjoint_uniform_perturbation_of_gap_any
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type u) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModelsAny B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (p q h k c : A) (hpn : ‖p‖ ≤ 1) (hqn : ‖q‖ ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p*q=0)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hph : star p*p*h=h) (hqk : q*star q*k=k)
    (hch : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h))
    (hck : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k))
    (T : A) {η α : ℝ} (hη : 0 < η) (hα : 0 < α) :
    ∃ y : A, ‖y‖ ≤ 1 ∧ IsSelfAdjoint y ∧
      (∃ z : A, y=p*z*q+star (p*z*q)) ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖ := by
  have hpp : p*p*h=h := by simpa only [hp.star_eq] using hph
  have hqq : q*q*k=k := by simpa only [hq.star_eq] using hqk
  have hp4 : star (p*p)*(p*p)*h=h := by
    rw [star_mul,hp.star_eq]
    calc
      (p*p)*(p*p)*h=(p*p)*(p*p*h) := by noncomm_ring
      _ = h := by rw [hpp,hpp]
  have hq4 : (q*q)*star (q*q)*k=k := by
    rw [star_mul,hq.star_eq]
    calc
      (q*q)*(q*q)*k=(q*q)*(q*q*k) := by noncomm_ring
      _ = k := by rw [hqq,hqq]
  have hppn : ‖p*p‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg p])
  have hqqn : ‖q*q‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg q])
  obtain ⟨z,hzn,hz⟩ := uniform_perturbation_of_gap_any hσ hσγ hgap hA hn hpi
    (p*p) (q*q) h k c hppn hqqn hh hk hc hp4 hq4 hch hck T hη hα
  have hy := orthogonal_selfadjoint_test p q z hp hq hpq hpn hqn hzn
  refine ⟨p*z*q+star (p*z*q),hy.1,isSelfAdjoint_add_star _,⟨z,rfl⟩,?_⟩
  intro H π hπc
  rw [hy.2]
  exact hz H π hπc

end

end WeakPureInfiniteness
end

end OAI
