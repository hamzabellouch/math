import Mathlib
import OAI.Computability.MinUncut.Estimates.ActualBoxBound

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
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma gradient_energy_first_tables (f : FoldedProof A) (hn : 0 < n)
    {σ η : ℝ} (hσ : σ≠0) (hη : η≠0) :
    1-4*(𝔼 B : FaceArray A m n, ∫ c, firstRejection f B σ η c ∂gauss (Point m n)) ≤
      𝔼 B : FaceArray A m n, ∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n) := by
  calc
    _ = 𝔼 B : FaceArray A m n, (1-4*(∫ c, firstRejection f B σ η c ∂gauss (Point m n))) := by
      rw [Finset.expect_sub_distrib,← Finset.mul_expect,Fintype.expect_const]
    _ ≤ _ := Finset.expect_le_expect (fun B _ => gradient_energy_first f B hn hσ hη)
end MinUncut.Inner
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)]
variable {m n : ℕ}

theorem gradient_energy_first_weighted (w : Ξ → ℝ) (hw : ∀ ξ, 0≤w ξ)
    (hw1 : ∑ ξ, w ξ=1) (f : ∀ ξ, FoldedProof (A ξ)) (hn : 0 < n)
    {σ η : ℝ} (hσ : σ≠0) (hη : η≠0) :
    1-4*(∑ ξ, w ξ*(𝔼 B : FaceArray (A ξ) m n,
      ∫ c, firstRejection (f ξ) B σ η c ∂gauss (Point m n))) ≤
      ∑ ξ, w ξ*(𝔼 B : FaceArray (A ξ) m n,
      ∫ c, spatialEnergy (gradient (f ξ) B σ η c) ∂gauss (Point m n)) := by
  calc
    _ = ∑ ξ, w ξ*(1-4*(𝔼 B : FaceArray (A ξ) m n,
        ∫ c, firstRejection (f ξ) B σ η c ∂gauss (Point m n))) := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,← mul_assoc]
      conv_rhs => rhs; arg 2; ext ξ; rw [mul_comm (w ξ) 4]
      rw [Finset.mul_sum,hw1]
      simp only [mul_assoc]
    _ ≤ _ := Finset.sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left
      (gradient_energy_first_tables (f ξ) hn hσ hη) (hw ξ))
end MinUncut.Inner

end

end OAI
