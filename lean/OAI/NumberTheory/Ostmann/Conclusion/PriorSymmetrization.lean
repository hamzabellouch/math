import OAI.NumberTheory.Ostmann.Conclusion.ActualAmplitudeNorm
import OAI.NumberTheory.Ostmann.Conclusion.SymmetrizedNorm

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion
open Construction

theorem prior_correlation_permute {J S : Type*} [Fintype J] [Fintype S]
    (μ : FinitePrior J) (R A : J → S → ℂ) (e : J ≃ J)
    (he : ∀x, μ.mass (e x)=μ.mass x) (hR : ∀x s, R (e x) s=R x s) :
    μ.cmean (fun x => ∑s,R x s*A (e x) s)=μ.cmean (fun x => ∑s,R x s*A x s) := by
  have h := e.sum_comp (fun x => (μ.mass x:ℂ)*∑s,R x s*A x s)
  simpa only [FinitePrior.cmean,he,hR] using h

def priorSymmetrizedCoefficient {J S Γ : Type*} [Fintype Γ]
    (e : Γ → J ≃ J) (A : J → S → ℂ) (x : J) (s : S) : ℂ :=
  (Fintype.card Γ:ℂ)⁻¹*∑σ,A (e σ x) s

theorem prior_correlation_symmetrize {J S Γ : Type*} [Fintype J] [Fintype S]
    [Fintype Γ] [Nonempty Γ] (μ : FinitePrior J) (R A : J → S → ℂ) (e : Γ → J ≃ J)
    (he : ∀σ x, μ.mass (e σ x)=μ.mass x) (hR : ∀σ x s, R (e σ x) s=R x s) :
    μ.cmean (fun x => ∑s,R x s*priorSymmetrizedCoefficient e A x s)=
      μ.cmean (fun x => ∑s,R x s*A x s) := by
  have hlin : ∀ (c : ℂ) (B : Γ → J → S → ℂ),
      μ.cmean (fun x => ∑s,R x s*(c*∑σ,B σ x s)) =
        c*∑σ,μ.cmean (fun x => ∑s,R x s*B σ x s) := by
    intro c B
    simp only [FinitePrior.cmean,Finset.mul_sum]
    calc
      _ = ∑x,∑s,∑σ,c*((μ.mass x:ℂ)*(R x s*B σ x s)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro σ hσ
        ring
      _ = ∑x,∑σ,∑s,c*((μ.mass x:ℂ)*(R x s*B σ x s)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold priorSymmetrizedCoefficient
  rw [hlin]
  simp_rw [prior_correlation_permute μ R A _ (he _) (hR _)]
  have hcard : (Fintype.card Γ:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

theorem prior_correlation_symmetrized_bound {J S Γ : Type*} [Fintype J] [Fintype S]
    [Fintype Γ] [Nonempty Γ] (μ : FinitePrior J) (R A : J → S → ℂ) (e : Γ → J ≃ J)
    (he : ∀σ x, μ.mass (e σ x)=μ.mass x) (hR : ∀σ x s, R (e σ x) s=R x s) :
    ‖μ.cmean (fun x => ∑s,R x s*A x s)‖^2 ≤
      μ.mean (fun x => ∑s,‖R x s‖^2)*
        μ.mean (fun x => ∑s,‖priorSymmetrizedCoefficient e A x s‖^2) := by
  rw [←prior_correlation_symmetrize μ R A e he hR]
  exact prior_correlation_cauchy_schwarz μ R _

end Ostmann.Conclusion

end

end OAI
