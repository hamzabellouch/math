import OAI.NumberTheory.CubicMoment.Estimates.ProfileRadialForm
import OAI.NumberTheory.CubicMoment.Estimates.HeightPoissonAnnulus

namespace OAI

/-! Uniform profile control survives the exact A/(9N) Poisson Jacobian. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem smallB_poisson_annulus_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (q : ℕ) (hq : q ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (A B T u N J : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 < A → 0 < N → 0 < J →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) 2) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      (1+A*J/(27*N^2))^q*dyadicHeightMean (fun t =>
        ‖finitePoissonContribution S H β (u+t) P.V A‖) T ≤
        (K*P.cost)*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := smallB_radial_form_height_power hMV hC hHuxley q hq
  refine ⟨K/9,by positivity,?_⟩
  intro P S H β Z A B T u N J hZ hB hT hA hN hJ hS hrange hsize hH hHJ
  let phase := fun h : Eisenstein =>
    (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)
  have hb := hbound P S H β phase Z B T u (A*J/(27*N^2)) N J
    hZ hB hT (by positivity) hN hJ hS hrange hsize hH hHJ
    (fun h _ => by simp [phase])
  have heq (t : ℝ) : ‖finitePoissonContribution S H β (u+t) P.V A‖ =
      (A/(9*N))*‖normCoprimeRadialForm S H
        (fun a => star (β a*mellinPhase (t+u) (norm a)))
        (fun a => star (β a*mellinPhase (t+u) (norm a)))
        phase (fun h => norm h/J) (fun a => norm a/N) P.V (A*J/(27*N^2))‖ := by
    rw [finitePoissonContribution_radial S H
      (fun a ha => primary_ne_zero (hS a ha).1) β (u+t) P.V hA.le hN hJ,
      norm_mul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ A/(9*N) by positivity)]
    simp only [add_comm u t,phase]
  simp_rw [heq]
  rw [dyadicHeightMean_const_mul]
  calc
    _ = (A/(9*N))*((1+A*J/(27*N^2))^q*dyadicHeightMean (fun t =>
        ‖normCoprimeRadialForm S H
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          (fun a => star (β a*mellinPhase (t+u) (norm a)))
          phase (fun h => norm h/J) (fun a => norm a/N) P.V (A*J/(27*N^2))‖) T) := by ring
    _ ≤ (A/(9*N))*((K*P.cost)*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end CubicFirstMoment.ProfileControl

end

end OAI
