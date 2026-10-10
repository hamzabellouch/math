import OAI.NumberTheory.CubicMoment.Estimates.LowProfilePoissonAnnulus
import OAI.NumberTheory.CubicMoment.Estimates.HeightPoissonDyadic

namespace OAI
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem low_poisson_dyadic_height_log_saving (hpnt : PrimaryPrimePNT) (k : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (I : Finset ℕ) (β : Eisenstein → ℂ) (Z : ℕ) (A T M u N : ℝ),
      65536 ≤ (Z:ℝ) → 0 ≤ M → (1+Real.log Z)^Ct ≤ T → 0 < A → 0 < N →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) 2) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      (∀ j ∈ I, 16*(2:ℝ)^j ≤ (Z:ℝ)^(3/4:ℝ)) →
      (∀ j, H j ⊆ frequencyDyad j) →
      dyadicHeightMean (fun t => ‖∑ j ∈ I, finitePoissonContribution S (H j) β (u+t) P.V A‖) T ≤
        (K*P.cost)*(A/N)*(Z:ℝ)^2*(A/(27*N^2))^(-(1/3:ℝ))*
          M^2/(1+Real.log Z)^k := by
  obtain ⟨K₀,Ct,hK₀,hbound₀⟩ := low_poisson_annulus_height_log_saving hpnt k hMV hC hHuxley 3 (by norm_num)
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨K₀*(2:ℝ)^(1/3:ℝ)*D,Ct,by positivity,?_⟩
  intro P S H I β Z A T M u N hZ hM hT hA hN hS hrange hβ hI hH
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
  have hZ1 : 1 ≤ (Z:ℝ) := by linarith
  have hlog : 0 < 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hlog _).trans_le hT
  let t := A/(27*N^2)
  let C₀ := K*(A/N)*(Z:ℝ)^2*(2:ℝ)^(1/3:ℝ)*M^2/(1+Real.log Z)^k
  let F := fun j v => finitePoissonContribution S (H j) β (u+v) P.V A
  have ht : 0 < t := by dsimp [t]; positivity
  have hrow (j : ℕ) (hj : j ∈ I) :
      dyadicHeightMean (fun v => ‖F j v‖) T ≤ C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hJ : 0 < (2:ℝ)^j := by positivity
    have hJ₁ : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hb := hbound S (H j) β Z A (2*(2:ℝ)^j) T M u N ((2:ℝ)^j)
      hZ (by linarith) hM hT hA hN hJ hS hrange hβ
      (by linarith [hI j hj])
      (fun h hh => ⟨(mem_frequencyDyad.mp (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
      (fun h hh => ⟨(frequencyDyad_norm (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
    have heq : A*(2:ℝ)^j/(27*N^2) = t*2^j := by dsimp [t]; ring
    rw [heq,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le] at hb
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀,F]
    convert hb using 1 <;> ring
  have hs := averaged_cubic_dyadic_sum I F
    (fun j _ => (finitePoissonContribution_continuous_height S (H j) β P.V A).comp
      (continuous_const.add continuous_id)) (by dsimp [C₀]; positivity) ht hTp hrow
  apply hs.trans_eq
  dsimp [C₀,t,D,K]
  ring

end CubicFirstMoment.ProfileControl

end

end OAI
