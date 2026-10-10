import OAI.NumberTheory.CubicMoment.Estimates.SmallBPoissonAnnulus
import OAI.NumberTheory.CubicMoment.Estimates.HeightPoissonDyadic

namespace OAI

/-! Sum the genuine low Poisson annuli for arbitrary coefficients at
the natural Fourier scale. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem smallB_poisson_dyadic_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) {R : ℝ} (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (I : Finset ℕ) (β : Eisenstein → ℂ) (Z : ℕ) (A T u N : ℝ),
      1 ≤ (Z:ℝ) → (Z:ℝ)^(1/50:ℝ) ≤ T → 0 < A → 0 < N →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) R) →
      (∀ j ∈ I, 16*(2:ℝ)^j ≤ (Z:ℝ)^(3/4:ℝ)) →
      (∀ j, H j ⊆ frequencyDyad j) →
      dyadicHeightMean (fun t => ‖∑ j ∈ I, finitePoissonContribution S (H j) β (u+t) V A‖) T ≤
        K*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*(A/(27*N^2))^(-(1/3:ℝ))*
          ∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := smallB_poisson_annulus_height_power hMV hC hHuxley hR V hV hV' 3
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨K*(2:ℝ)^(1/3:ℝ)*D,by positivity,?_⟩
  intro S H I β Z A T u N hZ hT hA hN hS hrange hI hH
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  let t := A/(27*N^2)
  let C₀ := K*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*(2:ℝ)^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2
  let F := fun j v => finitePoissonContribution S (H j) β (u+v) V A
  have ht : 0 < t := by dsimp [t]; positivity
  have hrow (j : ℕ) (hj : j ∈ I) :
      dyadicHeightMean (fun v => ‖F j v‖) T ≤ C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hJ : 0 < (2:ℝ)^j := by positivity
    have hJ₁ : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hb := hbound S (H j) β Z A (2*(2:ℝ)^j) T u N ((2:ℝ)^j)
      hZ (by linarith) hT hA hN hJ hS hrange
      (by linarith [hI j hj])
      (fun h hh => ⟨(mem_frequencyDyad.mp (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
      (fun h hh => ⟨(frequencyDyad_norm (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
    have heq : A*(2:ℝ)^j/(27*N^2) = t*2^j := by dsimp [t]; ring
    rw [heq,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le] at hb
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀,F]
    convert hb using 1 <;> ring
  have hs := averaged_cubic_dyadic_sum I F
    (fun j _ => (finitePoissonContribution_continuous_height S (H j) β V A).comp
      (continuous_const.add continuous_id)) (by dsimp [C₀]; positivity) ht hTp hrow
  apply hs.trans_eq
  dsimp [C₀,t,D]
  ring

end CubicFirstMoment

end

end OAI
