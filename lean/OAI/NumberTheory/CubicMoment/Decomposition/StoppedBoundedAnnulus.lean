import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedRadial
import OAI.NumberTheory.CubicMoment.Estimates.FinitePoissonRadial
import OAI.NumberTheory.CubicMoment.Estimates.PoissonDyadicSum

namespace OAI

/-! Bounded squarefree rows in literal Poisson annuli and finite dyadic
sums.  Every nonzero frequency is retained, including cubes. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_poisson_annulus (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S H : Finset Eisenstein)
      (β : Eisenstein → ℂ) (N M B u A J : ℝ),
      65536 ≤ N → 0 ≤ M → 1 ≤ B → 0 ≤ A → 0 < J →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N/2 ≤ norm a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) → 8*B ≤ N^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      (1+A*J/(27*(N/2)^2))^q*‖finitePoissonContribution S H β u V A‖ ≤
        K*A*N*M^2*B^(1/3:ℝ)*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_coprime_radial_form hpnt hHuxley
    (by norm_num : (1:ℝ) ≤ 2) V hV hV' q
  refine ⟨2*K/9,d,by positivity,?_⟩
  intro S H β N M B u A J hN hM hB hA hJ hS hβ hsize hH hHJ
  have hNp : 0 < N := by linarith
  have hL : 0 < N/2 := by positivity
  let ρ := A*J/(27*(N/2)^2)
  let phase := fun h : Eisenstein =>
    (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)
  have hrange : ∀ a ∈ S, norm a/(N/2) ∈ Icc (1:ℝ) 2 := by
    intro a ha
    exact ⟨(le_div_iff₀ hL).mpr (by simpa using (hS a ha).2.2.1),
      (div_le_iff₀ hL).mpr (by linarith [(hS a ha).2.2.2])⟩
  have hb := hbound S H β phase N M B u ρ (N/2) J hN hM hB
    (by dsimp [ρ]; positivity) hL hJ
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)
    hβ hrange hsize hH hHJ (fun h _ => by simp [phase])
  rw [finitePoissonContribution_radial S H (fun a ha => primary_ne_zero (hS a ha).1)
    β u V hA hL hJ,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ = (A/(9*(N/2)))*((1+ρ)^q*‖normCoprimeRadialForm S H
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun a => star (β a*mellinPhase u (norm a))) phase
        (fun h => norm h/J) (fun a => norm a/(N/2)) V ρ‖) := by ring
    _ ≤ (A/(9*(N/2)))*(K*M^2*N^2*B^(1/3:ℝ)*(1+Real.log N)^d) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

theorem bounded_poisson_dyadic (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (H : ℕ → Finset Eisenstein) (I : Finset ℕ) (β : Eisenstein → ℂ)
      (N M u A : ℝ), 65536 ≤ N → 0 ≤ M → 0 < A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N/2 ≤ norm a ∧ norm a ≤ N) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      (∀ j ∈ I, 16*(2:ℝ)^j ≤ N^(3/4:ℝ)) → (∀ j, H j ⊆ frequencyDyad j) →
      ‖∑ j ∈ I, finitePoissonContribution S (H j) β u V A‖ ≤
        K*A^(2/3:ℝ)*N^(5/3:ℝ)*M^2*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_poisson_annulus hpnt hHuxley V hV hV' 3
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨3*K*(2:ℝ)^(1/3:ℝ)*D,d,by positivity,?_⟩
  intro S H I β N M u A hN hM hA hS hβ hI hH
  have hNp : 0 < N := by linarith
  have hlog : 0 ≤ 1+Real.log N := by
    have hN1 : 1 ≤ N := by linarith
    linarith [Real.log_nonneg hN1]
  let t := A/(27*N^2)
  let C₀ := K*A*N*M^2*(2:ℝ)^(1/3:ℝ)*(1+Real.log N)^d
  let F := fun j => finitePoissonContribution S (H j) β u V A
  have ht : 0 < t := by dsimp [t]; positivity
  have hrow (j : ℕ) (hj : j ∈ I) :
      ‖F j‖ ≤ C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hY : 0 < (2:ℝ)^j := by positivity
    have hY1 : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hb := hbound S (H j) β N M (2*(2:ℝ)^j) u A ((2:ℝ)^j)
      hN hM (by linarith) hA.le hY hS hβ (by linarith [hI j hj])
      (fun h hh => ⟨(mem_frequencyDyad.mp (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
      (fun h hh => frequencyDyad_norm (hH j hh))
    have hscale : t*(2:ℝ)^j ≤ A*(2:ℝ)^j/(27*(N/2)^2) := by
      calc
        _ = A*(2:ℝ)^j/(27*N^2) := by dsimp [t]; ring
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg N])
    have hw : (1+t*(2:ℝ)^j)^3*‖F j‖ ≤
        (1+A*(2:ℝ)^j/(27*(N/2)^2))^3*‖F j‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 3)
        (_root_.norm_nonneg _)
    have hr := hw.trans hb
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hY.le] at hr
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀]
    convert hr using 1 <;> ring
  have hs := finite_cubic_dyadic_sum I F (by dsimp [C₀]; positivity) ht hrow
  apply hs.trans_eq
  calc
    _ = (K*(2:ℝ)^(1/3:ℝ)*D*M^2*(1+Real.log N)^d)*
        (A*N*(A/(27*N^2))^(-(1/3:ℝ))) := by dsimp [C₀,t,D]; ring
    _ = _ := by rw [cubic_poisson_scale hA hNp]; ring

end CubicFirstMoment

end

end OAI
