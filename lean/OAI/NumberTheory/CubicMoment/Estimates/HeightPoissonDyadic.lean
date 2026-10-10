import OAI.NumberTheory.CubicMoment.Estimates.HeightPoissonAnnulus
import OAI.NumberTheory.CubicMoment.Estimates.PoissonDyadicSum
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace OAI

/-! Sum the actual height-averaged frequency annuli at their natural
Poisson scale; arbitrary subsets of each annulus are allowed. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dyadicHeightMean_norm_sum_le {α : Type*} (I : Finset α) (F : α → ℝ → ℂ)
    (hF : ∀ i ∈ I, Continuous (F i)) {T : ℝ} (hT : 0 < T) :
    dyadicHeightMean (fun t => ‖∑ i ∈ I, F i t‖) T ≤
      ∑ i ∈ I, dyadicHeightMean (fun t => ‖F i t‖) T := by
  have h := dyadicHeightMean_mono (continuous_finsetSum I hF).norm
    (continuous_finsetSum I (fun i hi => (hF i hi).norm)) hT
    (fun t _ => norm_sum_le _ _)
  exact h.trans_eq (dyadicHeightMean_sum I (fun i t => ‖F i t‖)
    (fun i hi => (hF i hi).norm) T)

lemma averaged_cubic_dyadic_sum (I : Finset ℕ) (F : ℕ → ℝ → ℂ)
    (hF : ∀ i ∈ I, Continuous (F i)) {C t T : ℝ} (hC : 0 ≤ C) (ht : 0 < t) (hT : 0 < T)
    (hbound : ∀ j ∈ I, dyadicHeightMean (fun u => ‖F j u‖) T ≤
      C*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) :
    dyadicHeightMean (fun u => ‖∑ j ∈ I, F j u‖) T ≤
      C*SevenEighths.CubicDyadicDecay.decayConstant (1/3)*t^(-(1/3:ℝ)) := by
  have hs := SevenEighths.CubicDyadicDecay.decay_summable t (1/3) ht (by norm_num)
  have hb := SevenEighths.CubicDyadicDecay.dyadic_decay_bound t (1/3) ht (by norm_num) (by norm_num)
  calc
    _ ≤ ∑ j ∈ I, dyadicHeightMean (fun u => ‖F j u‖) T := dyadicHeightMean_norm_sum_le I F hF hT
    _ ≤ ∑ j ∈ I, C*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := Finset.sum_le_sum hbound
    _ = C*(∑ j ∈ I, ((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ C*(∑' j : ℕ, ((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum I (fun j _ => by positivity)) hC
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC

lemma continuous_poisson_series (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
    (β : Eisenstein → ℂ) (V : ℝ → ℂ) (A u : ℝ) {C t : ℝ} (ht : 0 < t)
    (hbound : ∀ j v, ‖finitePoissonContribution S (H j) β (u+v) V A‖ ≤
      C*(2:ℝ)^j/(1+t*2^j)^3) :
    Continuous (fun v => ∑' j : ℕ, finitePoissonContribution S (H j) β (u+v) V A) := by
  have hs := SevenEighths.CubicDyadicDecay.decay_summable t 1 ht (by norm_num)
  simp only [Real.rpow_one] at hs
  apply continuous_tsum (fun j => (finitePoissonContribution_continuous_height S (H j) β V A).comp
    (continuous_const.add continuous_id)) (hs.mul_left C)
  intro j v
  simpa only [Function.comp_apply,Pi.add_apply,id_eq,mul_div_assoc] using hbound j v

theorem height_poisson_dyadic_saving
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (I : Finset ℕ) (H : ℕ → Finset Eisenstein)
        (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → 0 < A →
      (∀ j ∈ I, 2*(2:ℝ)^j ≤ (L r)^(1+η)) → (∀ j, H j ⊆ frequencyDyad j) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      dyadicHeightMean (fun t => ‖∑ j ∈ I,
        finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e) (H j)
          (fullPrimeCoefficient R (W r) X) (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hbound⟩ := height_poisson_annulus_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k 3
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,L₀,m,hK,hbound⟩ := hbound L W hL hW hlo hhi
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨3*K*(2:ℝ)^(1/3:ℝ)*D,L₀,m,by positivity,?_⟩
  intro r X A I H e u T hL₀ hprod hX hA hI hH he heN hT hThi hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  let t := A/(27*(L r)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  let C₀ := K*A*L r*(2:ℝ)^(1/3:ℝ)/(1+Real.log (L r))^k
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  let F := fun j v => finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
    (H j) (fullPrimeCoefficient R (W r) X) (u+v) V A
  have hrow (j : ℕ) (hj : j ∈ I) :
      dyadicHeightMean (fun v => ‖F j v‖) T ≤ C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hJ : 0 < (2:ℝ)^j := by positivity
    have hJ₁ : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hb := hbound r X A (2*(2:ℝ)^j) ((2:ℝ)^j) (H j) e u T
      hL₀ hprod hX hA (by linarith) (hI j hj) hJ
      (fun h hh => ⟨(mem_frequencyDyad.mp (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
      (fun h hh => ⟨(frequencyDyad_norm (hH j hh)).1,(frequencyDyad_norm (hH j hh)).2⟩)
      he heN hT hThi hu
    have heq : A*(2:ℝ)^j/(27*(L r)^2) = t*2^j := by dsimp [t]; ring
    rw [heq,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le] at hb
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀,F]
    convert hb using 1 <;> ring
  have hs := averaged_cubic_dyadic_sum I F (fun j _ =>
    (finitePoissonContribution_continuous_height _ _ _ _ _).comp (continuous_const.add continuous_id))
    hC₀ ht hTp hrow
  apply hs.trans_eq
  calc
    _ = (K*(2:ℝ)^(1/3:ℝ)*D/(1+Real.log (L r))^k)*
        (A*L r*(A/(27*(L r)^2))^(-(1/3:ℝ))) := by dsimp [C₀,t,D]; ring
    _ = _ := by rw [cubic_poisson_scale hA hLp]; ring

end CubicFirstMoment

end

end OAI
