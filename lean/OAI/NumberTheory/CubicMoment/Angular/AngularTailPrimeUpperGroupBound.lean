import OAI.NumberTheory.CubicMoment.Angular.AngularTailPrimeHighGroup
import OAI.NumberTheory.CubicMoment.Angular.AngularTailPrimeMiddleGroup
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeHeightRanges
import OAI.NumberTheory.CubicMoment.Estimates.PrimeBoxRange

namespace OAI

/-! Three overlapping length ranges bound the literal upper-height prime
product tail. The stopping exponent is chosen before arity and logarithmic
saving, and may be decreased to match the low-scale stopping argument. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_tailPrime_upper_group_bound_uniform
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
      ∀ (i j : ℕ) (s : Finset (Fin i ⊕ Fin j)) (k : ℕ),
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      X^(1/3-3*κ) ≤ B → B^2 ≤ 3*X →
      X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      X^(1/100:ℝ) ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (fun b => theta ℓ b*largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s b)
        (fun a => theta ℓ a*largeTupleOtherCoefficient ξ z.1.1 z.1.2 s a)
        primeProductEnvelope H T z.1.1‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨γ,hγ,hhigh⟩ := angular_tailPrime_high_group_uniform ℓ hHuxley hMV hC
  let κ₀ : ℝ := min (1/1000) (γ/(100*(3+γ)))
  have hden : 0 < 100*(3+γ) := by positivity
  have hκ₀ : 0 < κ₀ := lt_min (by norm_num) (div_pos hγ hden)
  have hκ₀small : κ₀ < 1/36 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle ξ hξ hξz i j s k
  have hκsmall : κ < 1/12 := by linarith
  have hκtiny : κ ≤ 1/1000 := hκle.trans (min_le_left _ _)
  have hκγ : κ*(3+γ) ≤ γ/100 := by
    have hh := mul_le_mul_of_nonneg_right (hκle.trans (min_le_right _ _))
      (show 0 ≤ 3+γ by positivity)
    have he : γ/(100*(3+γ))*(3+γ) = γ/100 := by field_simp
    rwa [he] at hh
  have hmargin : 1 < (1/3-3*κ)*(3+γ) := by nlinarith
  have hmargin₃ : 1 < (1/3-3*κ)*(3+(1:ℝ)) := by linarith
  have hquarter : (1/4:ℝ) ≤ 1/3-3*κ := by linarith
  let D : ℝ := 2*2^(i+j)
  let W : ℝ := 2*(2:ℝ)^s.card
  let Q : ℝ := (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})
  have hD : 0 < D := by dsimp [D]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  obtain ⟨K₁,B₁,hK₁,hb₁⟩ := hhigh i j s ξ k
  obtain ⟨K₂,B₂,hK₂,hb₂⟩ := angular_tailPrime_middle_group ℓ s hHuxley hMV hC k
  obtain ⟨η,G,K₃,B₃,m,hη,_hηone,hK₃,hb₃⟩ :=
    angular_tailPrime_hecke_group ℓ s hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ k
  let K := K₁+K₂+K₃
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K*3^(5/6:ℝ)/(1/4:ℝ)^k,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by linarith : 0 < 1/3-3*κ)).eventually_ge_atTop (max B₁ (max B₂ B₃)),
    eventually_tailPrime_small_localized_length hD (show 0 < 4*W^(3/2:ℝ) by positivity),
    eventually_tailPrime_small_group_length hD (show 0 < W^(27/25:ℝ) by positivity),
    eventually_tailPrime_small_high_upper hκ hκsmall hQ hmargin,
    eventually_tailPrime_small_high_upper hκ hκsmall (by norm_num : (0:ℝ) < 1) hmargin₃,
    eventually_tailPrime_middle_upper,
    eventually_tailPrime_middle_height hW,
    eventually_prime_box_range (show (0:ℝ) < 39/100-1/3 by norm_num) hη (i+j) G,
    eventually_tailPrime_power_height_log m,
    eventually_tailPrime_large_height_cap (by norm_num : (1/3000:ℝ) ≤ 1/1500)]
    with X hX hlarge hlocal hmiddle hlowerpower hcube hupper hheight hbox hlog hcap
  intro z H T hz
  dsimp only
  intro hBlo hBsq hABlo hABhi hrough hT hH hHX
  let B := largeTupleGroupLength s z
  let A := largeTupleGroupLength (Finset.univ\s) z
  have hBp : 0 < B := zero_lt_one.trans_le (largeTupleGroupLength_one s z)
  have hAp : 0 < A := zero_lt_one.trans_le (largeTupleGroupLength_one _ z)
  have hB₁ : B₁ ≤ B := (le_max_left _ _).trans (hlarge.trans hBlo)
  have hB₂ : B₂ ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans (hlarge.trans hBlo))
  have hB₃ : B₃ ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans (hlarge.trans hBlo))
  have hBquarter : X^(1/4:ℝ) ≤ B :=
    (Real.rpow_le_rpow_of_exponent_le hX hquarter).trans hBlo
  have hBX : B ≤ 3*X := by nlinarith [largeTupleGroupLength_one s z]
  have hHcube : H ≤ B^3 := hHX.trans (tailPrime_height_cube hX (by norm_num) hBquarter)
  have hA3 : A ≤ B^3 := by
    have hh := hcube A B hBlo hABhi
    rw [one_mul,show (2+(1:ℝ)) = ((3:ℕ):ℝ) by norm_num,Real.rpow_natCast] at hh
    exact hh
  have hscale : K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
      (K*3^(5/6:ℝ)/(1/4:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k :=
    triple_bilinear_nat_scale hX hAp.le hBquarter hK.le hABhi k
  apply le_trans _ hscale
  have hnonneg : 0 ≤ A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
    have hl := Real.log_nonneg (largeTupleGroupLength_one s z)
    positivity
  have henlarge {K' : ℝ} (hh : K' ≤ K) :
      K'*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_right hh hnonneg
  by_cases hsmall : B ≤ X^(39/100:ℝ)
  · have hlo : 4*(W*B)^(3/2:ℝ) ≤ A := by
      rw [Real.mul_rpow hW.le hBp.le]
      simpa only [mul_assoc] using hlocal A B hBp hABlo hsmall
    have hup : Q*A ≤ B^(2+γ) := hlowerpower A B hBlo hABhi
    have ht : (W*B)^(1/50:ℝ) ≤ T :=
      (hheight B hBp (hsmall.trans (Real.rpow_le_rpow_of_exponent_le hX (by norm_num)))).trans hT
    exact (hb₁ z H T hB₁ hlo hup hA3 ht hH hHcube).trans
      (henlarge (by dsimp [K]; linarith))
  · have hbig : X^(39/100:ℝ) ≤ B := le_of_lt (lt_of_not_ge hsmall)
    by_cases hmid : B ≤ X^(12/25:ℝ)
    · have hlo : (W*B)^(27/25:ℝ) ≤ A := by
        rw [Real.mul_rpow hW.le hBp.le]
        exact hmiddle A B hBp hABlo hmid
      have hup : A ≤ B^(19/10:ℝ) := hupper A B hBp hABhi hbig
      have ht : (W*B)^(1/50:ℝ) ≤ T := (hheight B hBp hmid).trans hT
      exact (hb₂ z H T hB₂ hlo hup ht hH hHcube).trans
        (henlarge (by dsimp [K]; linarith))
    · have hlargeB : X^(12/25:ℝ) ≤ B := le_of_lt (lt_of_not_ge hmid)
      have hrange := hbox A B hABlo hABhi hBsq (by
        simpa only [show (1/3+(39/100-1/3):ℝ) = 39/100 by ring] using hbig)
      have ht : (1+Real.log B)^m ≤ T :=
        (hlog B (largeTupleGroupLength_one s z) hBX).trans hT
      have hh : 2*Real.pi*H ≤ B^(7/20:ℝ) :=
        (mul_le_mul_of_nonneg_left hHX (by positivity)).trans (hcap B hlargeB)
      exact (hb₃ z H T hB₃ hrough hrange.1 hrange.2 ht hH hHcube hh).trans
        (henlarge (by dsimp [K]; linarith))

end CubicFirstMoment

end

end OAI
