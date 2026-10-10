import OAI.NumberTheory.DirichletL.Descent.FirstCanonicalTail

namespace OAI

namespace SevenEighths.InverseMoment
open SecondPassArithmetic
noncomputable section

lemma first_tail_fixed_cap (K D E U₁ U₂ B G₁ G₂ P H : ℝ) (A : ℕ)
    (hK : 0<K) (hD : 0<D) (hE : 0<E) (hU₁ : 0<U₁) (hU₂ : 0<U₂) (hB : 1≤B)
    (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hP : 0≤P) (hH : 0≤H)
    (hKb : K≤B) (hKi : K⁻¹≤B) (hDb : D≤B) (hEb : E≤B) (h₁ : U₁≤B) (h₂ : U₂≤B) :
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A)) ≤
    65536*G₁*G₂*P*B^19/(1+H)^A := by
  have hB0 : 0≤B := zero_le_one.trans hB
  have hB2 : B≤B^2 := by nlinarith
  have hB3 : B≤B*B^2 := le_mul_of_one_le_right hB0 (one_le_pow₀ hB)
  have hb := firstTail_scalar_bound K D E U₁ U₂ B B G₁ G₂ P H A hK hD hE hU₁ hU₂
    hB0 hG₁ hG₂ hP hH (hDb.trans hB3) (hEb.trans hB2) h₁ h₂
  have hscale : 1+B^3*B^4/K≤2*B^8 := by
    calc
      _ ≤ 1+B^3*B^4*B := by rw [div_eq_mul_inv]; gcongr
      _ ≤ 2*B^8 := by have hh : 1≤B^8 := one_le_pow₀ hB; nlinarith [hh]
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (128*B)^2*(G₁*G₂*B)*P*(2*B^8)^2 := by gcongr
    _ = _ := by ring

theorem choose_first_tail_order (Lcap tau saving : ℝ) (hL : 0≤Lcap) (htau : 0<tau) :
    ∃ A : ℕ, ∀ (Z K D E U₁ U₂ G₁ G₂ P : ℝ),1≤Z →
      0<K → 0<D → 0<E → 0<U₁ → 0<U₂ → 0≤G₁ → 0≤G₂ → 0≤P →
      K≤Z^Lcap → K⁻¹≤Z^Lcap → D≤Z^Lcap → E≤Z^Lcap → U₁≤Z^Lcap → U₂≤Z^Lcap →
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+Z^tau)^A)) ≤
      65536*G₁*G₂*P*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((19*Lcap+saving)/tau)
  refine ⟨A,?_⟩
  intro Z K D E U₁ U₂ G₁ G₂ P hZ hK hD hE hU₁ hU₂ hG₁ hG₂ hP hKb hKi hDb hEb h₁ h₂
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := first_tail_fixed_cap K D E U₁ U₂ (Z^Lcap) G₁ G₂ P (Z^tau) A
    hK hD hE hU₁ hU₂ (Real.one_le_rpow hZ hL) hG₁ hG₂ hP
    (Real.rpow_pos_of_pos hz _).le hKb hKi hDb hEb h₁ h₂
  have hdecay : (Z^Lcap)^19/(1+Z^tau)^A≤Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^19/(Z^tau)^A := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) A)
      _ = Z^(19*Lcap-tau*(A:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp hA
        nlinarith
  apply hb.trans
  calc
    _ = (65536*G₁*G₂*P)*((Z^Lcap)^19/(1+Z^tau)^A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end SevenEighths.InverseMoment

end OAI
