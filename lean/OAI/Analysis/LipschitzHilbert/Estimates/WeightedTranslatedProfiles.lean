import OAI.Analysis.LipschitzHilbert.Fourier.SymbolWeights

namespace OAI

/-! Fixed polynomial weights absorb translations of normalized packet
profiles. The estimates are uniform before all packet locations. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def weightedTranslatedProfile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a : ℝ×ℝ) : SchwartzMap (ℝ×ℝ) ℂ :=
  symbolWeight q nu • F.compSubConstCLM ℂ a

theorem translatedProfile_seminorm (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a : ℝ×ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (F.compSubConstCLM ℂ a)≤
      (1+‖a‖)^k*(2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro x
  change ‖x‖^k*‖iteratedFDeriv ℝ n (fun z => F (z-a)) x‖≤_
  rw [iteratedFDeriv_comp_sub]
  have ht : ‖x‖≤‖x-a‖+‖a‖ := by
    convert norm_add_le (x-a) a using 1; simp
  have hp : ‖x‖≤(1+‖a‖)*(1+‖x-a‖) := by
    nlinarith only [ht, norm_nonneg a, norm_nonneg (x-a),
      mul_nonneg (norm_nonneg a) (norm_nonneg (x-a))]
  calc
    _ ≤ ((1+‖a‖)*(1+‖x-a‖))^k*‖iteratedFDeriv ℝ n F (x-a)‖ := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hp k) (norm_nonneg _)
    _ = (1+‖a‖)^k*((1+‖x-a‖)^k*‖iteratedFDeriv ℝ n F (x-a)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k,n)) le_rfl le_rfl F (x-a))
      (by positivity)

theorem weightedTranslatedProfile_seminorm (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a : ℝ×ℝ) (ha : ‖a‖≤‖nu‖)
    (k n : ℕ) (hk : k≤q) :
    SchwartzMap.seminorm ℝ k n (weightedTranslatedProfile F q nu a)≤
      2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F := by
  have hweight : symbolWeight q nu*(1+‖a‖)^k≤1 := by
    have hpow : (1+‖a‖)^k≤(1+‖nu‖)^q :=
      (pow_le_pow_left₀ (by positivity) (by linarith only [ha]) k).trans
        (pow_le_pow_right₀ (by linarith only [norm_nonneg nu]) hk)
    unfold symbolWeight
    calc
      _ ≤ ((1+‖nu‖)^q)⁻¹*((1+‖nu‖)^q) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  rw [weightedTranslatedProfile, map_smul_eq_mul]
  simp only [Real.norm_eq_abs, abs_of_pos (symbolWeight_pos q nu)]
  calc
    _ ≤ symbolWeight q nu*((1+‖a‖)^k*
        (2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F)) :=
      mul_le_mul_of_nonneg_left (translatedProfile_seminorm F a k n) (symbolWeight_pos q nu).le
    _ = (symbolWeight q nu*(1+‖a‖)^k)*
        (2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) := by ring
    _ ≤ 1*(2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := one_mul _

/-- Any fixed continuous seminorm has a uniformly weighted translation
bound. Its finite required order determines the weight exponent. -/
theorem weightedTranslatedProfile_bounded (F : SchwartzMap (ℝ×ℝ) ℂ)
    (P : Seminorm ℝ (SchwartzMap (ℝ×ℝ) ℂ)) (hP : Continuous P) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace, ∀ a : ℝ×ℝ, ‖a‖≤‖nu‖ →
      P (weightedTranslatedProfile F q nu a)≤C := by
  obtain ⟨s,A,_hA,hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ (ℝ×ℝ) ℂ) P hP
  let M : ℝ := ∑ i ∈ s, 2^i.1*(Finset.Iic i).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F
  have hM : 0≤M := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨s.sup Prod.fst, (A:ℝ)*M+1, by positivity, ?_⟩
  intro q hq nu a ha
  have hs : (s.sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ))
      (weightedTranslatedProfile F q nu a)≤M := by
    apply Seminorm.finset_sup_apply_le hM
    intro i hi
    exact (weightedTranslatedProfile_seminorm F q nu a ha i.1 i.2 ((Finset.le_sup hi).trans hq)).trans
      (Finset.single_le_sum (f := fun j : ℕ×ℕ =>
        2^j.1*(Finset.Iic j).sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ) F)
          (fun j _ => by positivity) hi)
  have hb := (Seminorm.le_def.mp hbound) (weightedTranslatedProfile F q nu a)
  change P (weightedTranslatedProfile F q nu a)≤
    (A:ℝ)*(s.sup (schwartzSeminormFamily ℝ (ℝ×ℝ) ℂ))
      (weightedTranslatedProfile F q nu a) at hb
  exact (hb.trans (mul_le_mul_of_nonneg_left hs A.coe_nonneg)).trans (by linarith)

end LipschitzHilbert.PacketRepresentation

end

end OAI
