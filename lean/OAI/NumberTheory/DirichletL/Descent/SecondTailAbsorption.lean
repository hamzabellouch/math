import OAI.NumberTheory.DirichletL.Descent.SecondSourceSize

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

lemma second_tail_fixed_cap (Y L cap B P H : ℝ) (order : ℕ)
    (hY : 0<Y) (hL : 0≤L) (hc : 1≤cap) (_hB : 0≤B) (hP : 0≤P) (hH : 0≤H)
    (hy : Y≤cap) (hyi : Y⁻¹≤cap) (hl : L≤cap) :
    (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+H)^order))≤
      (4*128^4)*B^2*P*cap^13/(1+H)^order := by
  have hc0 : 0≤cap := zero_le_one.trans hc
  have hscale : 1+L^3/Y≤2*cap^4 := by
    calc
      _ ≤ 1+cap^3*cap := by rw [div_eq_mul_inv]; gcongr
      _ ≤ _ := by have hh : 1≤cap^4 := one_le_pow₀ hc; nlinarith
  calc
    _ = (128*L)^4*B^2*Y*P*(1+L^3/Y)^2/(1+H)^order := by ring
    _ ≤ (128*cap)^4*B^2*cap*P*(2*cap^4)^2/(1+H)^order := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
    _ = _ := by ring

theorem choose_second_tail_order (Lcap tau saving : ℝ) (hL : 0≤Lcap) (htau : 0<tau) :
    ∃ order : ℕ,∀ Z Y L B P : ℝ,1≤Z → 0<Y → 0≤L → 0≤B → 0≤P →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+Z^tau)^order))≤
        (4*128^4)*B^2*P*Z^(-saving) := by
  obtain ⟨order,ho⟩ := exists_nat_gt ((13*Lcap+saving)/tau)
  refine ⟨order,?_⟩
  intro Z Y L B P hZ hY hL0 hB hP hy hyi hl
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := second_tail_fixed_cap Y L (Z^Lcap) B P (Z^tau) order hY hL0
    (Real.one_le_rpow hZ hL) hB hP (Real.rpow_pos_of_pos hz _).le hy hyi hl
  have hdecay : (Z^Lcap)^13/(1+Z^tau)^order≤Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^13/(Z^tau)^order := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) order)
      _ = Z^(13*Lcap-tau*(order:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp ho
        nlinarith
  apply hb.trans
  calc
    _ = ((4*128^4)*B^2*P)*((Z^Lcap)^13/(1+Z^tau)^order) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end SevenEighths.InverseMoment

end OAI
