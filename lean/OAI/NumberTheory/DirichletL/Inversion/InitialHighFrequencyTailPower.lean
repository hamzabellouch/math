import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailScale

namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail

theorem initial_tail_power_cost (A : ℕ) (Z L Lcap m D τ : ℝ)
    (hZ : 1≤Z) (hL : 1≤L) (hcap : 0≤Lcap) (hsize : L≤Z^Lcap)
    (hm : -m≤Lcap) (hmd : m-D≤Lcap) :
    (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
      128^7*Z^(16*Lcap-τ*A) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hl : 0<L := zero_lt_one.trans_le hL
  have hbase : Z^(-4*Lcap)≤min 1 (Z^m/L^3) := by
    apply le_min
    · exact Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
    · calc
        _ = Z^(-Lcap)/(Z^Lcap)^3 := by
          rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
          congr 1
          norm_num
          ring
        _ ≤ Z^m/L^3 := by
          gcongr ; linarith
  calc
    _ ≤ (128*Z^Lcap)^7*Z^Lcap/((Z^(-4*Lcap))^2*(Z^τ)^A) := by
      gcongr ; linarith
    _ = 128^7*Z^(16*Lcap-τ*A) := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
        ←Real.rpow_mul_natCast hz.le]
      rw [mul_assoc,←Real.rpow_add hz,←Real.rpow_add hz,mul_div_assoc,
        ←Real.rpow_sub hz]
      congr 2
      norm_num
      ring

theorem initial_tail_rapid_order (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ A : ℕ, ∀ (Z L m D : ℝ), 1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap →
      -m≤Lcap → m-D≤Lcap →
      (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
        128^7*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((16*Lcap+saving)/τ)
  refine ⟨A,?_⟩
  intro Z L m D hZ hL hcap hsize hm hmd
  apply (initial_tail_power_cost A Z L Lcap m D τ hZ hL hcap hsize hm hmd).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have h := (div_lt_iff₀ hτ).mp hA
  nlinarith

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
