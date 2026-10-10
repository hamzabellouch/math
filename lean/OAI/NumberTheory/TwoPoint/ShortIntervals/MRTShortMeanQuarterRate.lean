import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortMeanHalfRate

namespace OAI

/-! The larger elementary frequency tail in the quarter-height kernel is
absorbed by doubling the already proved half-height scalar bound. -/

namespace TwoPointCorrelations

open Filter

theorem mrt_short_mean_quarter_rate (A : ℕ) (hA : 500000 ≤ A) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C L₀ H₀ : ℝ, 0<C ∧ 1 ≤ L₀ ∧ 1 ≤ H₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ H : ℝ, H₀ ≤ H → ∀ M : ℝ,
      Real.sqrt ((139968/(2*Real.pi)) *
        (12*(C₁*((Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H))^2+
            Real.exp (-M)+Real.log L/L^(1/100:ℝ)) +
          33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H)
            (minorArcFirstUpper H) (1/100))⁻¹ + 2*(minorArcFirstLower A H)⁻¹ +
          1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H)
            (minorArcFirstUpper H) (1/100))⁻¹*(1+minorArcFirstUpper H/H)) +
          2048*Real.exp 1/H^2)) +
        C₂*(Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H))  ≤
      C*(Real.log (Real.log H)/Real.log H + Real.exp (-M/2)+L^(-1/700:ℝ)) := by
  obtain ⟨C,L₀,H₀,hC,hL₀,hH₀,hmean⟩ := mrt_short_mean_half_rate A hA C₁ C₂ hC₁ hC₂
  obtain ⟨H₁,hH₁⟩ := eventually_atTop.mp (mrt_first_kernel_square_rate A hA)
  refine ⟨2*C,L₀,max H₀ H₁,by positivity,hL₀,hH₀.trans (le_max_left _ _),?_⟩
  intro L hL H hH M
  have hL1 : 1 ≤ L := hL₀.trans hL
  have hH0 : H₀ ≤ H := (le_max_left _ _).trans hH
  have hH1 : 1 ≤ H := hH₀.trans hH0
  have hHpos : 0 < H := by linarith
  have hLpos : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hm := hmean L hL H hH0 M
  have hr := (hH₁ H ((le_max_right _ _).trans hH)).2.1
  let R := Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H)
  let B := 12*(C₁*(R^2+Real.exp (-M)+Real.log L/L^(1/100:ℝ)) +
    33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H)
      (minorArcFirstUpper H) (1/100))⁻¹ + 2*(minorArcFirstLower A H)⁻¹ +
    1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H)
      (minorArcFirstUpper H) (1/100))⁻¹*(1+minorArcFirstUpper H/H))
  have hQ : 0 ≤ minorArcFirstUpper H := by dsimp [minorArcFirstUpper]; positivity
  have hP : 0 ≤ (minorArcFirstLower A H)⁻¹ := by dsimp [minorArcFirstLower]; positivity
  have hres : 0 ≤ (mrtBaseResolution (minorArcFirstLower A H)
      (minorArcFirstUpper H) (1/100))⁻¹ := by dsimp [mrtBaseResolution]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ (139968/(2*Real.pi):ℝ) := by positivity
  have henergy : (139968/(2*Real.pi))*(B+2048*Real.exp 1/H^2) ≤
      4*((139968/(2*Real.pi))*(B+512*Real.exp 1/H^2)) := by
    calc
      _ ≤ (139968/(2*Real.pi))*(B+2048*Real.exp 1/H^2) +
          3*((139968/(2*Real.pi))*B) :=
        le_add_of_nonneg_right (mul_nonneg (by norm_num) (mul_nonneg hK hB))
      _ = _ := by ring
  have hroot : Real.sqrt ((139968/(2*Real.pi))*(B+2048*Real.exp 1/H^2)) ≤
      2*Real.sqrt ((139968/(2*Real.pi))*(B+512*Real.exp 1/H^2)) := by
    apply (Real.sqrt_le_sqrt henergy).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  have hR : 0 ≤ C₂*R := mul_nonneg hC₂ hr
  change Real.sqrt ((139968/(2*Real.pi))*(B+2048*Real.exp 1/H^2))+C₂*R ≤ _
  change Real.sqrt ((139968/(2*Real.pi))*(B+512*Real.exp 1/H^2))+C₂*R ≤ _ at hm
  calc
    _ ≤ 2*(Real.sqrt ((139968/(2*Real.pi))*(B+512*Real.exp 1/H^2))+C₂*R) := by
      linarith
    _ ≤ 2*(C*(Real.log (Real.log H)/Real.log H+Real.exp (-M/2)+L^(-1/700:ℝ))) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
