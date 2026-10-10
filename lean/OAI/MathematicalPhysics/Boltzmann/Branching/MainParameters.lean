import OAI.MathematicalPhysics.Boltzmann.Approximation.CapUniformFiniteHorizon

namespace OAI

/-! # Concrete compatible parameters for the nonuniqueness construction -/
noncomputable section
open scoped ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum

structure ConstructionParameters where
  s₀ : ℝ
  η : ℝ
  K : ℝ
  α : ℝ
  γ : ℝ
  d₀ : ℝ
  q : ℝ
  scale_pos : 0 < s₀
  scale_le : s₀ ≤ 1/8
  eta_pos : 0 < η
  eta_le : η ≤ Real.log 2
  density_pos : 0 < K
  alpha_pos : 0 < α
  alpha_le : α ≤ 1/4
  gamma_pos : 0 < γ
  width_pos : 0 < d₀
  width_le : d₀ ≤ 1
  width_small : d₀*(1/8:ℝ)^10 ≤ 1/64
  comparison_small : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1
  q_lower : 1 < q
  q_upper : q < 2
  finite_horizon : ∀ (F : ShrinkingCapFamily s₀ η K α γ d₀ q) (S : AttainedCapSequence F)
    (E : AttainedCapSequence.HotPairExtraction S), E.horizon < ⊤

theorem exists_construction_parameters
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) : Nonempty ConstructionParameters := by
  obtain ⟨_,_,A₀,ε,γ₀,_,_,_,_,hA₀,hε,_,hγ₀,hfinite⟩ :=
    AttainedCapSequence.uniform_finite_horizon_parameters
  let K := 1+480*(8*A₀)/ε
  have hK : 0 < K := by dsimp [K]; positivity
  let C := JetComparisonCoefficient.coefficient K
  have hC : 1 ≤ C := JetComparisonCoefficient.coefficient_ge_one hK.le
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let d₀ := (2*C)⁻¹
  have hd : 0 < d₀ := inv_pos.mpr (by positivity)
  have hdmax : d₀ ≤ 1 := (inv_le_one₀ (by positivity : 0 < 2*C)).mpr (by linarith)
  have hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64 :=
    (mul_le_mul_of_nonneg_right hdmax (by positivity)).trans (by norm_num)
  have hc : C*d₀ = 1/2 := by dsimp [d₀]; field_simp
  have hsmall : JetComparisonCoefficient.coefficient K*d₀*(1/8:ℝ)^9 ≤ 1 := by
    change C*d₀*(1/8:ℝ)^9 ≤ 1
    rw [hc]
    norm_num
  let η := min (Real.log 2) (Real.log (1+ε/20))
  have hη : 0 < η := lt_min (Real.log_pos (by norm_num)) (Real.log_pos (by linarith))
  have hηmax : η ≤ Real.log 2 := min_le_left _ _
  have hηsmall : η ≤ Real.log (1+ε/20) := min_le_right _ _
  let α := min ε (1/4)
  have hα : 0 < α := lt_min hε (by norm_num)
  have hαmax : α ≤ 1/4 := min_le_right _ _
  have hKlarge : 480*(8*A₀) ≤ ε*K := by
    have he : ε*K = ε+480*(8*A₀) := by dsimp [K]; field_simp
    rw [he]
    linarith
  refine ⟨⟨1/8,η,K,α,γ₀,d₀,3/2,by norm_num,le_rfl,hη,hηmax,hK,hα,hαmax,hγ₀,
    hd,hdmax,hwidth,hsmall,by norm_num,by norm_num,?_⟩⟩
  intro F S E
  exact hfinite hDP hcarleman hGLPS hMityagin E (by norm_num) le_rfl hη hηmax hK hα hαmax
    hγ₀ hd hdmax hsmall (by norm_num) (by norm_num) hηsmall (min_le_left _ _) le_rfl hKlarge

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
