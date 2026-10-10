import OAI.NumberTheory.CubicMoment.Estimates.TypeIFinal
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAngularOuter

namespace OAI

/-! The Type-I height bounds with a weight selected independently for every
level. Constants are chosen before the selector, so subsequent decompositions
may use the original joint smooth-weight family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem typeI_selected_finite_levels {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1/12) (D : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (a : Eisenstein → ℂ)
      (R U T A : ℝ), 0 < R → 1 ≤ U → 1 ≤ T →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖a r‖) ≤ A →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W (w r)) U t‖)+
       (∫ t in -(2*T)..(-T), ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W (w r)) U t‖))/T ≤
        (C*U^(1/2+ε)*(2*R)^(1/4+2*ε)*Real.sqrt T+
          E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D)*A := by
  obtain ⟨C,E,hC,hE,hbound⟩ := uniform_metaplectic_dyadic_height
    hW hF hGrowth hHB hε hεsmall D
  refine ⟨C,E,hC,hE,?_⟩
  intro w S a R U T A hR hU hT hS hA
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let B := C*U^(1/2+ε)*(2*R)^(1/4+2*ε)*Real.sqrt T+
    E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D
  have hBn : 0 ≤ B := by dsimp [B]; positivity
  have hb (r : Eisenstein) (hr : r ∈ S) :
      ((∫ t in T..2*T, ‖metaplecticSmoothSum r (W (w r)) U t‖)+
       (∫ t in -(2*T)..(-T), ‖metaplecticSmoothSum r (W (w r)) U t‖))/T ≤ B := by
    obtain ⟨hprim,hlow,hup⟩ := hS r hr
    by_cases hs : Squarefree r
    · apply (hbound (w r) r hprim hs U hU T hT).trans
      have hp := Real.rpow_le_rpow (norm_nonneg r) hup (by linarith : 0 ≤ 1/4+2*ε)
      have hq := Real.rpow_le_rpow_of_nonpos hR hlow (by norm_num : (-1/6:ℝ) ≤ 0)
      dsimp [B]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (Real.rpow_nonneg hUp.le _)))
          (Real.sqrt_nonneg _)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq (mul_nonneg hE (Real.rpow_nonneg hUp.le _)))
          (pow_nonneg hTp.le _)
    · simp only [metaplecticSmoothSum_zero_of_not_squarefree hprim hs,norm_zero,
        intervalIntegral.integral_zero,add_zero,zero_div]
      exact hBn
  rw [dyadic_finite_norm_sum S a (fun r => metaplecticSmoothSum r (W (w r)) U)
    (fun r _ => metaplecticSmoothSum_continuous r (W (w r)) (hW.compact (w r)) hUp)]
  calc
    _ = ∑ r ∈ S, ‖a r‖*(((∫ t in T..2*T, ‖metaplecticSmoothSum r (W (w r)) U t‖)+
        (∫ t in -(2*T)..(-T), ‖metaplecticSmoothSum r (W (w r)) U t‖))/T) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r ∈ S, ‖a r‖*B := Finset.sum_le_sum
      (fun r hr => mul_le_mul_of_nonneg_left (hb r hr) (_root_.norm_nonneg _))
    _ = B*(∑ r ∈ S, ‖a r‖) := by rw [← Finset.sum_mul,mul_comm]
    _ ≤ B*A := mul_le_mul_of_nonneg_left hA hBn


theorem typeI_selected_height_of_published {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {ε : ℝ} (hε : 0 < ε) (D B : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (a : Eisenstein → ℂ)
      (R U T : ℝ), 1 ≤ R → 1 ≤ U → 1 ≤ T →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖a r‖) ≤ K*R*(Real.log (R*U))^B →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W (w r)) U t‖)+
       (∫ t in -(2*T)..(-T), ∑ r ∈ S, ‖a r‖*‖metaplecticSmoothSum r (W (w r)) U t‖))/T ≤
        C*(R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T+
        E*(R*U)^(5/6:ℝ)*(Real.log (R*U))^B/T^D := by
  let δ := min (ε/3) (1/24)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδs : δ < 1/12 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : 3*δ ≤ ε := by have := min_le_left (ε/3) (1/24:ℝ); dsimp [δ]; linarith
  obtain ⟨C,E,hC,hE,hbound⟩ := typeI_selected_finite_levels hW hF hGrowth hHB hδ hδs D
  obtain ⟨L,hL,hlog⟩ := typeI_log_power_bound B hδ
  refine ⟨C*2^(1/4+2*δ)*K*L,E*K,by positivity,by positivity,?_⟩
  intro w S a R U T hR hU hT hS ha
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  have hRX : R ≤ R*U := le_mul_of_one_le_right hRp.le hU
  have hA : (∑ r ∈ S, ‖a r‖) ≤ R*(K*(Real.log (R*U))^B) := by
    nlinarith [ha]
  have hb := hbound w S a R U T (R*(K*(Real.log (R*U))^B)) hRp hU hT hS hA
  rw [typeI_level_mass_scaling hRp hUp] at hb
  apply hb.trans
  have hmain := typeI_principal_log_bound hX hRp hRX hδ.le B (hlog _ hX)
  have hpow := Real.rpow_le_rpow_of_exponent_le hX
    (show 1/2+3*δ ≤ 1/2+ε by linarith)
  have hmain' : (R*U)^(1/2+δ)*R^(3/4+δ)*(Real.log (R*U))^B ≤
      L*(R*U)^(1/2+ε)*R^(3/4:ℝ) := hmain.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hL.le)
          (Real.rpow_nonneg hRp.le _))
  calc
    _ = (C*2^(1/4+2*δ)*K)*
        ((R*U)^(1/2+δ)*R^(3/4+δ)*(Real.log (R*U))^B)*Real.sqrt T+
        (E*K)*(R*U)^(5/6:ℝ)*(Real.log (R*U))^B/T^D := by ring
    _ ≤ (C*2^(1/4+2*δ)*K)*
        (L*(R*U)^(1/2+ε)*R^(3/4:ℝ))*Real.sqrt T+
        (E*K)*(R*U)^(5/6:ℝ)*(Real.log (R*U))^B/T^D := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmain' (by positivity)) (Real.sqrt_nonneg _)) le_rfl
    _ = _ := by ring


theorem angular_typeI_selected_height_of_published
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {η : ℝ} (hη : 0 < η)
    (d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ (mpos mneg : ℕ) (K : ℝ), 2 ≤ mpos ∧ 2 ≤ mneg ∧ 0 ≤ K ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ) (R U T : ℝ),
      1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U → 1 ≤ T →
      T ≤ (R*U)^2 →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^d →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mneg:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mneg:ℝ)-1/2)) →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖))/T ≤
          K*(R*U)^(1/2+η)*R^(3/4:ℝ)*Real.sqrt T := by
  have hh : 0 < η/2 := by positivity
  obtain ⟨mpos,mneg,C,hmp,hmn,hC,hmean⟩ :=
    hW.metaplectic_inverted_angular_mean hV hMV hM ℓ hℓ hh (by norm_num : (0:ℝ) ≤ 2)
  obtain ⟨L,hL,hlog⟩ := typeI_log_power_bound d hh
  refine ⟨mpos,mneg,C*A*L*2^(1/4:ℝ),hmp,hmn,by positivity,?_⟩
  intro w S α R U T hR hU hsize hT hTX hS hα hgmpos hgppos hgmneg hgpneg
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX2 : 2 ≤ R*U := (le_max_left _ _).trans hsize
  have hX : 1 ≤ R*U := by linarith
  have hXp : 0 < R*U := by positivity
  have hRX : R ≤ R*U := le_mul_of_one_le_right hRp.le hU
  have hUX : U ≤ R*U := le_mul_of_one_le_left hUp.le hR
  have hXsq : R*U ≤ (R*U)^2 := by nlinarith
  have hlow : (R*U)^(-(2:ℝ)) ≤ U := by
    calc
      _ ≤ (R*U)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = 1 := Real.rpow_zero _
      _ ≤ U := hU
  have hF : Real.exp hW.radius*U ≤ (R*U)^2 := by
    have hs := (le_max_right _ _).trans hsize
    nlinarith [mul_le_mul hs hUX hUp.le hXp.le]
  let B := C*Real.sqrt U*(R*U)^(η/2)*(2*R)^(1/4:ℝ)*Real.sqrt T
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (r : Eisenstein) (hr : r ∈ S) :
      ((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖))/T ≤ B := by
    obtain ⟨hprim,_,hupper⟩ := hS r hr
    have hnr := norm_nonneg r
    by_cases hsf : Squarefree r
    · have hbound := hmean (w r) r hprim hsf (R*U) U (Real.exp hW.radius*U) T
        hX hUp hT (by rw [Real.rpow_two]; nlinarith)
        (by simpa only [Real.rpow_two] using hTX) hlow
        (by simpa only [Real.rpow_two] using hUX.trans hXsq) le_rfl
        (by simpa only [Real.rpow_two] using hF) hgmpos hgppos hgmneg hgpneg
      rw [add_comm] at hbound
      apply hbound.trans
      dsimp [B]
      gcongr
    · simp only [metaplecticAngularSmoothSum_zero_of_not_squarefree hprim hsf,
        norm_zero,intervalIntegral.integral_zero,add_zero,zero_div]
      exact hB
  rw [dyadic_finite_norm_sum S α (fun r => metaplecticAngularSmoothSum r ℓ (W (w r)) U)
    (fun r _ => continuous_metaplecticAngularSmoothSum_of_cutoff r ℓ (W (w r)) hUp
      (le_refl (Real.exp hW.radius*U)) (hW.upper_support (w r)))]
  calc
    _ = ∑ r ∈ S, ‖α r‖*(((∫ t in T..2*T, ‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖))/T) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r ∈ S, ‖α r‖*B := Finset.sum_le_sum
      (fun r hr => mul_le_mul_of_nonneg_left (hb r hr) (_root_.norm_nonneg _))
    _ = B*(∑ r ∈ S, ‖α r‖) := by rw [←Finset.sum_mul,mul_comm]
    _ ≤ B*(A*R*(Real.log (R*U))^d) := mul_le_mul_of_nonneg_left hα hB
    _ = (C*A)*(Real.sqrt U*(2*R)^(1/4:ℝ)*R)*
        (R*U)^(η/2)*(Real.log (R*U))^d*Real.sqrt T := by dsimp [B]; ring
    _ ≤ (C*A)*(Real.sqrt U*(2*R)^(1/4:ℝ)*R)*
        (R*U)^(η/2)*(L*(R*U)^(η/2))*Real.sqrt T := by
      gcongr
      exact hlog _ hX
    _ = (C*A*L*2^(1/4:ℝ))*
        (Real.sqrt (R*U)*((R*U)^(η/2)*(R*U)^(η/2)))*R^(3/4:ℝ)*Real.sqrt T := by
      rw [angular_level_scaling hRp hUp]
      ring
    _ = _ := by
      rw [←Real.rpow_add hXp,show η/2+η/2=η by ring,
        Real.sqrt_eq_rpow,←Real.rpow_add hXp]


end CubicFirstMoment

end

end OAI
