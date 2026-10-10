import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularOuter
import OAI.NumberTheory.CubicMoment.Angular.AngularTypeIProductWindow

namespace OAI

/-! Actual nonzero-angular Type-I bounds for selected weights and the
literal product cutoff, derived without a Voronoi hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_typeI_selected_height_proved
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {η : ℝ} (hη : 0 < η)
    (d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ) (R U T : ℝ),
      1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U → 1 ≤ T →
      T ≤ (R*U)^2 →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^d →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖))/T ≤
          K*(R*U)^(1/2+η)*R^(3/4:ℝ)*Real.sqrt T := by
  have hh : 0 < η/2 := by positivity
  obtain ⟨C,hC,hmean⟩ :=
    hW.cubicTheta_inverted_angular_mean hMV hM ℓ hℓ hh (by norm_num : (0:ℝ) ≤ 2)
  obtain ⟨L,hL,hlog⟩ := typeI_log_power_bound d hh
  refine ⟨C*A*L*2^(1/4:ℝ),by positivity,?_⟩
  intro w S α R U T hR hU hsize hT hTX hS hα
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
        (by simpa only [Real.rpow_two] using hF)
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



theorem angular_typeI_selected_height_ranges_proved
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T : ℝ), 1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U →
        1 ≤ T → T ≤ (R*U)^2 →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
        ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖)+
          (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖))/T ≤
        C*(R*U)^(5/6-min (1/100) (3*κ/16)) := by
  let ε := min (1/100:ℝ) (κ/16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨C,hC,hbound⟩ := angular_typeI_selected_height_proved
     hMV hMV0 hW ℓ hℓ hε B hA
  refine ⟨C,hC,?_⟩
  intro w S α R U T hR hU hsize hT hTX hrange hS hmass
  have hX : 1 ≤ R*U := by nlinarith
  have hp : (R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤
      (R*U)^(5/6-min (1/100) (3*κ/16)) := by
    rcases hrange with ⟨hr,ht⟩ | ⟨hr,ht⟩
    · apply (typeI_first_fixed_gap hX (by positivity) (by positivity) hr ht
        (min_le_left _ _)).trans
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [min_le_left (1/100:ℝ) (3*κ/16)])
    · apply (typeI_second_fixed_gap hX (by positivity) (by positivity) hr ht hρ
        (min_le_right _ _)).trans
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [min_le_right (1/100:ℝ) (3*κ/16)])
  apply (hbound w S α R U T hR hU hsize hT hTX hS hmass).trans
  calc
    _ = C*((R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hC


theorem angular_typeI_height_integral_proved
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T H X₀ : ℝ), 1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U →
        1 ≤ T → T ≤ (R*U)^2 →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
          ‖typeIHeightIntegral w S α W ℓ U H T X₀‖ ≤
          C*(R*U)^(5/6-min (1/100) (3*κ/16)) := by
  obtain ⟨C,hC,hbound⟩ := angular_typeI_selected_height_ranges_proved
     hMV hMV0 hW ℓ hℓ hκ hρ B hA
  refine ⟨C,hC,?_⟩
  intro w S α R U T H X₀ hR hU hsize hT hTX hrange hS hmass
  apply (typeIHeightIntegral_le_mean hW w S α ℓ (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le hT) H X₀).trans
  simpa only [dyadicHeightMean,neg_mul] using
    hbound w S α R U T hR hU hsize hT hTX hrange hS hmass


theorem angular_productTypeICutoffWindow_proved
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : Eisenstein → γ) (P : Finset Eisenstein) (α : Eisenstein → ℂ)
        (X R U T H X₀ : ℝ),
        1 ≤ R → 1 ≤ U → R*U = X →
        max 2 (Real.exp (hW.radius+Real.log 2)) ≤ X → 1 ≤ T → T ≤ X^2 →
        0 < X₀ →
        ((R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
          (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) →
        (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ P, ‖α r‖) ≤ A*R*(Real.log X)^B →
        ‖productTypeICutoffWindow w P α W ℓ (Real.exp hW.radius) X U H T X₀‖ ≤
          C*X^(5/6-min (1/100) (3*κ/16)) := by
  let hV := hW.logDilate (Real.log 2) (Real.log_nonneg (by norm_num))
  obtain ⟨C,hC,hbound⟩ := angular_typeI_height_integral_proved hMV hMV0 hV
    ℓ hℓ hκ hρ B hA
  refine ⟨2*C,by positivity,?_⟩
  intro w P α X R U T H X₀ hR hU hRU hsize hT hTX hX₀ hrange hP hmass
  obtain ⟨v,hv⟩ := productTypeICutoffWindow_dilate hW w P α ℓ hR
    (zero_lt_one.trans_le hU) hRU hP
  rw [hv, typeICutoffWindow_endpoints hV v P α ℓ (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le hT) hX₀ H]
  have hsize' : max 2 (Real.exp hV.radius) ≤ R*U := by
    change max 2 (Real.exp (hW.radius+Real.log 2)) ≤ R*U
    simpa only [hRU] using hsize
  have h₁ := hbound v P α R U T H X₀ hR hU hsize' hT
    (by simpa only [hRU] using hTX) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  have h₂ := hbound v P α R U T H (2*X₀) hR hU hsize' hT
    (by simpa only [hRU] using hTX) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass)
  rw [hRU] at h₁ h₂
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))


end CubicFirstMoment

end

end OAI
