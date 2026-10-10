import OAI.NumberTheory.CubicMoment.Estimates.RadialTypeIHeight
import OAI.NumberTheory.CubicMoment.Estimates.TypeIHeightIntegral

namespace OAI

/-! The radial Type-I cutoff integral from the Voronoi formula alone,
in the two exact height ranges used by the main proof. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma typeI_range_height_le_square {X R T κ ρ : ℝ} (hX : 1 ≤ X) (hR : 1 ≤ R)
    (hρ : ρ ≤ κ/4)
    (hrange : (R ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
      (R ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+ρ))) : T ≤ X^2 := by
  rcases hrange with ⟨_,ht⟩ | ⟨hr,ht⟩
  · exact ht.trans (by simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/100:ℝ) ≤ 2))
  · by_cases hx : X = 1
    · simpa only [hx,Real.one_rpow,one_pow] using ht
    · have hXgt : 1 < X := lt_of_le_of_ne hX (Ne.symm hx)
      have he : (0:ℝ) ≤ 1/3-κ/2 := by
        apply (Real.rpow_le_rpow_left_iff hXgt).mp
        simpa only [Real.rpow_zero] using hR.trans hr
      exact ht.trans (by simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hX (by linarith : 1/6+ρ ≤ 2))

theorem radial_typeI_selected_ranges_of_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4) (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ) (R U T : ℝ),
      1 ≤ R → 1 ≤ U → 1 ≤ Real.log (R*U) → Real.log (R*U) ≤ T →
      ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
        (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
      ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r 0 (W (w r)) U t‖))/T ≤
        C*(R*U)^(5/6-min (1/100) (3*κ/16))+
          E*(R*U)^(5/6:ℝ)/(Real.log (R*U))^M := by
  let ε := min (1/100:ℝ) (κ/16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨C,E,hC,hE,hbound⟩ := radial_typeI_height_of_voronoi hV hMV hMV0 hW hε (B+M) B hA
  refine ⟨C,E,hC,hE,?_⟩
  intro w S α R U T hR hU hlog hLT hrange hS hmass
  have hT : 1 ≤ T := hlog.trans hLT
  have hX : 1 ≤ R*U := by nlinarith
  have hTX := typeI_range_height_le_square hX hR hρ hrange
  have hp : (R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤
      (R*U)^(5/6-min (1/100) (3*κ/16)) := by
    rcases hrange with ⟨hr,ht⟩ | ⟨hr,ht⟩
    · apply (typeI_first_fixed_gap hX (by positivity) (by positivity) hr ht
        (min_le_left _ _)).trans
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [min_le_left (1/100:ℝ) (3*κ/16)])
    · apply (typeI_second_fixed_gap hX (by positivity) (by positivity) hr ht hρ
        (min_le_right _ _)).trans
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [min_le_right (1/100:ℝ) (3*κ/16)])
  have hpole := typeI_pole_log_saving (show 0 ≤ R*U by positivity) hlog hLT
    (show B+M ≤ B+M from le_rfl)
  apply (hbound w S α R U T hR hU hT hTX hS hmass).trans
  apply add_le_add
  · calc
      _ = C*((R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hC
  · simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hpole hE

theorem radial_typeI_height_integral_of_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4) (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T H X₀ : ℝ), 1 ≤ R → 1 ≤ U → 1 ≤ Real.log (R*U) →
        Real.log (R*U) ≤ T →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
        ‖typeIHeightIntegral w S α W 0 U H T X₀‖ ≤
          C*(R*U)^(5/6-min (1/100) (3*κ/16))+
            E*(R*U)^(5/6:ℝ)/(Real.log (R*U))^M := by
  obtain ⟨C,E,hC,hE,hbound⟩ := radial_typeI_selected_ranges_of_voronoi hV hMV hMV0 hW hκ hρ B M hA
  refine ⟨C,E,hC,hE,?_⟩
  intro w S α R U T H X₀ hR hU hlog hLT hrange hS hmass
  apply (typeIHeightIntegral_le_mean hW w S α 0 (zero_lt_one.trans_le hU)
    (zero_lt_one.trans_le (hlog.trans hLT)) H X₀).trans
  simpa only [dyadicHeightMean,neg_mul] using
    hbound w S α R U T hR hU hlog hLT hrange hS hmass

end CubicFirstMoment

end

end OAI
