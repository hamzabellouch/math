import OAI.NumberTheory.CubicMoment.Estimates.TypeISelectedHeight
import OAI.NumberTheory.CubicMoment.Estimates.TypeIRanges

namespace OAI

/-! The two actual height ranges in the prime decomposition.  The
constants remain uniform in the selected smooth weight and the pole
term has an arbitrary prescribed logarithmic saving. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

theorem typeI_selected_height_ranges
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B M : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T : ℝ), 1 ≤ R → 1 ≤ U → 1 ≤ Real.log (R*U) →
        Real.log (R*U) ≤ T →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
        ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticSmoothSum r (W (w r)) U t‖)+
          (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticSmoothSum r (W (w r)) U t‖))/T ≤
        C*(R*U)^(5/6-min (1/100) (3*κ/16))+
          E*(R*U)^(5/6:ℝ)/(Real.log (R*U))^M := by
  let ε := min (1/100:ℝ) (κ/16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨C,E,hC,hE,hbound⟩ := typeI_selected_height_of_published hW
    hF hGrowth hHB hε (B+M) B hA
  refine ⟨C,E,hC,hE,?_⟩
  intro w S α R U T hR hU hlog hLT hrange hS hmass
  have hT : 1 ≤ T := hlog.trans hLT
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
  have hpole := typeI_pole_log_saving (show 0 ≤ R*U by positivity) hlog hLT
    (show B+M ≤ B+M by exact le_rfl)
  apply (hbound w S α R U T hR hU hT hS hmass).trans
  apply add_le_add
  · calc
      _ = C*((R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hC
  · calc
      _ = E*((R*U)^(5/6:ℝ)*(Real.log (R*U))^B/T^(B+M)) := by ring
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hpole hE

theorem angular_typeI_selected_height_ranges
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4)
    (B : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ (mpos mneg : ℕ) (C : ℝ), 2 ≤ mpos ∧ 2 ≤ mneg ∧ 0 ≤ C ∧
      ∀ (w : Eisenstein → γ) (S : Finset Eisenstein) (α : Eisenstein → ℂ)
        (R U T : ℝ), 1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U →
        1 ≤ T → T ≤ (R*U)^2 →
        ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
          (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
        (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
        (∑ r ∈ S, ‖α r‖) ≤ A*R*(Real.log (R*U))^B →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mpos:ℝ)-1/2)) →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mpos:ℝ)-1/2)) →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mneg:ℝ)-1/2)) →
        AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mneg:ℝ)-1/2)) →
        ((∫ t in T..2*T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖)+
          (∫ t in -(2*T)..-T, ∑ r ∈ S, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖))/T ≤
        C*(R*U)^(5/6-min (1/100) (3*κ/16)) := by
  let ε := min (1/100:ℝ) (κ/16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨mp,mn,C,hmp,hmn,hC,hbound⟩ := angular_typeI_selected_height_of_published
    hV hMV hMV0 hW ℓ hℓ hε B hA
  refine ⟨mp,mn,C,hmp,hmn,hC,?_⟩
  intro w S α R U T hR hU hsize hT hTX hrange hS hmass hgmp hgpp hgmn hgpn
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
  apply (hbound w S α R U T hR hU hsize hT hTX hS hmass hgmp hgpp hgmn hgpn).trans
  calc
    _ = C*((R*U)^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hC

end CubicFirstMoment

end

end OAI
