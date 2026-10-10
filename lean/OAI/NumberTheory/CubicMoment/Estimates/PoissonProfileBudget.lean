import OAI.NumberTheory.CubicMoment.Estimates.NormMellinSeminorm
import OAI.NumberTheory.CubicMoment.Estimates.WideMellinControl
import OAI.NumberTheory.CubicMoment.Estimates.NormMassHeightControl

namespace OAI

/-! A quantitative profile budget is constructed from finitely many
Schwartz seminorms. It records only the two analytic costs used by the
Poisson argument; it is not an additional published input. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

def poissonProfileLogWidth : ℝ := 1+2*Real.log 2

lemma poissonProfileLogWidth_pos : 0 < poissonProfileLogWidth := by
  dsimp [poissonProfileLogWidth]
  have h : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

structure PoissonProfileBudget where
  V : ℝ → ℂ
  compact : HasCompactSupport V
  smooth : ContDiff ℝ ∞ V
  cost : ℝ
  cost_pos : 0 < cost
  mellin : ∀ ρ : ℝ, 0 ≤ ρ →
    (1+ρ)^3*(∫ s : ℝ, ‖normDenominatorMellinCoefficient poissonProfileLogWidth
      poissonProfileLogWidth_pos V compact smooth ρ s‖) ≤ cost
  radial : ∀ t : ℝ, 0 ≤ t → (1+t)^47*‖radialDualProfile V t‖ ≤ cost
  wide : ∀ ρ : ℝ, 0 ≤ ρ →
    (1+ρ)^3*(∫ s : ℝ, ‖wideGramMellinCoefficient poissonProfileLogWidth
      poissonProfileLogWidth_pos V compact smooth ρ s‖) ≤ cost

lemma PoissonProfileBudget.mellin_le (P : PoissonProfileBudget) {q : ℕ} (hq : q ≤ 3)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (1+ρ)^q*(∫ s : ℝ, ‖normDenominatorMellinCoefficient poissonProfileLogWidth
      poissonProfileLogWidth_pos P.V P.compact P.smooth ρ s‖) ≤ P.cost := by
  apply le_trans _ (P.mellin ρ hρ)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hq)
    (integral_nonneg (fun _ => _root_.norm_nonneg _))

lemma PoissonProfileBudget.radial_le (P : PoissonProfileBudget) {q : ℕ} (hq : q ≤ 47)
    (t : ℝ) (ht : 0 ≤ t) : (1+t)^q*‖radialDualProfile P.V t‖ ≤ P.cost :=
  (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hq)
    (_root_.norm_nonneg _)).trans (P.radial t ht)

lemma radialDualProfile_seminorm_control (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (q : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^q*‖radialDualProfile V t‖ ≤ 2^(2*q)*
      ((Finset.Iic (2*q,0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (normProfileFourierSchwartz V hV hV') := by
  let F := normProfileFourierSchwartz V hV hV'
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2*q,0)) (k := 2*q) (n := 0) (le_refl _) (le_refl _) F (Real.sqrt t : ℂ)
  simp only [norm_iteratedFDeriv_zero] at hb
  have hn : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : (1+t)^q ≤ (1+‖(Real.sqrt t : ℂ)‖)^(2*q) := by
    rw [hn,pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt ht,Real.sqrt_nonneg t]
  have he : F (Real.sqrt t : ℂ) = radialDualProfile V t :=
    normProfileFourierSchwartz_apply V hV hV' _
  have hh := mul_le_mul_of_nonneg_right hs (_root_.norm_nonneg (F (Real.sqrt t : ℂ)))
  rw [he] at hh hb
  exact hh.trans hb

/-- Every smooth compact profile has a budget bounded by the same finite
set of derivatives, chosen before the profile. -/
theorem exists_poissonProfileBudget_control :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V),
      ∃ P : PoissonProfileBudget, P.V = V ∧
        P.cost ≤ 1+C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz V hV hV') := by
  obtain ⟨I₀,C₀,hC₀,hM⟩ := normDenominatorMellinCoefficient_moment_control
    poissonProfileLogWidth poissonProfileLogWidth_pos 3 0
  obtain ⟨I₁,C₁,hC₁,hW⟩ := wideGramMellinCoefficient_moment_control
    poissonProfileLogWidth poissonProfileLogWidth_pos 3 0
  let J : Finset (ℕ × ℕ) := Finset.Iic (94,0)
  let I := (I₀ ∪ I₁) ∪ J
  let C := C₀+C₁+(2:ℝ)^94
  refine ⟨I,C,by dsimp [C]; positivity,?_⟩
  intro V hV hV'
  let F := normProfileFourierSchwartz V hV hV'
  let S := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hm (ρ : ℝ) (hρ : 0 ≤ ρ) :
      (1+ρ)^3*(∫ s : ℝ, ‖normDenominatorMellinCoefficient poissonProfileLogWidth
        poissonProfileLogWidth_pos V hV hV' ρ s‖) ≤ 1+C*S := by
    have hh := hM V hV hV' ρ hρ
    simp only [pow_zero,one_mul] at hh
    have hs : (I₀.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
      Seminorm.le_def.mp (Finset.sup_mono
        (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)) F
    have hb := hh.trans (mul_le_mul_of_nonneg_left hs hC₀.le)
    dsimp [C]
    nlinarith
  have hr (t : ℝ) (ht : 0 ≤ t) : (1+t)^47*‖radialDualProfile V t‖ ≤ 1+C*S := by
    have hh := radialDualProfile_seminorm_control V hV hV' 47 t ht
    have hsub : J ⊆ I := Finset.subset_union_right
    have hsup : J.sup (fun m => (SchwartzMap.seminorm ℝ m.1 m.2 : Seminorm ℝ 𝓢(ℂ,ℂ))) ≤
        I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) := Finset.sup_mono hsub
    have hs : (J.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
      Seminorm.le_def.mp hsup F
    rw [show (2:ℕ)*47 = 94 by omega] at hh
    dsimp only [J,F] at hs
    have hp : 0 ≤ (2:ℝ)^94 := pow_nonneg (by norm_num) _
    have hb := hh.trans (mul_le_mul_of_nonneg_left hs hp)
    have hcoeff : (2:ℝ)^94 ≤ C := by dsimp [C]; linarith
    exact hb.trans ((mul_le_mul_of_nonneg_right hcoeff hS).trans
      (le_add_of_nonneg_left (by norm_num)))
  have hw (ρ : ℝ) (hρ : 0 ≤ ρ) :
      (1+ρ)^3*(∫ s : ℝ, ‖wideGramMellinCoefficient poissonProfileLogWidth
        poissonProfileLogWidth_pos V hV hV' ρ s‖) ≤ 1+C*S := by
    have hh := hW V hV hV' ρ hρ
    simp only [pow_zero,one_mul] at hh
    have hs : (I₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F ≤ S :=
      Seminorm.le_def.mp (Finset.sup_mono
        (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)) F
    have hb := hh.trans (mul_le_mul_of_nonneg_left hs hC₁.le)
    dsimp [C]
    nlinarith
  exact ⟨⟨V,hV,hV',1+C*S,by positivity,hm,hr,hw⟩,rfl,le_rfl⟩

end CubicFirstMoment

end

end OAI
