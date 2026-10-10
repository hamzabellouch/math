import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformShort
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformLong
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformNegativeLong
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticNegativeShort

namespace OAI

/-! Both signed completed means, with constants and far-left lines
chosen before every index in the given uniform smooth weight family. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_completed_angular_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ (m : ℕ) (K : ℝ), 2 ≤ m ∧ 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X → X ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)) →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) X t‖)/T ≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hshort⟩ := h.metaplectic_completed_short_mean hMV hM hη hB
  obtain ⟨m,D,hm,hD,hlong⟩ := h.metaplectic_completed_long_mean hV hMV hM ℓ hη hB
  refine ⟨m,C+D,hm,add_nonneg hC hD,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY hgm hgp
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hcommon : 0 ≤ Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by positivity
  by_cases hs : X ≤ Real.sqrt (norm r)*T^2
  · have hh := hshort i r hr ℓ Y X T 0 hY hX hT hXY hs
    simp only [add_zero] at hh
    apply hh.trans
    nlinarith only [mul_nonneg hD hcommon]
  · have hh := hlong i r hr hsr Y X T hY hX hT hRY hTY hYX (le_of_lt (lt_of_not_ge hs)) hgm hgp
    simp only [metaplecticMain,hℓ,ite_false,mul_zero,sub_zero] at hh
    apply hh.trans
    nlinarith only [mul_nonneg hC hcommon]


theorem UniformLogWeights.metaplectic_completed_negative_angular_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ (m : ℕ) (K : ℝ), 2 ≤ m ∧ 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X → X ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)) →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) X (-t)‖)/T ≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hshort⟩ := h.metaplectic_completed_short_mean hMV hM hη hB
  obtain ⟨m,D,hm,hD,hlong⟩ := h.metaplectic_completed_negative_long_mean hV hMV hM ℓ hη hB
  refine ⟨m,C+D,hm,add_nonneg hC hD,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY hgm hgp
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hcommon : 0 ≤ Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by positivity
  by_cases hs : X ≤ Real.sqrt (norm r)*T^2
  · have hh := hshort i r hr ℓ Y X T (-(3*T)) hY hX hT hXY hs
    have he := integral_reflected_height (fun t : ℝ => ‖metaplecticHeightCompleted r ℓ (W i) X t‖) T
    rw [he]
    simp only [sub_eq_add_neg]
    apply hh.trans
    nlinarith only [mul_nonneg hD hcommon]
  · have hh := hlong i r hr hsr Y X T hY hX hT hRY hTY hYX (le_of_lt (lt_of_not_ge hs)) hgm hgp
    simp only [metaplecticMain,hℓ,ite_false,mul_zero,sub_zero] at hh
    apply hh.trans
    nlinarith only [mul_nonneg hC hcommon]


theorem UniformLogWeights.metaplectic_completed_signed_angular_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ (mpos mneg : ℕ) (K : ℝ), 2 ≤ mpos ∧ 2 ≤ mneg ∧ 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X → X ≤ Y^B →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mneg:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mneg:ℝ)-1/2)) →
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r ℓ (W i) X t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) X t‖))/T ≤
          K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨mpos,C,hmpos,hC,hpositive⟩ :=
    h.metaplectic_completed_angular_mean hV hMV hM ℓ hℓ hη hB
  obtain ⟨mneg,D,hmneg,hD,hnegative⟩ :=
    h.metaplectic_completed_negative_angular_mean hV hMV hM ℓ hℓ hη hB
  refine ⟨mpos,mneg,C+D,hmpos,hmneg,add_nonneg hC hD,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY hgmpos hgppos hgmneg hgpneg
  have hp := hpositive i r hr hsr Y X T hY hX hT hRY hTY hYX hXY hgmpos hgppos
  have hn := hnegative i r hr hsr Y X T hY hX hT hRY hTY hYX hXY hgmneg hgpneg
  have he := intervalIntegral.integral_comp_neg (a := T) (b := 2*T)
    (fun t : ℝ => ‖metaplecticHeightCompleted r ℓ (W i) X t‖)
  rw [←he,add_div]
  calc
    _ ≤ D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
        C*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := add_le_add hn hp
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
