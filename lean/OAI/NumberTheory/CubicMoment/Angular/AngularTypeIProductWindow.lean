import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductWindow

namespace OAI

/-! Fixed nonzero angular Type I for the actual product envelope. The
only analytic inputs are Voronoi, Montgomery--Vaughan, and the cited
fixed-angular Gamma strip bounds. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem angular_productTypeICutoffWindow_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hGamma : ∀ m : ℕ,
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)))
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
  obtain ⟨mp,mn,C,_hmp,_hmn,hC,hbound⟩ := angular_typeI_height_integral hVor hMV hMV0 hV
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
    (by simpa only [hRU] using hmass) (hGamma mp).1 (hGamma mp).2
    (hGamma mn).1 (hGamma mn).2
  have h₂ := hbound v P α R U T H (2*X₀) hR hU hsize' hT
    (by simpa only [hRU] using hTX) (by simpa only [hRU] using hrange) hP
    (by simpa only [hRU] using hmass) (hGamma mp).1 (hGamma mp).2
    (hGamma mn).1 (hGamma mn).2
  rw [hRU] at h₁ h₂
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
