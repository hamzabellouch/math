import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGluing

namespace OAI

/-! Determinant zeros give genuine nonzero global solutions with the two prescribed branches. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralMatching_zero_iff_glued (νp νm η : ℂ) (m : ℕ) (Q : ℝ → ℂ)
    (R : ℝ) (hR : 0 < R) (Rp Rm Op Om : ℝ → E₄)
    (hRp : ∀ r ∈ Ioc 0 R, HasDerivAt Rp
      (spectralPhysicalCircularField νp νm η m (Q r) r (Rp r)) r)
    (hRm : ∀ r ∈ Ioc 0 R, HasDerivAt Rm
      (spectralPhysicalCircularField νp νm η m (Q r) r (Rm r)) r)
    (hOp : ∀ r, R ≤ r → HasDerivAt Op
      (spectralPhysicalCircularField νp νm η m (Q r) r (Op r)) r)
    (hOm : ∀ r, R ≤ r → HasDerivAt Om
      (spectralPhysicalCircularField νp νm η m (Q r) r (Om r)) r)
    (hrank : LinearIndependent ℂ ![Rp R,Rm R])
    (horank : LinearIndependent ℂ ![Op R,Om R]) :
    spectralMatchingDeterminant (Rp R) (Rm R) (Op R) (Om R)=0 ↔
      ∃ (U : ℝ → E₄) (a b c d : ℂ),
        (∀ r, r ≤ R → U r=a • Rp r+b • Rm r) ∧
        (∀ r, R ≤ r → U r=c • Op r+d • Om r) ∧ U R ≠ 0 ∧
        (∀ r, 0 < r → HasDerivAt U
          (spectralPhysicalCircularField νp νm η m (Q r) r (U r)) r) := by
  rw [spectralMatchingDeterminant_zero_iff_intersection _ _ _ _ hrank horank]
  constructor
  · rintro ⟨a,b,c,d,he,hne⟩
    let F := fun r => a • Rp r+b • Rm r
    let G := fun r => c • Op r+d • Om r
    let V := fun r => spectralPhysicalCircularField νp νm η m (Q r) r
    let U := fun r => if r ≤ R then F r else G r
    have hF : ∀ r ∈ Ioc 0 R, HasDerivAt F (V r (F r)) r := by
      intro r hr
      apply (((hRp r hr).const_smul a).add ((hRm r hr).const_smul b)).congr_deriv
      dsimp only [F,V]
      rw [spectralPhysicalField_add,spectralPhysicalField_smul,spectralPhysicalField_smul]
    have hG : ∀ r, R ≤ r → HasDerivAt G (V r (G r)) r := by
      intro r hr
      apply (((hOp r hr).const_smul c).add ((hOm r hr).const_smul d)).congr_deriv
      dsimp only [G,V]
      rw [spectralPhysicalField_add,spectralPhysicalField_smul,spectralPhysicalField_smul]
    refine ⟨U,a,b,c,d,?_,?_,?_,spectral_ode_join F G V R hR hF hG he⟩
    · intro r hr
      exact ite_eq_left hr
    · intro r hr
      rcases hr.eq_or_lt with rfl | hr
      · simpa only [U,ite_eq_left le_rfl] using he
      · exact ite_eq_right hr.not_ge
    · simpa only [U,ite_eq_left le_rfl] using hne
  · rintro ⟨U,a,b,c,d,hinner,houter,hne,_hODE⟩
    refine ⟨a,b,c,d,?_,?_⟩
    · exact (hinner R le_rfl).symm.trans (houter R le_rfl)
    · rwa [← hinner R le_rfl]

end DefocusingNLS

end OAI
