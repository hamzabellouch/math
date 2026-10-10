import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingMatrix

namespace OAI

/-! A vanishing matching determinant is exactly a nonzero common boundary jet. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

private theorem pair_coefficients (X Y : E₄) (h : LinearIndependent ℂ ![X,Y])
    (a b : ℂ) (he : a • X+b • Y=0) : a=0 ∧ b=0 := by
  have hz := Fintype.linearIndependent_iff.mp h ![a,b]
    (by simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using he)
  exact ⟨hz 0,hz 1⟩

theorem spectralMatchingDeterminant_zero_iff_intersection (R₀ R₁ O₀ O₁ : E₄)
    (hR : LinearIndependent ℂ ![R₀,R₁]) (hO : LinearIndependent ℂ ![O₀,O₁]) :
    spectralMatchingDeterminant R₀ R₁ O₀ O₁=0 ↔
      ∃ a b c d : ℂ, a • R₀+b • R₁=c • O₀+d • O₁ ∧ a • R₀+b • R₁ ≠ 0 := by
  rw [spectralMatchingDeterminant_zero_iff]
  constructor
  · rintro ⟨a,b,c,d,he,hne⟩
    have he' : (a • R₀+b • R₁)+(c • O₀+d • O₁)=0 := by simpa only [add_assoc] using he
    refine ⟨a,b,-c,-d,?_,?_⟩
    · simpa only [neg_smul,← neg_add] using eq_neg_of_add_eq_zero_left he'
    · intro hx
      have hab := pair_coefficients R₀ R₁ hR a b hx
      rw [hx,zero_add] at he'
      have hcd := pair_coefficients O₀ O₁ hO c d he'
      rcases hne with ha | hb | hc | hd
      · exact ha hab.1
      · exact hb hab.2
      · exact hc hcd.1
      · exact hd hcd.2
  · rintro ⟨a,b,c,d,he,hx⟩
    refine ⟨a,b,-c,-d,?_,?_⟩
    · calc
        _ = (a • R₀+b • R₁)-(c • O₀+d • O₁) := by simp only [neg_smul]; abel
        _ = 0 := sub_eq_zero.mpr he
    · by_cases ha : a=0
      · right; left
        intro hb
        exact hx (by simp [ha,hb])
      · exact Or.inl ha

end DefocusingNLS

end OAI
