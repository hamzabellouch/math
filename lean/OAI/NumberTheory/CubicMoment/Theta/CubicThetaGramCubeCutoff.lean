import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeFilter

namespace OAI

/-! Reindex the cube-divisible denominators with the two scaled positive
cutoffs. The finite norm cutoff is retained exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaGramDenominators_cube_scale {p : Eisenstein} (hp : primaryPrime p)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (d : Eisenstein) :
    d∈cubicThetaGramDenominators ε δ ↔
      p^3*d∈cubicThetaGramDenominators (ε/‖((p^3:Eisenstein):ℂ)‖)
        (δ/‖((p^3:Eisenstein):ℂ)‖) := by
  let r := ‖((p^3:Eisenstein):ℂ)‖
  have hr : 0<r := norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))
  have hN : norm (p^3)=r^2 := Complex.normSq_eq_norm_sq _
  have hscale : 1/((ε/r)*(δ/r))=norm (p^3)*(1/(ε*δ)) := by
    rw [hN]
    field_simp
  have hn : norm d≤1/(ε*δ) ↔ norm (p^3*d)≤1/((ε/r)*(δ/r)) := by
    rw [hscale,norm_mul_eq,mul_le_mul_iff_right₀ (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero))]
  have h3p : IsCoprime (3:Eisenstein) p :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))
  have hd : (3:Eisenstein)∣p^3*d ↔ (3:Eisenstein)∣d :=
    ⟨h3p.pow_right.dvd_of_dvd_mul_left,fun hd => dvd_mul_of_dvd_right hd _⟩
  have hz : p^3*d≠0 ↔ d≠0 := by
    simp only [ne_eq,mul_eq_zero,pow_ne_zero 3 hp.2.ne_zero,false_or]
  rw [cubicThetaGramDenominators_iff,cubicThetaGramDenominators_iff,hn,hd,hz]

lemma cubicThetaGramDenominators_cube_sum {p : Eisenstein} (hp : primaryPrime p)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (F : Eisenstein → ℂ) :
    (∑ c∈(cubicThetaGramDenominators (ε/‖((p^3:Eisenstein):ℂ)‖)
      (δ/‖((p^3:Eisenstein):ℂ)‖)).filter (fun c => p^3∣c),F c)=
      ∑ d∈cubicThetaGramDenominators ε δ,F (p^3*d) := by
  symm
  apply Finset.sum_bij (fun d _ => p^3*d)
  · intro d hd
    exact Finset.mem_filter.mpr
      ⟨(cubicThetaGramDenominators_cube_scale hp hε hδ d).mp hd,dvd_mul_right _ _⟩
  · intro d₁ _ d₂ _ he
    exact mul_left_cancel₀ (pow_ne_zero 3 hp.2.ne_zero) he
  · intro c hc
    obtain ⟨hc,a,rfl⟩ := Finset.mem_filter.mp hc
    exact ⟨a,(cubicThetaGramDenominators_cube_scale hp hε hδ a).mpr hc,rfl⟩
  · intro d _
    rfl

end CubicFirstMoment

end

end OAI
