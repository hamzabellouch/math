import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFourier

namespace OAI

/-! The actual principal Eisenstein series as a sum of its explicitly
transformed rows, retaining the leading cusp term. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinRow_zero (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinRow 0 p s = (p.2:ℂ)^s := by
  unfold cubicThetaEisensteinRow
  calc
    _ = ∑' d : Eisenstein, if d = 1 then (p.2:ℂ)^s else 0 := by
      apply tsum_congr
      intro d
      by_cases hd : d = 1
      · subst d
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,
          primary_one,cubicSymbol_one_lower,norm,isCoprime_zero_left]
      · have hp : ¬(primary d ∧ IsCoprime (0:Eisenstein) d) := by
          intro h
          exact hd (primary_unit_eq_one (isCoprime_zero_left.mp h.2) h.1)
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hd,hp]
    _ = _ := by simp

lemma cubicThetaEisensteinRow_nondivisible {c : Eisenstein}
    (hc : ¬(3:Eisenstein) ∣ c) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinRow c p s = 0 := by
  simp [cubicThetaEisensteinRow,cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]

theorem cubicThetaEisenstein_fourier_rows {p : ℂ × ℝ} (hp : 0 < p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisenstein p s = Complex.Gamma s*(p.2:ℂ)^s+
      ∑' c : Eisenstein, if (3:Eisenstein) ∣ c ∧ c ≠ 0 then
        ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
          ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
            (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
      else 0 := by
  have hrow : Summable (fun c : Eisenstein => cubicThetaEisensteinRow c p s) :=
    (cubicThetaEisensteinGrid_summable hp hs).prod
  have he : cubicThetaEisenstein p s = ∑' c : Eisenstein, cubicThetaEisensteinRow c p s := by
    rw [cubicThetaEisenstein_eq_grid, (cubicThetaEisensteinGrid_summable hp hs).tsum_prod]
    rfl
  rw [he, hrow.tsum_eq_add_tsum_ite 0, cubicThetaEisensteinRow_zero, mul_add, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro c
  by_cases hc0 : c = 0
  · simp [hc0]
  · by_cases hc : (3:Eisenstein) ∣ c
    · simpa [hc0,hc] using cubicThetaEisensteinRow_fourier hc hc0 hp hs
    · simp [hc0,hc,cubicThetaEisensteinRow_nondivisible hc]

end CubicFirstMoment

end

end OAI
