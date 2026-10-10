import OAI.Analysis.CircleDomains.Rigidity.ConductivityContraction

namespace OAI

/-! Real and complex forms of the two-dimensional conductivity system.
These pointwise identities retain the signs and normalization used in the
Dirichlet-energy argument. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 def planarDz (aX aY vX vY : ℝ) : ℂ :=
  ((aX + vY) / 2 : ℝ) + ((vX - aY) / 2 : ℝ) * Complex.I

 def planarDbar (aX aY vX vY : ℝ) : ℂ :=
  ((aX - vY) / 2 : ℝ) + ((vX + aY) / 2 : ℝ) * Complex.I

 theorem conductivity_system_iff {k aX aY vX vY : ℝ} (hk : 0 ≤ k) :
    planarDbar aX aY vX vY = ((k - 1) / (k + 1) : ℝ) • star (planarDz aX aY vX vY) ↔
      aX = k * vY ∧ aY = -k * vX := by
  have hd : k + 1 ≠ 0 := by linarith
  have dzr (a b c d : ℝ) : (planarDz a b c d).re = (a + d) / 2 := by
    simp [planarDz]
  have dzi (a b c d : ℝ) : (planarDz a b c d).im = (c - b) / 2 := by
    simp [planarDz]
  have dbr (a b c d : ℝ) : (planarDbar a b c d).re = (a - d) / 2 := by
    simp [planarDbar]
  have dbi (a b c d : ℝ) : (planarDbar a b c d).im = (c + b) / 2 := by
    simp [planarDbar]
  have sr (q : ℝ) (z : ℂ) : (q • star z).re = q * z.re := by
    simp only [Complex.smul_re, Complex.star_def, Complex.conj_re, smul_eq_mul]
  have si (q : ℝ) (z : ℂ) : (q • star z).im = -(q * z.im) := by
    simp only [Complex.smul_im, Complex.star_def, Complex.conj_im, smul_eq_mul, mul_neg]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    rw [dbr, sr, dzr] at hr
    rw [dbi, si, dzi] at hi
    field_simp at hr hi
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    apply Complex.ext
    · rw [dbr, sr, dzr]
      field_simp
    · rw [dbi, si, dzi]
      field_simp
      ring

 theorem conductivity_jacobian {k aX aY vX vY : ℝ}
    (hx : aX = k * vY) (hy : aY = -k * vX) :
    aX * vY - aY * vX = k * (vX ^ 2 + vY ^ 2) := by
  rw [hx, hy]
  ring

 theorem conductivity_energy_identity {k aX aY vX vY : ℝ}
    (hx : aX = k * vY) (hy : aY = -k * vX) :
    vX ^ 2 + (vY - 1) ^ 2 + (k - 1) * (vX ^ 2 + vY ^ 2) =
      (aX * vY - aY * vX) - 2 * vY + 1 := by
  rw [conductivity_jacobian hx hy]
  ring

 theorem conductivity_dz_formula {k aX aY vX vY : ℝ}
    (hx : aX = k * vY) (hy : aY = -k * vX) :
    planarDz aX aY vX vY = ((k + 1) / 2 : ℝ) * ((vY : ℂ) + (vX : ℂ) * Complex.I) := by
  rw [hx, hy]
  apply Complex.ext <;> simp [planarDz] <;> ring

end CircleDomainRigidity

end

end OAI
