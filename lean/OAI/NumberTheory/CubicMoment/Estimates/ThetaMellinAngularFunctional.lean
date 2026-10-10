import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplitAngular

namespace OAI

/-! The Mellin change of variables for an even-weight reciprocal identity. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma theta_mellin_functional_angular (k : ℕ) {f g : ℝ→ℂ} {ε : ℂ}
    (hFE : ∀ t : ℝ,0<t → f (1/t)=ε*(t:ℂ)^(2*k)*g t) (s : ℂ) :
    mellin f s=ε*mellin g (((2*k:ℕ):ℂ)-s) := by
  calc
    _ = mellin (fun t : ℝ => f t⁻¹) (-s) := by rw [mellin_comp_inv,neg_neg]
    _ = mellin (fun t : ℝ => ε • ((t:ℂ)^((2*k:ℕ):ℂ) • g t)) (-s) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [←one_div, hFE t ht, Complex.cpow_natCast]
      simp only [smul_eq_mul]
      ring
    _ = _ := by
      rw [mellin_const_smul,mellin_cpow_smul]
      simp only [smul_eq_mul,show -s+((2*k:ℕ):ℂ)=((2*k:ℕ):ℂ)-s by ring]

end CubicFirstMoment

end

end OAI
