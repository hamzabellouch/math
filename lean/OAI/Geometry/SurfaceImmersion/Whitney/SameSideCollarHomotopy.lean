import OAI.Geometry.SurfaceImmersion.Whitney.HomotopyCollarDerivative

namespace OAI

/-! A common positive transverse functional gives an explicit regular
linear homotopy of boundary vectors. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def linearTransverseHomotopy (a b : ℝ → W) (z : ℝ × ℝ) : W :=
  (1-z.1) • a z.2 + z.1 • b z.2

lemma linearTransverseHomotopy_smooth {a b : ℝ → W}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (linearTransverseHomotopy a b) :=
  ((contDiff_const.sub contDiff_fst).smul (ha.comp contDiff_snd)).add
    (contDiff_fst.smul (hb.comp contDiff_snd))

lemma same_side_collar_jet {c a b : ℝ → W} {t s : ℝ}
    (hv : deriv c t ≠ 0) (hs : s ∈ Icc (0:ℝ) 1)
    (L : W →L[ℝ] ℝ) (hLv : L (deriv c t) = 0)
    (hLa : 0 < L (a t)) (hLb : 0 < L (b t)) :
    Function.Injective (homotopyCollarJet c (linearTransverseHomotopy a b) s t 0 0) := by
  let A := linearTransverseHomotopy a b (s,t)
  have hLA : 0 < L A := by
    change 0 < L ((1-s) • a t + s • b t)
    rw [map_add,map_smul,map_smul]
    change 0 < (1-s)*L (a t)+s*L (b t)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hLa.le,
      mul_nonneg hs.1 hLb.le]
  have hzero : ∀ x : Base,
      homotopyCollarJet c (linearTransverseHomotopy a b) s t 0 0 x = 0 → x = 0 := by
    intro x hx
    have he : x 1 • deriv c t + x 0 • A = 0 := by
      simpa only [homotopyCollarJet,add_apply,ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.proj_apply,zero_smul,smul_zero,add_zero] using hx
    have hh := congrArg L he
    rw [map_add,map_smul,map_smul,hLv,map_zero] at hh
    have hx0 : x 0 = 0 := by
      change x 1*0+x 0*L A = 0 at hh
      exact (mul_eq_zero.mp (by simpa only [mul_zero,zero_add] using hh)).resolve_right hLA.ne'
    have hx1 : x 1 = 0 := by
      rw [hx0,zero_smul,add_zero] at he
      exact (smul_eq_zero.mp he).resolve_right hv
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub,hxy,sub_self]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
