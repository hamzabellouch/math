import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBottomRowAction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusGenerators

namespace OAI

/-! The cubic Eisenstein series on the principal group, before analytic
continuation. The bottom-row reindexing proves its actual automorphy;
no transformation formula for the theta coefficients is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrincipalComplex : cubicThetaPrincipalGroup →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (eisensteinRing.subtype : Eisenstein →+* ℂ)).comp
    cubicThetaPrincipalGroup.subtype

@[simp] lemma cubicThetaPrincipalComplex_apply (g : cubicThetaPrincipalGroup) (i j : Fin 2) :
    cubicThetaPrincipalComplex g i j = ((g.val i j:Eisenstein):ℂ) := rfl

def CubicThetaBottomRow.height (r : CubicThetaBottomRow) (p : ℂ × ℝ) : ℝ :=
  p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)

lemma cubicThetaBottomRow_height (g : cubicThetaPrincipalGroup) (p : ℂ × ℝ) :
    (cubicThetaBottomRow g).height p = (cubicThetaMobius (cubicThetaPrincipalComplex g) p).2 := rfl

lemma CubicThetaBottomRow.height_pos (r : CubicThetaBottomRow) {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < r.height p := by
  rw [←r.completion_row,cubicThetaBottomRow_height]
  exact cubicThetaMobius_height_pos _ hp

lemma CubicThetaBottomRow.height_rightMul (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    (r.rightMul g).height p = r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p) := by
  change (cubicThetaBottomRow (r.completion*g)).height p = _
  rw [cubicThetaBottomRow_height,map_mul]
  rw [←cubicThetaMobius_comp _ _ hp]
  rw [←cubicThetaBottomRow_height,r.completion_row]

def cubicThetaEisensteinTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  star r.phase*(r.height p:ℂ)^s

def cubicThetaEisenstein (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaEisensteinTerm r p s

lemma cubicThetaEisensteinTerm_translate (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0 < p.2) (s : ℂ) :
    cubicThetaEisensteinTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s =
      cubicThetaKubotaValue g*cubicThetaEisensteinTerm (r.rightMul g) p s := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g) = 1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaEisensteinTerm,cubicThetaEisensteinTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*(r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p):ℂ)^s) := by
      rw [hu,one_mul]
    _ = _ := by ring

/-- Automorphy follows by the exact bijection of primitive bottom rows.
Absolute convergence in the initial half-plane is proved separately. -/
theorem cubicThetaEisenstein_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0 < p.2) (s : ℂ) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s =
      cubicThetaKubotaValue g*cubicThetaEisenstein p s := by
  unfold cubicThetaEisenstein
  simp_rw [cubicThetaEisensteinTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaEisensteinTerm r p s)

end CubicFirstMoment

end

end OAI
