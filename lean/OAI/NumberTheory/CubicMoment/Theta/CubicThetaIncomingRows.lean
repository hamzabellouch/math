import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingForcing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinCusp
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspSeparation

namespace OAI

/-! The incoming cutoff series uses the actual primitive bottom rows.
Above the arithmetic cusp threshold at most one row contributes. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaBottomRow.high_height_c_zero (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 1<p.2) (hr : 1<r.height p) : r.c=0 := by
  have h : 1<(cubicThetaMobius (cubicThetaFullComplex r.completion.val) p).2 := by
    change 1<(cubicThetaBottomRow r.completion).height p
    rwa [r.completion_row]
  have hc := cubicThetaMobius_high_overlap r.completion.val hp h
  have he := congrArg CubicThetaBottomRow.c r.completion_row
  change r.completion.val 1 0=r.c at he
  exact he.symm.trans hc

theorem cubicThetaIncomingRows_unique {p : ℂ × ℝ} (hp : 0<p.2)
    {r t : CubicThetaBottomRow} (hr : 1<r.height p) (ht : 1<t.height p) : r=t := by
  let g := r.completion
  let q := cubicThetaMobius (cubicThetaPrincipalComplex g) p
  have hq : 0<q.2 := cubicThetaMobius_height_pos _ hp
  have hq1 : 1<q.2 := by
    change 1<(cubicThetaBottomRow r.completion).height p
    rwa [r.completion_row]
  have hinv : cubicThetaMobius (cubicThetaPrincipalComplex g⁻¹) q=p := by
    dsimp [q]
    rw [cubicThetaMobius_comp _ _ hp,← map_mul,inv_mul_cancel,map_one,cubicThetaMobius_one]
  have htq : 1<(t.rightMul g⁻¹).height q := by
    rw [CubicThetaBottomRow.height_rightMul _ _ hq,hinv]
    exact ht
  have htz : t.rightMul g⁻¹=cubicThetaZeroRow :=
    (CubicThetaBottomRow.c_zero_iff _).mp
      ((t.rightMul g⁻¹).high_height_c_zero hq1 htq)
  have hrz : r.rightMul g⁻¹=cubicThetaZeroRow := by
    calc
      _ = (cubicThetaBottomRow g).rightMul g⁻¹ := by
        rw [show cubicThetaBottomRow g=r from r.completion_row]
      _ = cubicThetaBottomRow (g*g⁻¹) := cubicThetaBottomRow_mul _ _
      _ = cubicThetaZeroRow := by rw [mul_inv_cancel]; rfl
  exact (CubicThetaBottomRow.rightMulEquiv g⁻¹).injective (hrz.trans htz.symm)

def cubicThetaIncomingTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicThetaCuspCutoff (r.height p)*cubicThetaEisensteinTerm r p s

lemma cubicThetaIncomingTerm_high {r : CubicThetaBottomRow} {p : ℂ × ℝ} {s : ℂ}
    (h : cubicThetaIncomingTerm r p s≠0) : 1<r.height p := by
  by_contra hn
  have hz := cubicThetaCuspCutoff_zero (le_of_not_gt hn)
  exact h (by simp only [cubicThetaIncomingTerm,hz,zero_mul])

lemma cubicThetaIncomingTerm_finite {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    (Function.support (fun r => cubicThetaIncomingTerm r p s)).Finite := by
  apply Set.Subsingleton.finite
  intro r hr t ht
  exact cubicThetaIncomingRows_unique hp
    (cubicThetaIncomingTerm_high hr) (cubicThetaIncomingTerm_high ht)

def cubicThetaIncomingEisenstein (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaIncomingTerm r p s

lemma cubicThetaIncomingTerm_translate (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingTerm (r.rightMul g) p s := by
  rw [cubicThetaIncomingTerm,cubicThetaIncomingTerm,
    ← CubicThetaBottomRow.height_rightMul r g hp,cubicThetaEisensteinTerm_translate r g hp s]
  ring

theorem cubicThetaIncomingEisenstein_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingEisenstein (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingEisenstein p s := by
  unfold cubicThetaIncomingEisenstein
  simp_rw [cubicThetaIncomingTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaIncomingTerm r p s)

theorem cubicThetaIncomingEisenstein_high {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaIncomingEisenstein p s=cubicThetaCuspCutoff p.2*(p.2:ℂ)^s := by
  have he : cubicThetaIncomingEisenstein p s=cubicThetaIncomingTerm cubicThetaZeroRow p s := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hc := r.high_height_c_zero hp (cubicThetaIncomingTerm_high hn)
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he,cubicThetaIncomingTerm,cubicThetaEisensteinTerm_zeroRow]
  simp [CubicThetaBottomRow.height,cubicThetaZeroRow,norm]

end CubicFirstMoment

end

end OAI
