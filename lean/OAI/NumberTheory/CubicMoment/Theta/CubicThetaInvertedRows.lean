import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSiegelReduction

namespace OAI

/-! Exact primitive rows at the inverted cusp. This identifies the
actual transformed Eisenstein series before taking its constant term. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

@[ext] structure CubicThetaInvertedRow where
  c : Eisenstein
  d : Eisenstein
  c_primary : primary c
  d_three : (3:Eisenstein) ∣ d
  coprime : IsCoprime c d

def cubicThetaInvertedRowEquiv : CubicThetaBottomRow ≃ CubicThetaInvertedRow where
  toFun r := ⟨r.d,-r.c,r.d_primary,dvd_neg.mpr r.c_three,r.coprime.symm.neg_right⟩
  invFun r := ⟨-r.d,r.c,dvd_neg.mpr r.d_three,r.c_primary,r.coprime.neg_right.symm⟩
  left_inv r := by ext <;> simp
  right_inv r := by ext <;> simp

def CubicThetaInvertedRow.height (r : CubicThetaInvertedRow) (p : ℂ × ℝ) : ℝ :=
  p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)

def cubicThetaInvertedTerm (r : CubicThetaInvertedRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicSymbol r.c r.d*(r.height p:ℂ)^s

theorem cubicThetaBottomRow_height_full (r : CubicThetaBottomRow)
    (g : SL(2,Eisenstein)) {p : ℂ × ℝ} (hp : 0<p.2) :
    r.height (cubicThetaMobius (cubicThetaFullComplex g) p)=
      p.2/(Complex.normSq ((((r.c*g 0 0+r.d*g 1 0):Eisenstein):ℂ)*p.1+
        ((r.c*g 0 1+r.d*g 1 1):Eisenstein))+
        norm (r.c*g 0 0+r.d*g 1 0)*p.2^2) := by
  have hc : r.completion.val 1 0=r.c := congrArg CubicThetaBottomRow.c r.completion_row
  have hd : r.completion.val 1 1=r.d := congrArg CubicThetaBottomRow.d r.completion_row
  have hmap : cubicThetaPrincipalComplex r.completion =
      cubicThetaFullComplex r.completion.val := by
    ext i j
    rfl
  calc
    _ = (cubicThetaMobius (cubicThetaFullComplex r.completion.val)
        (cubicThetaMobius (cubicThetaFullComplex g) p)).2 := by
      simpa only [r.completion_row,hmap] using cubicThetaBottomRow_height r.completion
        (cubicThetaMobius (cubicThetaFullComplex g) p)
    _ = (cubicThetaMobius (cubicThetaFullComplex (r.completion.val*g)) p).2 := by
      rw [map_mul,cubicThetaMobius_comp _ _ hp]
    _ = _ := by
      change p.2/(Complex.normSq ((((r.completion.val*g) 1 0:Eisenstein):ℂ)*p.1+
        (((r.completion.val*g) 1 1:Eisenstein):ℂ))+
        norm ((r.completion.val*g) 1 0)*p.2^2)=_
      simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hc,hd]

theorem cubicThetaBottomRow_height_inverted (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    r.height (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p)=
      (cubicThetaInvertedRowEquiv r).height p := by
  rw [cubicThetaBottomRow_height_full r _ hp]
  simp only [cubicThetaFullInversion,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_zero,mul_one,mul_neg_one,
    zero_add,add_zero]
  rfl

theorem cubicThetaEisensteinTerm_inverted (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisensteinTerm r
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      cubicThetaInvertedTerm (cubicThetaInvertedRowEquiv r) p s := by
  rw [cubicThetaEisensteinTerm,CubicThetaBottomRow.phase,star_star,
    cubicThetaBottomRow_height_inverted r hp]
  unfold cubicThetaInvertedTerm
  change cubicSymbol r.d r.c*_ = cubicSymbol r.d (-r.c)*_
  rw [cubicSymbol_neg r.d_primary]

theorem cubicThetaEisenstein_inverted {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' r : CubicThetaInvertedRow, cubicThetaInvertedTerm r p s := by
  unfold cubicThetaEisenstein
  simp_rw [cubicThetaEisensteinTerm_inverted _ hp]
  exact cubicThetaInvertedRowEquiv.tsum_eq
    (fun r : CubicThetaInvertedRow => cubicThetaInvertedTerm r p s)

end CubicFirstMoment

end

end OAI
