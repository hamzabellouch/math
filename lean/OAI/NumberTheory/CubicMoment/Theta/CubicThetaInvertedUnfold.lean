import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowMellin

namespace OAI

/-! Absolute convergence and the literal primary-row unfolding at the
inverted cusp. The second coordinate is exactly three times a lattice point. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaInvertedAdmissible (cd : Eisenstein × Eisenstein) : Prop :=
  primary cd.1 ∧ (3:Eisenstein)∣cd.2 ∧ IsCoprime cd.1 cd.2

def cubicThetaInvertedPairEquiv :
    CubicThetaInvertedRow ≃ {cd // cubicThetaInvertedAdmissible cd} where
  toFun r := ⟨(r.c,r.d),r.c_primary,r.d_three,r.coprime⟩
  invFun cd := ⟨cd.val.1,cd.val.2,cd.property.1,cd.property.2.1,cd.property.2.2⟩
  left_inv r := by cases r; rfl
  right_inv cd := by apply Subtype.ext; rfl

def cubicThetaInvertedGridTerm (cd : Eisenstein × Eisenstein)
    (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if cubicThetaInvertedAdmissible cd then
    cubicSymbol cd.1 cd.2*
      ((p.2/(Complex.normSq ((cd.1:ℂ)*p.1+cd.2)+norm cd.1*p.2^2):ℝ):ℂ)^s
  else 0

lemma cubicThetaInvertedGridTerm_admissible
    (cd : {cd // cubicThetaInvertedAdmissible cd}) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaInvertedGridTerm cd.val p s=
      cubicThetaInvertedTerm (cubicThetaInvertedPairEquiv.symm cd) p s := by
  simp only [cubicThetaInvertedGridTerm,cd.property,ite_true,cubicThetaInvertedTerm,
    cubicThetaInvertedPairEquiv,CubicThetaInvertedRow.height]
  rfl

lemma cubicThetaInvertedTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun r : CubicThetaInvertedRow => cubicThetaInvertedTerm r p s) := by
  have ht := cubicThetaEisenstein_summable
    (cubicThetaMobius_height_pos (cubicThetaFullComplex cubicThetaFullInversion) hp) hs
  have he : (fun r : CubicThetaBottomRow => cubicThetaEisensteinTerm r
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s)=
      (fun r => cubicThetaInvertedTerm (cubicThetaInvertedRowEquiv r) p s) := by
    funext r
    exact cubicThetaEisensteinTerm_inverted r hp s
  rw [he] at ht
  exact cubicThetaInvertedRowEquiv.summable_iff.mp ht

lemma cubicThetaInvertedGrid_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun cd : Eisenstein × Eisenstein => cubicThetaInvertedGridTerm cd p s) := by
  have hsub := (cubicThetaInvertedTerm_summable hp hs).comp_injective
    cubicThetaInvertedPairEquiv.symm.injective
  have hg : Summable (fun cd : {cd // cubicThetaInvertedAdmissible cd} =>
      cubicThetaInvertedGridTerm cd.val p s) := by
    apply hsub.congr
    intro cd
    exact (cubicThetaInvertedGridTerm_admissible cd p s).symm
  apply (Subtype.val_injective.summable_iff
    (f:=fun cd => cubicThetaInvertedGridTerm cd p s) ?_).mp hg
  intro cd hcd
  by_cases hc : cubicThetaInvertedAdmissible cd
  · exact False.elim (hcd ⟨⟨cd,hc⟩,rfl⟩)
  · simp [cubicThetaInvertedGridTerm,hc]

theorem cubicThetaEisenstein_inverted_grid {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' cd : Eisenstein × Eisenstein, cubicThetaInvertedGridTerm cd p s := by
  rw [cubicThetaEisenstein_inverted hp]
  have hsup : Function.support (fun cd => cubicThetaInvertedGridTerm cd p s) ⊆
      {cd | cubicThetaInvertedAdmissible cd} := by
    intro cd hcd
    by_contra hc
    change ¬cubicThetaInvertedAdmissible cd at hc
    exact hcd (by simp [cubicThetaInvertedGridTerm,hc])
  calc
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd},
        cubicThetaInvertedTerm (cubicThetaInvertedPairEquiv.symm cd) p s :=
      (cubicThetaInvertedPairEquiv.symm.tsum_eq _).symm
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd}, cubicThetaInvertedGridTerm cd.val p s :=
      tsum_congr (fun cd => (cubicThetaInvertedGridTerm_admissible cd p s).symm)
    _ = _ := tsum_subtype_eq_of_support_subset hsup

lemma cubicThetaInvertedGridTerm_triple {c : Eisenstein} (hc : primary c)
    (a : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaInvertedGridTerm (c,3*a) p s=
      cubicSymbol c (3*a)*
        ((p.2/(Complex.normSq ((c:ℂ)*p.1+3*(a:ℂ))+norm c*p.2^2):ℝ):ℂ)^s := by
  by_cases hcop : IsCoprime c (3*a)
  · have h3 : ((3:Eisenstein):ℂ)=(3:ℂ) := rfl
    simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,hc,hcop,h3]
  · simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,hcop,
      cubicSymbol_eq_zero_of_not_isCoprime hc hcop]

end CubicFirstMoment

end

end OAI
