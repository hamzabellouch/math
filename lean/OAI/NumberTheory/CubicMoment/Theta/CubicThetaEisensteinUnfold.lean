import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinResidues

namespace OAI

/-! Exact absolutely convergent unfolding from primitive rows to the
two Eisenstein lattice coordinates. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaAdmissiblePair (cd : Eisenstein × Eisenstein) : Prop :=
  (3:Eisenstein) ∣ cd.1 ∧ primary cd.2 ∧ IsCoprime cd.1 cd.2

def cubicThetaBottomRowEquiv : CubicThetaBottomRow ≃ {cd // cubicThetaAdmissiblePair cd} where
  toFun r := ⟨(r.c,r.d),r.c_three,r.d_primary,r.coprime⟩
  invFun cd := ⟨cd.val.1,cd.val.2,cd.property.1,cd.property.2.1,cd.property.2.2⟩
  left_inv r := by cases r; rfl
  right_inv cd := by apply Subtype.ext; rfl

def cubicThetaEisensteinGridTerm (cd : Eisenstein × Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if cubicThetaAdmissiblePair cd then
    cubicSymbol cd.2 cd.1*
      ((p.2/(Complex.normSq ((cd.1:ℂ)*p.1+cd.2)+norm cd.1*p.2^2):ℝ):ℂ)^s
  else 0

lemma cubicThetaEisensteinGridTerm_admissible (cd : {cd // cubicThetaAdmissiblePair cd})
    (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm cd.val p s =
      cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm cd) p s := by
  simp only [cubicThetaEisensteinGridTerm,cd.property,ite_true,cubicThetaEisensteinTerm,
    cubicThetaBottomRowEquiv,CubicThetaBottomRow.phase,CubicThetaBottomRow.height,star_star]
  rfl

lemma cubicThetaEisensteinGrid_summable {p : ℂ × ℝ} (hp : 0 < p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun cd : Eisenstein × Eisenstein => cubicThetaEisensteinGridTerm cd p s) := by
  have hsub : Summable (fun cd : {cd // cubicThetaAdmissiblePair cd} =>
      cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm cd) p s) :=
    (cubicThetaEisenstein_summable hp hs).comp_injective cubicThetaBottomRowEquiv.symm.injective
  have hgsub : Summable (fun cd : {cd // cubicThetaAdmissiblePair cd} =>
      cubicThetaEisensteinGridTerm cd.val p s) := by
    apply hsub.congr
    intro cd
    exact (cubicThetaEisensteinGridTerm_admissible cd p s).symm
  have hi : Summable ({cd | cubicThetaAdmissiblePair cd}.indicator
      (fun cd => cubicThetaEisensteinGridTerm cd p s)) :=
    (summable_subtype_iff_indicator (s := {cd | cubicThetaAdmissiblePair cd})).mp hgsub
  apply hi.congr
  intro cd
  by_cases hc : cubicThetaAdmissiblePair cd <;>
    simp [Set.indicator,cubicThetaEisensteinGridTerm,hc]

theorem cubicThetaEisenstein_eq_grid (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisenstein p s = ∑' cd : Eisenstein × Eisenstein, cubicThetaEisensteinGridTerm cd p s := by
  calc
    _ = ∑' cd : {cd // cubicThetaAdmissiblePair cd},
        cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm cd) p s :=
      (cubicThetaBottomRowEquiv.symm.tsum_eq (fun r => cubicThetaEisensteinTerm r p s)).symm
    _ = ∑' cd : {cd // cubicThetaAdmissiblePair cd}, cubicThetaEisensteinGridTerm cd.val p s := by
      apply tsum_congr
      intro cd
      exact (cubicThetaEisensteinGridTerm_admissible cd p s).symm
    _ = ∑' cd : Eisenstein × Eisenstein,
        if cubicThetaAdmissiblePair cd then cubicThetaEisensteinGridTerm cd p s else 0 :=
      tsum_subtype {cd | cubicThetaAdmissiblePair cd} (fun cd => cubicThetaEisensteinGridTerm cd p s)
    _ = _ := by
      apply tsum_congr
      intro cd
      by_cases h : cubicThetaAdmissiblePair cd <;> simp [cubicThetaEisensteinGridTerm,h]

theorem cubicThetaEisenstein_unfold {p : ℂ × ℝ} (hp : 0 < p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein p s =
      ∑' c : Eisenstein, ∑' d : Eisenstein, if (3:Eisenstein) ∣ c then
        cubicThetaEisensteinWeight c d*
          ((p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2):ℝ):ℂ)^s
      else 0 := by
  rw [cubicThetaEisenstein_eq_grid]
  rw [(cubicThetaEisensteinGrid_summable hp hs).tsum_prod]
  apply tsum_congr
  intro c
  apply tsum_congr
  intro d
  by_cases hc : (3:Eisenstein) ∣ c <;>
    by_cases hd : primary d ∧ IsCoprime c d <;>
      simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,cubicThetaEisensteinWeight,hc,hd]

end CubicFirstMoment

end

end OAI
