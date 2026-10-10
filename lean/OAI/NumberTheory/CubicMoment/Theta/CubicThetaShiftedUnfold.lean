import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedRowWeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedUnfold
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowMellin

namespace OAI

/-! Literal primary-row unfolding at every translated inverted cusp.
Absolute convergence follows from equality of the actual row norms. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedGridTerm (b : Eisenstein) (cd : Eisenstein × Eisenstein)
    (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if cubicThetaInvertedAdmissible cd then
    cubicSymbol (cd.1+b*cd.2) cd.2*
      ((p.2/(Complex.normSq ((cd.1:ℂ)*p.1+cd.2)+norm cd.1*p.2^2):ℝ):ℂ)^s
  else 0

lemma cubicThetaShiftedGridTerm_admissible (b : Eisenstein)
    (cd : {cd // cubicThetaInvertedAdmissible cd}) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaShiftedGridTerm b cd.val p s=
      cubicThetaShiftedInvertedTerm b (cubicThetaInvertedPairEquiv.symm cd) p s := by
  simp only [cubicThetaShiftedGridTerm,cd.property,ite_true,cubicThetaShiftedInvertedTerm,
    cubicThetaInvertedPairEquiv,CubicThetaInvertedRow.height]
  rfl

lemma cubicThetaShiftedInvertedTerm_norm (b : Eisenstein) (r : CubicThetaInvertedRow)
    (p : ℂ×ℝ) (s : ℂ) :
    ‖cubicThetaShiftedInvertedTerm b r p s‖=‖cubicThetaInvertedTerm r p s‖ := by
  unfold cubicThetaShiftedInvertedTerm cubicThetaInvertedTerm
  rw [norm_mul,norm_mul,norm_cubicSymbol_of_isCoprime r.c_primary r.coprime]
  have hn := cubicThetaShiftedRowPhase_norm b r
  change ‖cubicSymbol (r.c+b*r.d) r.d‖=1 at hn
  rw [hn]

lemma cubicThetaShiftedInvertedTerm_summable {p : ℂ×ℝ} (hp : 0<p.2)
    (b : Eisenstein) {s : ℂ} (hs : 2<s.re) :
    Summable (fun r : CubicThetaInvertedRow => cubicThetaShiftedInvertedTerm b r p s) := by
  apply Summable.of_norm
  simpa only [cubicThetaShiftedInvertedTerm_norm] using (cubicThetaInvertedTerm_summable hp hs).norm

lemma cubicThetaShiftedGrid_summable (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun cd : Eisenstein × Eisenstein => cubicThetaShiftedGridTerm b cd p s) := by
  have hsub := (cubicThetaShiftedInvertedTerm_summable hp b hs).comp_injective
    cubicThetaInvertedPairEquiv.symm.injective
  have hg : Summable (fun cd : {cd // cubicThetaInvertedAdmissible cd} =>
      cubicThetaShiftedGridTerm b cd.val p s) := by
    apply hsub.congr
    intro cd
    exact (cubicThetaShiftedGridTerm_admissible b cd p s).symm
  apply (Subtype.val_injective.summable_iff
    (f:=fun cd => cubicThetaShiftedGridTerm b cd p s) ?_).mp hg
  intro cd hcd
  by_cases hc : cubicThetaInvertedAdmissible cd
  · exact False.elim (hcd ⟨⟨cd,hc⟩,rfl⟩)
  · simp [cubicThetaShiftedGridTerm,hc]

theorem cubicThetaEisenstein_shifted_grid (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisenstein ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ∑' cd : Eisenstein × Eisenstein, cubicThetaShiftedGridTerm b cd p s := by
  rw [cubicThetaEisenstein_shiftedInverted hp b]
  have hsup : Function.support (fun cd => cubicThetaShiftedGridTerm b cd p s) ⊆
      {cd | cubicThetaInvertedAdmissible cd} := by
    intro cd hcd
    by_contra hc
    change ¬cubicThetaInvertedAdmissible cd at hc
    exact hcd (by simp [cubicThetaShiftedGridTerm,hc])
  calc
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd},
        cubicThetaShiftedInvertedTerm b (cubicThetaInvertedPairEquiv.symm cd) p s :=
      (cubicThetaInvertedPairEquiv.symm.tsum_eq _).symm
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd}, cubicThetaShiftedGridTerm b cd.val p s :=
      tsum_congr (fun cd => (cubicThetaShiftedGridTerm_admissible b cd p s).symm)
    _ = _ := tsum_subtype_eq_of_support_subset hsup

lemma cubicThetaShiftedGridTerm_triple (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    (a : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaShiftedGridTerm b (c,3*a) p s=
      cubicThetaShiftedRowWeight b c a*
        ((p.2/(Complex.normSq ((c:ℂ)*p.1+3*(a:ℂ))+norm c*p.2^2):ℝ):ℂ)^s := by
  by_cases hcop : IsCoprime c (3*a)
  · have h3 : ((3:Eisenstein):ℂ)=(3:ℂ) := rfl
    simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,cubicThetaShiftedRowWeight,hc,hcop,h3]
  · simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,hcop,
      cubicThetaShiftedRowWeight,
      cubicSymbol_eq_zero_of_not_isCoprime
        (cubicTheta_primary_add_three_mul hc ⟨a,rfl⟩ b)
        ((cubicTheta_coprime_add_left c (3*a) b).not.mpr hcop)]

end CubicFirstMoment

end

end OAI
