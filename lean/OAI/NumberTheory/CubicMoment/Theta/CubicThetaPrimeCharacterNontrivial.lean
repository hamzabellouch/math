import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilationUnfold

namespace OAI

/-! Nontriviality of the actual prime-level character. A nontrivial
residue-field value is lifted to a primary bottom row and completed in
the original level-three group. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrime_primary_nontrivial {p : Eisenstein} (hp : primaryPrime p) :
    ∃ d : Eisenstein, primary d ∧ IsCoprime p d ∧ cubicSymbol p d≠1 := by
  obtain ⟨x,hx⟩ := MulChar.ne_one_iff.mp (cubicResidueChar_ne_one hp)
  let v := residueRepresentative p (x : Residues p)
  have hv : IsCoprime p v := by
    apply isCoprime_of_residue_isUnit
    simpa only [v,residueRepresentative_spec] using x.isUnit
  obtain ⟨d,hd,hdp⟩ := residue_crt_one (primary_coprime_three hp.1) v
  refine ⟨d,hdp,isCoprime_of_residue_congr hd hv,?_⟩
  intro he
  apply hx
  have heq : cubicSymbol p v=cubicResidueChar p hp (x : Residues p) := by
    rw [cubicSymbol_prime hp]
    exact (cubicResidueChar_mk p hp v).symm.trans
      (congrArg (cubicResidueChar p hp) (residueRepresentative_spec p (x : Residues p)))
  rw [←heq,←cubicSymbol_congr (residue_eq_of_dvd_sub hd),he]

theorem cubicThetaPrimeIwahoriCharacter_nontrivial {p : Eisenstein}
    (hp : primaryPrime p) :
    ∃ g : cubicThetaPrimeIwahori p, cubicThetaPrimeIwahoriCharacter p hp g≠1 := by
  obtain ⟨d,hd,hpd,hχ⟩ := cubicThetaPrime_primary_nontrivial hp
  let r : CubicThetaBottomRow :=
    ⟨3*p,d,dvd_mul_right 3 p,hd,(primary_coprime_three hd).symm.mul_left hpd⟩
  let g : cubicThetaPrimeIwahori p :=
    ⟨r.completion,by
      have hc := congrArg CubicThetaBottomRow.c r.completion_row
      change p∣r.completion.val 1 0
      change r.completion.val 1 0=3*p at hc
      rw [hc]
      exact dvd_mul_left p 3⟩
  refine ⟨g,?_⟩
  have hr := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 1=d at hr
  have he : p∣(g.val.val 0 0)*d-1 := by
    have hg := cubicThetaPrincipalGroup_det g.val
    rw [show g.val.val 1 1=d from hr] at hg
    rw [show (g.val.val 0 0)*d-1=(g.val.val 0 1)*(g.val.val 1 0) by
      linear_combination hg]
    exact dvd_mul_of_dvd_right g.property _
  have hone : cubicSymbol p ((g.val.val 0 0)*d)=1 := by
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  rw [cubicSymbol_mul_upper hp.1] at hone
  intro htriv
  change cubicSymbol p (g.val.val 0 0)=1 at htriv
  rw [htriv,one_mul] at hone
  exact hχ hone

end CubicFirstMoment

end

end OAI
