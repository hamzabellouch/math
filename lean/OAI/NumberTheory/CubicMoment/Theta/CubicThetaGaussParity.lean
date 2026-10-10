import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyDirichlet

namespace OAI

/-! Evenness of the genuine arithmetic Fourier coefficients follows by
negating the lower-left row and the frequency simultaneously. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_neg_c (c d : Eisenstein) :
    cubicThetaEisensteinWeight (-c) d=cubicThetaEisensteinWeight c d := by
  have hc : IsCoprime (-c) d ↔ IsCoprime c d :=
    ⟨fun h => by simpa using h.neg_left,fun h => h.neg_left⟩
  unfold cubicThetaEisensteinWeight
  rw [hc]
  split_ifs with h
  · exact cubicSymbol_neg h.1 c
  · rfl

lemma cubicThetaEisensteinGaussCoefficient_neg {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (-c) (-h)=cubicThetaEisensteinGaussCoefficient c h := by
  have hmod : modulus (3*(-c))=modulus (3*c) := by
    rw [show (3:Eisenstein)*(-c)= -(3*c) by ring]
    exact Ideal.span_singleton_neg (x:=(3*c:Eisenstein))
  let e : Residues (3*(-c)) ≃+* Residues (3*c) :=
    Ideal.quotEquivOfEq (R:=Eisenstein) hmod
  have hrep (x : Residues (3*(-c))) :
      Ideal.Quotient.mk (modulus (3*c)) (residueRepresentative (3*(-c)) x)=e x := by
    rw [← Ideal.quotEquivOfEq_mk hmod,residueRepresentative_spec]
  have hw (x : Residues (3*(-c))) :
      cubicThetaEisensteinResidueWeight (-c) x=cubicThetaEisensteinResidueWeight c (e x) := by
    rw [cubicThetaEisensteinResidueWeight,cubicThetaEisensteinWeight_neg_c]
    rw [← cubicThetaEisensteinResidueWeight_mk hc,hrep]
  unfold cubicThetaEisensteinGaussCoefficient
  rw [← e.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  rw [hw]
  congr 1
  have hphase := tracePhase_congr (mul_ne_zero (by norm_num : (3:Eisenstein)≠0) hc0) h
    ((hrep x).trans (residueRepresentative_spec (3*c) (e x)).symm)
  convert hphase using 1
  congr 2
  push_cast
  ring_nf

lemma cubicThetaFrequencyTerm_neg (s : ℂ) (h c : Eisenstein) :
    cubicThetaFrequencyTerm s (-h) (-c)=cubicThetaFrequencyTerm s h c := by
  have hn : norm (-c)=norm c := by simp only [norm,Subalgebra.coe_neg,Complex.normSq_neg]
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · have hc' : (3:Eisenstein)∣(-c) ∧ (-c)≠0 := by simpa using hc
    rw [cubicThetaFrequencyTerm,cubicThetaFrequencyTerm,ite_eq_left hc',ite_eq_left hc,
      cubicThetaEisensteinGaussCoefficient_neg hc.1 hc.2,hn]
  · have hc' : ¬((3:Eisenstein)∣(-c) ∧ (-c)≠0) := by simpa using hc
    simp only [cubicThetaFrequencyTerm,ite_eq_right hc',ite_eq_right hc]

theorem cubicThetaFrequencyDirichlet_neg (h : Eisenstein) (s : ℂ) :
    cubicThetaFrequencyDirichlet (-h) s=cubicThetaFrequencyDirichlet h s := by
  calc
    _ = ∑' c : Eisenstein, cubicThetaFrequencyTerm s (-h) (-c) :=
      ((Equiv.neg Eisenstein).tsum_eq (cubicThetaFrequencyTerm s (-h))).symm
    _ = _ := tsum_congr (cubicThetaFrequencyTerm_neg s h)

end CubicFirstMoment

end

end OAI
