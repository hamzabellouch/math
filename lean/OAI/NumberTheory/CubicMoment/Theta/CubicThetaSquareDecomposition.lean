import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMassFactorization

namespace OAI

/-! The unique primary squarefree-times-square decomposition, used only
for the coefficient-energy Euler quotient. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSquareNumerator (cd : CubicThetaPrimaryPair) : Eisenstein :=
  cd.val.1*cd.val.2^2

lemma cubicThetaSquareNumerator_primary (cd : CubicThetaPrimaryPair) :
    primary (cubicThetaSquareNumerator cd) := by
  exact primary_mul cd.property.1 (by
    simpa only [pow_two] using primary_mul cd.property.2.1 cd.property.2.1)

lemma cubicThetaSquareNumerator_injective : Function.Injective cubicThetaSquareNumerator := by
  intro cd ef he
  have hce := (idealExponentOf_squarefree_iff (primary_ne_zero cd.property.1)).mpr cd.property.2.2
  have hef := (idealExponentOf_squarefree_iff (primary_ne_zero ef.property.1)).mpr ef.property.2.2
  have hexp := congrArg idealExponentOf he
  change idealExponentOf (cd.val.1*cd.val.2^2)=idealExponentOf (ef.val.1*ef.val.2^2) at hexp
  rw [idealExponentOf_mul (primary_ne_zero cd.property.1) (pow_ne_zero 2 (primary_ne_zero cd.property.2.1)),
    idealExponentOf_mul (primary_ne_zero ef.property.1) (pow_ne_zero 2 (primary_ne_zero ef.property.2.1)),
    idealExponentOf_pow (primary_ne_zero cd.property.2.1),
    idealExponentOf_pow (primary_ne_zero ef.property.2.1)] at hexp
  have hp (p : EisensteinIdealPrime) :
      idealExponentOf cd.val.1 p=idealExponentOf ef.val.1 p ∧
      idealExponentOf cd.val.2 p=idealExponentOf ef.val.2 p := by
    have h := congrArg (fun ν : EisensteinIdealExponent => ν p) hexp
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at h
    have hc := hce p
    have hd := hef p
    omega
  apply Subtype.ext
  apply Prod.ext
  · apply primary_eq_of_idealExponentOf_eq cd.property.1 ef.property.1
    ext p
    exact (hp p).1
  · apply primary_eq_of_idealExponentOf_eq cd.property.2.1 ef.property.2.1
    ext p
    exact (hp p).2

lemma cubicThetaSquareNumerator_surjective (n : PrimaryArgument) :
    ∃ cd : CubicThetaPrimaryPair, cubicThetaSquareNumerator cd=n.val := by
  obtain ⟨d,c,he,hc⟩ := exists_sq_mul_squarefree n.val
  have hdc : d ∣ n.val := by rw [←he,pow_two,mul_assoc]; exact dvd_mul_right _ _
  have hcc : c ∣ n.val := by rw [←he]; exact dvd_mul_left _ _
  have hcp := primaryNormalize_primary (unit_residue_of_dvd_primary n.property hcc)
  have hdp := primaryNormalize_primary (unit_residue_of_dvd_primary n.property hdc)
  refine ⟨⟨(primaryNormalize c,primaryNormalize d),hcp,hdp,
    (primaryNormalize_associated c).squarefree_iff.mp hc⟩,?_⟩
  apply primary_associated_eq (primary_mul hcp (by simpa only [pow_two] using primary_mul hdp hdp))
    n.property
  change Associated (primaryNormalize c*primaryNormalize d^2) n.val
  rw [←he,mul_comm (d^2) c]
  exact ((primaryNormalize_associated c).mul_mul ((primaryNormalize_associated d).pow_pow)).symm

def cubicThetaSquareIndexEquiv : CubicThetaPrimaryPair ≃ PrimaryArgument :=
  Equiv.ofBijective (fun cd => ⟨cubicThetaSquareNumerator cd,cubicThetaSquareNumerator_primary cd⟩)
    ⟨fun _ _ h => cubicThetaSquareNumerator_injective (congrArg Subtype.val h),by
      intro n
      obtain ⟨cd,he⟩ := cubicThetaSquareNumerator_surjective n
      exact ⟨cd,Subtype.ext he⟩⟩

end CubicFirstMoment

end

end OAI
