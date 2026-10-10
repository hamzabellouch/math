import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeUnitBranch
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueCount

namespace OAI

/-! One step in the finite three-level valuation partition used by the
cubed-prime trace. Multiplication by p parametrizes the nonunits exactly. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeNonunitPart (p : Eisenstein) (j : Fin 3) :=
  {r : Residues (p^(j.val+1)) // p∣residueRepresentative (p^(j.val+1)) r}

lemma cubicThetaPrimeCubeResidueStep_divisible {p x : Eisenstein} (j : Fin 3) (hx : p∣x) :
    p∣residueRepresentative (p^(j.val+1)) (Ideal.Quotient.mk (modulus (p^(j.val+1))) x) := by
  have he := residueRepresentative_spec (p^(j.val+1)) (Ideal.Quotient.mk (modulus (p^(j.val+1))) x)
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have ht := dvd_add ((dvd_pow_self p (Nat.succ_ne_zero j.val)).trans hd) hx
  simpa only [sub_add_cancel] using ht

def cubicThetaPrimeCubeResidueStepMap (p : Eisenstein) (j : Fin 3)
    (r : Residues (p^j.val)) : cubicThetaPrimeCubeNonunitPart p j :=
  ⟨Ideal.Quotient.mk (modulus (p^(j.val+1))) (p*residueRepresentative (p^j.val) r),
    cubicThetaPrimeCubeResidueStep_divisible j (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeCubeResidueStepMap_injective {p : Eisenstein} (hp : p≠0) (j : Fin 3) :
    Function.Injective (cubicThetaPrimeCubeResidueStepMap p j) := by
  intro r s h
  have he := congrArg Subtype.val h
  change Ideal.Quotient.mk (modulus (p^(j.val+1))) (p*residueRepresentative (p^j.val) r)=
    Ideal.Quotient.mk (modulus (p^(j.val+1))) (p*residueRepresentative (p^j.val) s) at he
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hd' : p*p^j.val ∣ p*(residueRepresentative (p^j.val) r-residueRepresentative (p^j.val) s) := by
    convert hd using 1 <;> ring
  rw [mul_dvd_mul_iff_left hp] at hd'
  simpa only [residueRepresentative_spec] using residue_eq_of_dvd_sub hd'

lemma cubicThetaPrimeCubeResidueStepMap_surjective (p : Eisenstein) (j : Fin 3) :
    Function.Surjective (cubicThetaPrimeCubeResidueStepMap p j) := by
  intro r
  obtain ⟨m,hm⟩ := r.property
  refine ⟨Ideal.Quotient.mk (modulus (p^j.val)) m,?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (modulus (p^(j.val+1)))
    (p*residueRepresentative (p^j.val) (Ideal.Quotient.mk (modulus (p^j.val)) m))=r.val
  have hd : p^j.val ∣ residueRepresentative (p^j.val) (Ideal.Quotient.mk (modulus (p^j.val)) m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
  have he : p^(j.val+1) ∣ p*residueRepresentative (p^j.val)
      (Ideal.Quotient.mk (modulus (p^j.val)) m)-p*m := by
    convert mul_dvd_mul_left p hd using 1 <;> ring
  exact (residue_eq_of_dvd_sub he).trans (by rw [←hm,residueRepresentative_spec])

def cubicThetaPrimeCubeResidueStepEquiv {p : Eisenstein} (hp : p≠0) (j : Fin 3) :
    Residues (p^j.val) ≃ cubicThetaPrimeCubeNonunitPart p j :=
  Equiv.ofBijective (cubicThetaPrimeCubeResidueStepMap p j)
    ⟨cubicThetaPrimeCubeResidueStepMap_injective hp j,
      cubicThetaPrimeCubeResidueStepMap_surjective p j⟩

def cubicThetaPrimeCubeResidueSplit {p : Eisenstein} (hp : primaryPrime p) (j : Fin 3) :
    ((Residues (p^(j.val+1)))ˣ ⊕ Residues (p^j.val)) ≃ Residues (p^(j.val+1)) := by
  classical
  let e : cubicThetaPrimeCubeNonunitPart p j ≃
      {r : Residues (p^(j.val+1)) // ¬IsUnit r} :=
    Equiv.subtypeEquivRight (fun r => ((cubicTheta_primePower_nonunit_iff hp.2 j.val r).trans
      (cubicTheta_residueReduction_eq_zero_iff _ r)).symm)
  exact (Equiv.sumCongr (cubicThetaUnitsEquivIsUnit _) ((cubicThetaPrimeCubeResidueStepEquiv hp.2.ne_zero j).trans e)).trans
    (Equiv.sumCompl IsUnit)

theorem cubicThetaPrimeCubeResidueSum_split {p : Eisenstein} (hp : primaryPrime p)
    (j : Fin 3) (f : Residues (p^(j.val+1)) → ℂ) :
    (∑' r, f r)=(∑' u : (Residues (p^(j.val+1)))ˣ, f u)+
      ∑' r : Residues (p^j.val), f (Ideal.Quotient.mk (modulus (p^(j.val+1)))
        (p*residueRepresentative (p^j.val) r)) := by
  let : Finite (Residues (p^j.val)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Finite (Residues (p^(j.val+1))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  rw [←(cubicThetaPrimeCubeResidueSplit hp j).tsum_eq,
    Summable.tsum_sum Summable.of_finite Summable.of_finite]
  rfl

lemma cubicThetaPrimeCubeResidueSum_three {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues (p^3) → ℂ) :
    (∑' r, f r)=(∑' u : (Residues (p^3))ˣ, f u)+
      ∑' r : Residues (p^2), f (Ideal.Quotient.mk (modulus (p^3))
        (p*residueRepresentative (p^2) r)) := by
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨2,by decide⟩ : Fin 3)
  simp only [Nat.reduceAdd] at hs
  exact hs f

lemma cubicThetaPrimeCubeResidueSum_two {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues (p^2) → ℂ) :
    (∑' r, f r)=(∑' u : (Residues (p^2))ˣ, f u)+
      ∑' r : Residues p, f (Ideal.Quotient.mk (modulus (p^2))
        (p*residueRepresentative p r)) := by
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨1,by decide⟩ : Fin 3)
  simp only [Nat.reduceAdd] at hs
  rw [show p^(1:ℕ)=p from pow_one p] at hs
  exact hs f

lemma cubicThetaPrimeCubeResidueSum_one {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues p → ℂ) :
    (∑' r, f r)=(∑' u : (Residues p)ˣ, f u)+
      ∑' r : Residues 1, f (Ideal.Quotient.mk (modulus p)
        (p*residueRepresentative 1 r)) := by
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨0,by decide⟩ : Fin 3)
  simp only [Nat.reduceAdd] at hs
  rw [show p^(1:ℕ)=p from pow_one p,show p^(0:ℕ)=1 from pow_zero p] at hs
  exact hs f

end CubicFirstMoment

end

end OAI
