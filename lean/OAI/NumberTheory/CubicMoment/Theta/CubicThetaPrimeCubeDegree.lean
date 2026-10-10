import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeChartEquiv

namespace OAI

/-! Exact degree of the cubed-prime correspondence. The second chart
is explicitly identified with the residue ring modulo p^2. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeUpperParameterMap (p : Eisenstein) (r : Residues (p^2)) :
    cubicThetaPrimeCubeUpperParameter p :=
  ⟨Ideal.Quotient.mk (modulus (p^3)) (p*residueRepresentative (p^2) r),
    cubicThetaPrimeCubeRepresentative_dvd (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeCubeUpperParameterMap_injective {p : Eisenstein} (hp : p≠0) :
    Function.Injective (cubicThetaPrimeCubeUpperParameterMap p) := by
  intro r s h
  have he := congrArg Subtype.val h
  change Ideal.Quotient.mk (modulus (p^3)) (p*residueRepresentative (p^2) r)=
    Ideal.Quotient.mk (modulus (p^3)) (p*residueRepresentative (p^2) s) at he
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hd' : p*p^2 ∣ p*(residueRepresentative (p^2) r-residueRepresentative (p^2) s) := by
    convert hd using 1 <;> ring
  rw [mul_dvd_mul_iff_left hp] at hd'
  simpa only [residueRepresentative_spec] using residue_eq_of_dvd_sub hd'

lemma cubicThetaPrimeCubeUpperParameterMap_surjective (p : Eisenstein) :
    Function.Surjective (cubicThetaPrimeCubeUpperParameterMap p) := by
  intro r
  obtain ⟨m,hm⟩ := r.property
  refine ⟨Ideal.Quotient.mk (modulus (p^2)) m,?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (modulus (p^3))
    (p*residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m))=r.val
  have hd : p^2 ∣ residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
  have he : p^3 ∣ p*residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m)-p*m := by
    convert mul_dvd_mul_left p hd using 1 <;> ring
  exact (residue_eq_of_dvd_sub he).trans (by rw [←hm,residueRepresentative_spec])

def cubicThetaPrimeCubeUpperParameterEquiv {p : Eisenstein} (hp : p≠0) :
    Residues (p^2) ≃ cubicThetaPrimeCubeUpperParameter p :=
  Equiv.ofBijective (cubicThetaPrimeCubeUpperParameterMap p)
    ⟨cubicThetaPrimeCubeUpperParameterMap_injective hp,
      cubicThetaPrimeCubeUpperParameterMap_surjective p⟩

theorem cubicThetaPrimeCubeIwahori_index {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeIwahori (p^3)).index=(normNat p)^3+(normNat p)^2 := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Finite (cubicThetaPrimeCubeUpperParameter p) := by
    unfold cubicThetaPrimeCubeUpperParameter
    infer_instance
  rw [←(cubicThetaPrimeCubeTransversal_complement p).card_right,
    ←Nat.card_congr (cubicThetaPrimeCubeChartEquiv hp),Nat.card_sum,
    ←Nat.card_congr (cubicThetaPrimeCubeUpperParameterEquiv hp.2.ne_zero),
    residues_card (pow_ne_zero 3 hp.2.ne_zero),residues_card (pow_ne_zero 2 hp.2.ne_zero)]
  simp [pow_succ,normNat_mul]

end CubicFirstMoment

end

end OAI
