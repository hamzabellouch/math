import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeLowerValue

namespace OAI

/-! The literal lower-chart sum split into its three exact prime
valuations and its zero class. All reductions preserve the sharp modulus. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaResiduesOne_tsum (c : ℂ) : (∑' _ : Residues 1,c)=c := by
  let : Finite (Residues (1:Eisenstein)) := finite_residues one_ne_zero
  let : Fintype (Residues (1:Eisenstein)) := Fintype.ofFinite _
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,
    residues_card one_ne_zero,normNat_one,one_nsmul]

lemma cubicThetaPrimeCubePeriodic_sum {p : Eisenstein} (hp : primaryPrime p)
    (G : Eisenstein → ℂ) (hG : ∀ m n, p^3∣m-n → G m=G n) :
    (∑' r : Residues (p^3), G (residueRepresentative (p^3) r))=
      G 0+
      (∑' u : (Residues (p^3))ˣ, G (residueRepresentative (p^3) (u : Residues (p^3))))+
      (∑' u : (Residues (p^2))ˣ, G (p*residueRepresentative (p^2) (u : Residues (p^2))))+
      (∑' u : (Residues p)ˣ, G (p^2*residueRepresentative p (u : Residues p))) := by
  have hc0 (m : Eisenstein) :
      G (residueRepresentative (p^3) (Ideal.Quotient.mk (modulus (p^3)) m))=G m := by
    apply hG
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
  have hc1 (m : Eisenstein) :
      G (p*residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m))=G (p*m) := by
    apply hG
    have hd : p^2∣residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m)-m :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
    convert mul_dvd_mul_left p hd using 1 <;> ring
  have hc2 (m : Eisenstein) :
      G (p^2*residueRepresentative p (Ideal.Quotient.mk (modulus p) m))=G (p^2*m) := by
    apply hG
    have hd : p∣residueRepresentative p (Ideal.Quotient.mk (modulus p) m)-m :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
    convert mul_dvd_mul_left (p^2) hd using 1 <;> ring
  have hz (m : Eisenstein) : G (p^3*m)=G 0 := by
    apply hG
    simp only [sub_zero]
    exact dvd_mul_right _ _
  have h3 := cubicThetaPrimeCubeResidueSum_three hp
    (fun r : Residues (p^3) => G (residueRepresentative (p^3) r))
  simp_rw [hc0] at h3
  have h2 := cubicThetaPrimeCubeResidueSum_two hp
    (fun r : Residues (p^2) => G (p*residueRepresentative (p^2) r))
  simp_rw [hc1] at h2
  have h2' : (∑' r : Residues (p^2),G (p*residueRepresentative (p^2) r))=
      (∑' u : (Residues (p^2))ˣ,G (p*residueRepresentative (p^2) (u : Residues (p^2))))+
      ∑' r : Residues p,G (p^2*residueRepresentative p r) := by
    simpa only [pow_one,pow_two,mul_assoc] using h2
  have h1 := cubicThetaPrimeCubeResidueSum_one hp
    (fun r : Residues p => G (p^2*residueRepresentative p r))
  simp_rw [hc2] at h1
  have h1' : (∑' r : Residues p,G (p^2*residueRepresentative p r))=
      (∑' u : (Residues p)ˣ,G (p^2*residueRepresentative p (u : Residues p)))+G 0 := by
    have he (m : Eisenstein) : G (p^2*(p*m))=G 0 := by
      rw [show p^2*(p*m)=p^3*m by ring]
      exact hz m
    simp_rw [he] at h1
    simpa only [pow_zero,cubicThetaResiduesOne_tsum] using h1
  rw [h3,h2',h1']
  ac_rfl

theorem cubicThetaPrimeCubeLowerValue_sum {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' r : Residues (p^3), cubicThetaPrimeCubeLowerValue hp F x (residueRepresentative (p^3) r))=
      cubicThetaPrimeCubeLowerValue hp F x 0+
      (∑' u : (Residues (p^3))ˣ, cubicThetaPrimeCubeLowerValue hp F x
        (residueRepresentative (p^3) (u : Residues (p^3))))+
      (∑' u : (Residues (p^2))ˣ, cubicThetaPrimeCubeLowerValue hp F x
        (p*residueRepresentative (p^2) (u : Residues (p^2))))+
      (∑' u : (Residues p)ˣ, cubicThetaPrimeCubeLowerValue hp F x
        (p^2*residueRepresentative p (u : Residues p))) :=
  cubicThetaPrimeCubePeriodic_sum hp _ (cubicThetaPrimeCubeLowerValue_congr hp F x)

end CubicFirstMoment

end

end OAI
