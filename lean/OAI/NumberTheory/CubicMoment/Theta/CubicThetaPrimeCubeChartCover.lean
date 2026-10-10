import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeUpperChart

namespace OAI

/-! The two integral charts are disjoint and cover the actual right
cosets. The proof uses the primitive bottom row and units modulo p^3. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeLower_ne_upper {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (s : cubicThetaPrimeCubeUpperParameter p) :
    cubicThetaPrimeCubeLowerChart p r≠cubicThetaPrimeCubeUpperChart hp s := by
  intro he
  have hdet := (cubicThetaPrimeCubeCoset_eq_iff p _ _).mp he
  rw [cubicThetaPrimeCubeUpperRepresentative_c,cubicThetaPrimeCubeUpperRepresentative_d] at hdet
  change p^3 ∣ 3*1-(cubicThetaPrimeCubeWeylDenominator hp+
    9*residueRepresentative (p^3) s.val)*(3*residueRepresentative (p^3) r) at hdet
  have hpow : p ∣ p^3 := dvd_pow_self p (by norm_num)
  have hd : p ∣ cubicThetaPrimeCubeWeylDenominator hp+
      9*residueRepresentative (p^3) s.val :=
    dvd_add (hpow.trans (cubicThetaPrimeCubeWeylDenominator_dvd hp))
      (dvd_mul_of_dvd_right s.property 9)
  have ht := dvd_add (hpow.trans hdet)
    (dvd_mul_of_dvd_left hd (3*residueRepresentative (p^3) r))
  have hthree : p ∣ (3:Eisenstein) := by simpa only [mul_one,sub_add_cancel] using ht
  exact hp.2.not_isUnit ((primary_coprime_three hp.1).isRelPrime (dvd_refl p) hthree)

lemma cubicThetaPrimeCubeRepresentative_dvd {p x : Eisenstein} (hx : p∣x) :
    p∣residueRepresentative (p^3) (Ideal.Quotient.mk (modulus (p^3)) x) := by
  have he := residueRepresentative_spec (p^3) (Ideal.Quotient.mk (modulus (p^3)) x)
  have hd : p^3 ∣ residueRepresentative (p^3) (Ideal.Quotient.mk (modulus (p^3)) x)-x :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have ht := dvd_add ((dvd_pow_self p (by norm_num : (3:ℕ)≠0)).trans hd) hx
  simpa only [sub_add_cancel] using ht

theorem cubicThetaPrimeCubeUpperChart_covers {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (hd : p∣g.val 1 1) :
    ∃ r : cubicThetaPrimeCubeUpperParameter p,
      cubicThetaPrimeCubeUpperChart hp r=cubicThetaPrimeCubeCoset p g := by
  let q := Ideal.Quotient.mk (modulus (p^3))
  have hc : ¬p∣g.val 1 0 := fun hc => hp.2.not_isUnit
    ((cubicThetaBottomRow g).coprime.isRelPrime hc hd)
  have hpc : IsCoprime (p^3) (g.val 1 0) :=
    (hp.2.coprime_iff_not_dvd.mpr hc).pow_left
  have hunit : IsCoprime (p^3) (g.val 1 0*3) :=
    hpc.mul_right (primary_coprime_three (cubicThetaPrimeCube_primary hp))
  let u : (Residues (p^3))ˣ := (residue_isUnit_of_isCoprime hunit).unit
  let x := residueRepresentative (p^3) (u⁻¹ : (Residues (p^3))ˣ)
  let m := g.val 1 1*x
  let r : cubicThetaPrimeCubeUpperParameter p :=
    ⟨q m,cubicThetaPrimeCubeRepresentative_dvd (dvd_mul_of_dvd_left hd x)⟩
  refine ⟨r,(cubicThetaPrimeCubeCoset_eq_iff p _ _).mpr ?_⟩
  rw [cubicThetaPrimeCubeUpperRepresentative_c,cubicThetaPrimeCubeUpperRepresentative_d]
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (g.val 1 0*(cubicThetaPrimeCubeWeylDenominator hp+
    9*residueRepresentative (p^3) r.val)-g.val 1 1*3)=0
  have hqW : q (cubicThetaPrimeCubeWeylDenominator hp)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (cubicThetaPrimeCubeWeylDenominator_dvd hp))
  have hu : (u : Residues (p^3))=q (g.val 1 0*3) := IsUnit.unit_spec _
  have hx : q x=(u⁻¹ : (Residues (p^3))ˣ) := residueRepresentative_spec _ _
  have hi : q (g.val 1 0)*q 3*q x=1 := by
    rw [←map_mul,←hu,hx,←Units.val_mul,mul_inv_cancel,Units.val_one]
  have hr : q (residueRepresentative (p^3) r.val)=q m := residueRepresentative_spec _ _
  simp only [map_sub,map_add,map_mul,hqW,zero_add]
  rw [hr]
  change q (g.val 1 0)*(q 9*(q (g.val 1 1)*q x))-q (g.val 1 1)*q 3=0
  norm_num only [map_ofNat] at hi ⊢
  linear_combination (3*q (g.val 1 1))*hi

end CubicFirstMoment

end

end OAI
