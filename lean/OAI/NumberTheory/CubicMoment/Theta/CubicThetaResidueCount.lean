import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitCount

namespace OAI

/-! Elementary local cardinalities for the Eisenstein scattering factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_residueReduction_kernel_card {q d : Eisenstein}
    (hq : q≠0) (hd0 : d≠0) (hd : d∣q) :
    normNat q = normNat d * Nat.card (residueReduction hd).toAddMonoidHom.ker := by
  let f := (residueReduction hd).toAddMonoidHom
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr hd)
  have he := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    residues_card hq,residues_card hd0] at he
  exact he

lemma cubicTheta_residueReduction_primePower_card {p : Eisenstein} (hp : Prime p) (n : ℕ) :
    Nat.card (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n))).toAddMonoidHom.ker =
      normNat p^n := by
  have he := cubicTheta_residueReduction_kernel_card (pow_ne_zero _ hp.ne_zero)
    hp.ne_zero (dvd_pow_self p (Nat.succ_ne_zero n))
  have hn : normNat (p^(n+1))=normNat p^(n+1) := map_pow normNatHom p (n+1)
  rw [hn,pow_succ,mul_comm (normNat p^n)] at he
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (normNat_ne_zero hp.ne_zero)) he.symm

lemma cubicTheta_residueReduction_eq_zero_iff {q d : Eisenstein} (hd : d∣q)
    (x : Residues q) :
    residueReduction hd x=0 ↔ d∣residueRepresentative q x := by
  have he : residueReduction hd x=
      Ideal.Quotient.mk (modulus d) (residueRepresentative q x) := by
    exact (congrArg (residueReduction hd) (residueRepresentative_spec q x)).symm
  rw [he,Ideal.Quotient.eq_zero_iff_mem,modulus,Ideal.mem_span_singleton]

lemma cubicTheta_primePower_nonunit_iff {p : Eisenstein} (hp : Prime p) (n : ℕ)
    (x : Residues (p^(n+1))) :
    ¬IsUnit x ↔ residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x=0 := by
  rw [cubicTheta_residueReduction_eq_zero_iff]
  have hu : IsUnit x ↔ IsCoprime (p^(n+1)) (residueRepresentative (p^(n+1)) x) := by
    constructor
    · intro h
      exact isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])
    · intro h
      have he := residue_isUnit_of_isCoprime h
      rwa [residueRepresentative_spec] at he
  rw [hu,IsCoprime.pow_left_iff (Nat.succ_pos n),hp.irreducible.coprime_iff_not_dvd,not_not]

def cubicThetaUnitsEquivIsUnit (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.property.unit_spec

lemma cubicTheta_primePower_units_card {p : Eisenstein} (hp : Prime p) (n : ℕ) :
    Nat.card (Residues (p^(n+1)))ˣ = normNat p^(n+1)-normNat p^n := by
  let : Finite (Residues (p^(n+1))) := finite_residues (pow_ne_zero _ hp.ne_zero)
  let : Fintype (Residues (p^(n+1))) := Fintype.ofFinite _
  let f := (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n))).toAddMonoidHom
  have hk : Nat.card {x : Residues (p^(n+1)) // ¬IsUnit x}=normNat p^n := by
    let e : {x : Residues (p^(n+1)) // ¬IsUnit x} ≃ f.ker :=
      Equiv.subtypeEquivRight (fun x => cubicTheta_primePower_nonunit_iff hp n x)
    rw [Nat.card_congr e]
    exact cubicTheta_residueReduction_primePower_card hp n
  rw [Nat.card_congr (cubicThetaUnitsEquivIsUnit (Residues (p^(n+1))))]
  have he := Fintype.card_subtype_compl (fun x : Residues (p^(n+1)) => ¬IsUnit x)
  simp only [not_not] at he
  rw [Nat.card_eq_fintype_card] at hk
  rw [Nat.card_eq_fintype_card,he,hk,←Nat.card_eq_fintype_card,
    residues_card (pow_ne_zero _ hp.ne_zero)]
  exact congrArg (·-normNat p^n) (map_pow normNatHom p (n+1))

lemma cubicTheta_coprime_units_card {a b : Eisenstein} (hab : IsCoprime a b) :
    Nat.card (Residues (a*b))ˣ = Nat.card (Residues a)ˣ*Nat.card (Residues b)ˣ := by
  let e : Residues (a*b) ≃+* Residues a × Residues b :=
    (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
      (Ideal.quotientMulEquivQuotientProd (modulus a) (modulus b)
        ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))
  rw [Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv,
    Nat.card_congr (MulEquiv.prodUnits : (Residues a × Residues b)ˣ ≃* _).toEquiv,
    Nat.card_prod]

end CubicFirstMoment

end

end OAI
