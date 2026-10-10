import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueCount

namespace OAI

/-! Unit lifting through powers of an Eisenstein modulus. The cardinality
factor is obtained from the actual additive and multiplicative kernels. -/
noncomputable section
namespace CubicFirstMoment

private def unitKernelEquivAddKernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : ∀ x, IsUnit x ↔ IsUnit (f x)) :
    (Units.map f.toMonoidHom).ker ≃ f.toAddMonoidHom.ker where
  toFun u := ⟨(u.val:R)-1,by
    change f ((u.val:R)-1)=0
    rw [map_sub,map_one]
    have he := congrArg (fun v : Sˣ => (v:S)) u.property
    change f (u.val:R)=1 at he
    rw [he,sub_self]⟩
  invFun x :=
    let hu : IsUnit (1+x.val) := (h _).mpr (by
      have hx : f x.val=0 := x.property
      rw [map_add,map_one,hx,add_zero]
      exact isUnit_one)
    ⟨hu.unit,by
      apply Units.ext
      change f (hu.unit:R)=1
      rw [hu.unit_spec,map_add,map_one,show f x.val=0 from x.property,add_zero]⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    dsimp only
    rw [IsUnit.unit_spec]
    ring
  right_inv x := by
    apply Subtype.ext
    dsimp only
    rw [IsUnit.unit_spec]
    ring

private lemma unit_card_mul_of_reflect {R S : Type*} [CommRing R] [CommRing S]
    [Finite R] (f : R →+* S) (hf : Function.Surjective f)
    (h : ∀ x, IsUnit x ↔ IsUnit (f x)) :
    Nat.card Rˣ*Nat.card S=Nat.card R*Nat.card Sˣ := by
  have ha := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.toAddMonoidHom.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
    f.toAddMonoidHom hf).toEquiv] at ha
  have hu := Subgroup.card_eq_card_quotient_mul_card_subgroup (Units.map f.toMonoidHom).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (Units.map f.toMonoidHom) (finite_ring_units_surjective f hf)).toEquiv,
    Nat.card_congr (unitKernelEquivAddKernel f h)] at hu
  rw [ha,hu]
  ring

lemma cubicTheta_residue_mk_isUnit_iff (q z : Eisenstein) :
    IsUnit (Ideal.Quotient.mk (modulus q) z) ↔ IsCoprime q z :=
  ⟨isCoprime_of_residue_isUnit,residue_isUnit_of_isCoprime⟩

lemma cubicTheta_unit_card_lift {q d : Eisenstein} (hq : q≠0) (hd : d∣q)
    (hc : ∀ z : Eisenstein, IsCoprime q z ↔ IsCoprime d z) :
    Nat.card (Residues q)ˣ*normNat d=normNat q*Nat.card (Residues d)ˣ := by
  let : Finite (Residues q) := finite_residues hq
  have hr (x : Residues q) : IsUnit x ↔ IsUnit (residueReduction hd x) := by
    have hs := residueRepresentative_spec q x
    rw [←hs,residueReduction_mk,cubicTheta_residue_mk_isUnit_iff,
      cubicTheta_residue_mk_isUnit_iff]
    exact hc _
  have he := unit_card_mul_of_reflect (residueReduction hd)
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr hd)) hr
  have hd0 : d≠0 := by intro he; rw [he,zero_dvd_iff] at hd; exact hq hd
  rwa [residues_card hq,residues_card hd0] at he

lemma cubicTheta_power_units_card {q : Eisenstein} (hq : q≠0) (n : ℕ) :
    Nat.card (Residues (q^(n+1)))ˣ=normNat q^n*Nat.card (Residues q)ˣ := by
  have he := cubicTheta_unit_card_lift (pow_ne_zero _ hq)
    (dvd_pow_self q (Nat.succ_ne_zero n)) (fun _ => IsCoprime.pow_left_iff (Nat.succ_pos n))
  have hn : normNat (q^(n+1))=normNat q^(n+1) := map_pow normNatHom _ _
  rw [hn,pow_succ] at he
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (normNat_ne_zero hq))
  calc
    _ = (normNat q^n*normNat q)*Nat.card (Residues q)ˣ := he
    _ = _ := by ring

lemma cubicTheta_three_units_card {c : Eisenstein} (hc : c≠0) (h3 : (3:Eisenstein)∣c) :
    Nat.card (Residues (3*c))ˣ=9*Nat.card (Residues c)ˣ := by
  have he := cubicTheta_unit_card_lift (mul_ne_zero (by norm_num) hc) (dvd_mul_left c 3)
    (fun z => ⟨fun h => h.of_mul_left_right,
      fun h => (h.of_isCoprime_of_dvd_left h3).mul_left h⟩)
  have hnorm : normNat (3:Eisenstein)=9 := by
    change ⌊Complex.normSq (3:ℂ)⌋₊=9
    norm_num [Complex.normSq_apply]
  rw [normNat_mul,hnorm] at he
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (normNat_ne_zero hc))
  calc
    _ = (9*normNat c)*Nat.card (Residues c)ˣ := he
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
