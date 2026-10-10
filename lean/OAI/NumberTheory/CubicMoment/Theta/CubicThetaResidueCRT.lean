import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierCRT
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueConductorKernel

namespace OAI

/-! The actual product-ring reduction underlying the mixed-residue
parametrization of the Kloosterman denominators. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaResidueProductReduction (a b : Eisenstein) :
    Residues (a*b) →+* Residues a × Residues b :=
  (residueReduction (dvd_mul_right a b)).prod
    (residueReduction (dvd_mul_left b a))

lemma cubicThetaResidueProductReduction_injective {a b : Eisenstein}
    (hab : IsCoprime a b) : Function.Injective (cubicThetaResidueProductReduction a b) := by
  intro x y hxy
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha := congrArg Prod.fst hxy
  have hb := congrArg Prod.snd hxy
  change Ideal.Quotient.mk (modulus a) r=Ideal.Quotient.mk (modulus a) s at ha
  change Ideal.Quotient.mk (modulus b) r=Ideal.Quotient.mk (modulus b) s at hb
  exact residue_eq_of_dvd_sub (hab.mul_dvd
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp ha))
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hb)))

def cubicThetaResidueCRT {a b : Eisenstein} (ha : a≠0) (hb : b≠0)
    (hab : IsCoprime a b) : Residues (a*b) ≃+* Residues a × Residues b := by
  let : Finite (Residues a) := finite_residues ha
  let : Finite (Residues b) := finite_residues hb
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha hb)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  apply RingEquiv.ofBijective (cubicThetaResidueProductReduction a b)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨cubicThetaResidueProductReduction_injective hab,?_⟩
  rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,Nat.card_prod,
    residues_card ha,residues_card hb,residues_card (mul_ne_zero ha hb),normNat_mul]

lemma cubicThetaResidueProductReduction_mix (a b : Eisenstein)
    (x : Residues a) (y : Residues b) :
    cubicThetaResidueProductReduction a b (residueMix a b (x,y))=
      (Ideal.Quotient.mk (modulus a) b*x,Ideal.Quotient.mk (modulus b) a*y) := by
  apply Prod.ext
  · change Ideal.Quotient.mk (modulus a)
      (b*residueRepresentative a x+a*residueRepresentative b y)=_
    have hz : Ideal.Quotient.mk (modulus a) a=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl a))
    simp only [map_add,map_mul,residueRepresentative_spec,hz,zero_mul,add_zero]
  · change Ideal.Quotient.mk (modulus b)
      (b*residueRepresentative a x+a*residueRepresentative b y)=_
    have hz : Ideal.Quotient.mk (modulus b) b=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl b))
    simp only [map_add,map_mul,residueRepresentative_spec,hz,zero_mul,zero_add]

lemma cubicThetaResidueMix_isUnit {a b : Eisenstein} (ha : a≠0) (hb : b≠0)
    (hab : IsCoprime a b) (x : Residues a) (y : Residues b) :
    IsUnit (residueMix a b (x,y)) ↔ IsUnit x ∧ IsUnit y := by
  have habu : IsUnit (Ideal.Quotient.mk (modulus a) b) := residue_isUnit_of_isCoprime hab
  have hbau : IsUnit (Ideal.Quotient.mk (modulus b) a) := residue_isUnit_of_isCoprime hab.symm
  have he (z : Residues (a*b)) : IsUnit z ↔ IsUnit (cubicThetaResidueCRT ha hb hab z) := by
    constructor
    · intro hz
      exact hz.map (cubicThetaResidueCRT ha hb hab).toMonoidHom
    · intro hz
      have hh := hz.map (cubicThetaResidueCRT ha hb hab).symm.toMonoidHom
      change IsUnit ((cubicThetaResidueCRT ha hb hab).symm (cubicThetaResidueCRT ha hb hab z)) at hh
      rwa [RingEquiv.symm_apply_apply] at hh
  rw [he]
  change IsUnit (cubicThetaResidueProductReduction a b (residueMix a b (x,y))) ↔ _
  rw [cubicThetaResidueProductReduction_mix,Prod.isUnit_iff]
  exact and_congr habu.mul_left_iff hbau.mul_left_iff

lemma cubicThetaResidueHom_inverse {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {x : R} (hx : IsUnit x) : f (Ring.inverse x)=Ring.inverse (f x) := by
  obtain ⟨u,rfl⟩ := hx
  rw [Ring.inverse_unit]
  change f (↑u⁻¹)=Ring.inverse (↑(Units.map f.toMonoidHom u) : S)
  rw [Ring.inverse_unit]
  exact congrArg Units.val ((Units.map f.toMonoidHom).map_inv u)

end CubicFirstMoment

end

end OAI
