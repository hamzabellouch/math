import OAI.NumberTheory.DirichletL.Hecke.StripActual
import OAI.NumberTheory.DirichletL.CharacterTransport

namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckePresentation
open HeckeFamily

def generator (η : Character) : O := ConcretePrimeRowBridge.idealGenerator η.modulus

instance (η : Character) : NeZero (generator η) :=
  ⟨ConcretePrimeRowBridge.idealGenerator_ne_zero η.modulus η.modulus_ne_bot⟩

theorem span_generator (η : Character) : Ideal.span {generator η} = η.modulus :=
  ConcretePrimeRowBridge.span_idealGenerator η.modulus

def quotientEquiv (η : Character) : (O ⧸ Ideal.span {generator η}) ≃+* (O ⧸ η.modulus) :=
  Ideal.quotEquivOfEq (span_generator η)

def principalResidue (η : Character) : MulChar (O ⧸ Ideal.span {generator η}) ℂ :=
  CharacterTransport.pullback (quotientEquiv η) η.residue

@[simp] theorem principalResidue_mk (η : Character) (z : O) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) z) =
      elementCoeff η z := by
  simp only [principalResidue, CharacterTransport.pullback_apply, quotientEquiv,
    Ideal.quotEquivOfEq_mk, elementCoeff]

theorem principalResidue_unit (η : Character) (u : Oˣ) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) (u : O)) = 1 := by
  rw [principalResidue_mk]
  exact η.unit_trivial u

def principalCharacter (η : Character) : Character :=
  HeckePrimitive.character (generator η) (principalResidue η) (principalResidue_unit η)

@[simp] theorem principalCharacter_elementCoeff (η : Character) (z : O) :
    elementCoeff (principalCharacter η) z = elementCoeff η z := principalResidue_mk η z

theorem principalResidue_primitive (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) :
    FiniteFourier.IsPrimitiveOnIdeals (principalResidue η) :=
  CharacterTransport.primitive_pullback (quotientEquiv η) η.residue hp

private theorem pullback_one {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    CharacterTransport.pullback e (1 : MulChar S ℂ) = 1 := by
  apply MulChar.ext'
  intro x
  rw [CharacterTransport.pullback_apply]
  by_cases hx : IsUnit x
  · have hxe : IsUnit (e x) := hx.map e.toMonoidHom
    rw [MulChar.one_apply hxe, MulChar.one_apply hx]
  · have he : ¬ IsUnit (e x) := by
      intro h
      apply hx
      simpa using h.map e.symm.toMonoidHom
    rw [MulChar.map_nonunit _ he, MulChar.map_nonunit _ hx]

theorem principalResidue_ne_one (η : Character) (hη : η.residue ≠ 1) :
    principalResidue η ≠ 1 := by
  intro h
  have he := congrArg (CharacterTransport.pullback (quotientEquiv η).symm) h
  rw [principalResidue, CharacterTransport.pullback_symm, pullback_one] at he
  exact hη he

theorem LFunction_principalCharacter (η : Character) (hη : η.residue ≠ 1) (s : ℂ) :
    LFunction (principalCharacter η) s = LFunction η s := by
  have hp : (principalCharacter η).residue ≠ 1 := principalResidue_ne_one η hη
  have ha := LFunction_entire_nonprincipal (principalCharacter η) hp
  have hb := LFunction_entire_nonprincipal η hη
  have he : LFunction (principalCharacter η) = LFunction η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    unfold LFunction
    congr 1
    apply continuedLattice_eq_of_elementCoeff_eq _ _ (principalCharacter_elementCoeff η)
      (by linarith) (by intro h; norm_num [h] at hz)
  exact congr_fun he s

theorem uniform_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (hη : η.residue ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction η z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  have h := HeckeStripActual.uniform_strip_bound (generator η) (principalResidue η)
    (principalResidue_unit η) (principalResidue_primitive η hp) (principalResidue_ne_one η hη) z hz
  change ‖LFunction (principalCharacter η) z‖ ≤ _ at h
  rw [LFunction_principalCharacter η hη z] at h
  simpa only [HeckeStripActual.conductor, span_generator] using h

end SevenEighths.HeckePresentation

end

end OAI
