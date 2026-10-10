import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Hecke.FamilySeries
import OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
import OAI.NumberTheory.DirichletL.IdealCharacter

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def idealCoeff (χ : Character) : Ideal O →*₀ ℂ :=
  IdealCharacter.ofResidue χ.modulus χ.residue χ.unit_trivial

@[simp] theorem idealCoeff_zero (χ : Character) : idealCoeff χ 0 = 0 := map_zero _

theorem idealCoeff_span (χ : Character) {z : O} (hz : z ≠ 0) :
    idealCoeff χ (Ideal.span {z}) = elementCoeff χ z :=
  IdealCharacter.ofResidue_span χ.modulus χ.residue χ.unit_trivial hz

theorem coordinateElement_eq_baseline (a b : ℤ) :
    coordinateElement a b = ActualEisensteinCoordinates.eval a b := rfl

def coordinateEquiv : (ℤ × ℤ) ≃ O :=
  Equiv.ofBijective (fun n => coordinateElement n.1 n.2)
    ⟨fun _ _ h => Prod.ext
      (ActualEisensteinCoordinates.unique_coordinates h).1
      (ActualEisensteinCoordinates.unique_coordinates h).2,
      HeckeCoordinates.coordinateElement_surjective⟩

theorem normForm_eq_absNorm_span (n : ℤ × ℤ) :
    EisensteinTheta.normForm n.1 n.2 =
      (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℝ) := by
  rw [coordinateElement_eq_baseline,
    ← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ActualEisensteinCubic.eisEmbedding_eval_norm_sq]
  simp only [EisensteinTheta.normForm, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two]

def elementTerm (χ : Character) (s : ℂ) (z : O) : ℂ :=
  elementCoeff χ z / (Ideal.absNorm (Ideal.span {z}) : ℂ) ^ s

def idealTerm (χ : Character) (s : ℂ) (I : Ideal O) : ℂ :=
  idealCoeff χ I / (Ideal.absNorm I : ℂ) ^ s

theorem elementTerm_coordinate (χ : Character) (s : ℂ) (n : ℤ × ℤ) :
    elementTerm χ s (coordinateEquiv n) =
      elementCoeff χ (coordinateElement n.1 n.2) /
        (EisensteinTheta.normForm n.1 n.2 : ℂ) ^ s := by
  change elementCoeff χ (coordinateElement n.1 n.2) /
    (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℂ) ^ s = _
  rw [normForm_eq_absNorm_span]
  rw [Complex.ofReal_natCast]

theorem elementTerm_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (elementTerm χ s) (continuedLattice χ s) := by
  apply coordinateEquiv.hasSum_iff.mp
  change HasSum (fun n => elementTerm χ s (coordinateEquiv n)) _
  simpa only [elementTerm_coordinate] using continuedLattice_hasSum χ hs

theorem elementTerm_zero (χ : Character) {s : ℂ} (hs : s ≠ 0) :
    elementTerm χ s 0 = 0 := by
  simp [elementTerm, Complex.zero_cpow hs]

theorem elementTerm_unit_mul (χ : Character) (s : ℂ) (u : Oˣ) (z : O) :
    elementTerm χ s ((u : O) * z) = elementTerm χ s z := by
  unfold elementTerm
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem elementTerm_idealGenerator (χ : Character) (s : ℂ)
    (I : UnrestrictedIdealReindex.NonzeroIdeal) :
    elementTerm χ s (ConcretePrimeRowBridge.idealGenerator I.val) = idealTerm χ s I.val := by
  unfold elementTerm idealTerm
  rw [ConcretePrimeRowBridge.span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator χ.modulus χ.residue χ.unit_trivial
    I.property (ConcretePrimeRowBridge.span_idealGenerator I.val)).symm

theorem continuedLattice_eq_six_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    continuedLattice χ s = 6 * ∑' I : Ideal O, idealTerm χ s I := by
  have hs₀ : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero (elementTerm χ s)
    (elementTerm_hasSum χ hs).summable (elementTerm_zero χ hs₀)
    (elementTerm_unit_mul χ s)
  rw [(elementTerm_hasSum χ hs).tsum_eq] at h
  simp_rw [elementTerm_idealGenerator] at h
  have hsum : (∑' I : UnrestrictedIdealReindex.NonzeroIdeal, idealTerm χ s I.val) =
      ∑' I : Ideal O, idealTerm χ s I := by
    apply tsum_subtype_eq_of_support_subset
    intro I hI hzero
    exact hI (by rw [hzero]; unfold idealTerm; rw [map_zero]; exact zero_div _)
  rwa [hsum] at h

def LFunction (χ : Character) (s : ℂ) : ℂ := continuedLattice χ s / 6

theorem LFunction_eq_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = ∑' I : Ideal O, idealTerm χ s I := by
  rw [LFunction, continuedLattice_eq_six_ideal_tsum χ hs]
  ring

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

theorem LFunction_entire_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6

end SevenEighths.HeckeFamily

end

end OAI
