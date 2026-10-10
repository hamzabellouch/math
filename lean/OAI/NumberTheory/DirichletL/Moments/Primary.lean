import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Moments.Lattice

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimary
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)

def primaryIdealCharacter (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    Ideal O →* ℂ :=
  χ.toMonoidHom.comp ((Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom.comp
    primaryGeneratorHom.toMonoidHom)

@[simp] theorem primaryIdealCharacter_apply (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    primaryIdealCharacter c χ I =
      χ (Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator I)) := rfl

theorem primaryIdealCharacter_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    ‖primaryIdealCharacter c χ I‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact QuadraticInitialBound.norm_finite_character_le_one χ _

theorem primaryIdealCharacter_zero_of_bad (c : O)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O)
    (hI : primaryGenerator I = 0) : primaryIdealCharacter c χ I = 0 := by
  rw [primaryIdealCharacter_apply, hI, map_zero, χ.map_zero]

theorem tsum_primaryIdealCharacter_all (c : O)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (f : Ideal O → ℂ) :
    (∑' I : GoodIdeal, primaryIdealCharacter c χ I.val * f I.val) =
      ∑' I : Ideal O, primaryIdealCharacter c χ I * f I := by
  apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryGenerator I ≠ 0})
    (f := fun I => primaryIdealCharacter c χ I * f I)
  intro I hI
  change primaryGenerator I ≠ 0
  intro hz
  apply hI
  change primaryIdealCharacter c χ I * f I = 0
  rw [primaryIdealCharacter_zero_of_bad c χ I hz, zero_mul]

theorem primaryIdealCharacter_ray_trivial (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (a : O)
    (ha : (3 * c : O) ∣ a - 1) :
    primaryIdealCharacter c χ (Ideal.span {a}) = 1 := by
  have h3 : (3 : O) ∣ a - 1 := (dvd_mul_right (3 : O) c).trans ha
  have hc : c ∣ a - 1 := (dvd_mul_left c (3 : O)).trans ha
  have hp := lambda_sq_dvd_three.trans h3
  have ha0 := CubicJacobiGlobal.primary_ne_zero a hp
  have hq : Ideal.Quotient.mk (Ideal.span {c}) a = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {c})), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hc)
  rw [primaryIdealCharacter_apply, primaryGenerator_span a ha0 hp, hq, map_one]

theorem primaryIdealCharacter_mul (c : O)
    (χ ξ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    primaryIdealCharacter c (χ * ξ) = primaryIdealCharacter c χ * primaryIdealCharacter c ξ := by
  ext I
  rfl

def primaryResidueValue (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (r : O ⧸ Ideal.span {c}) : ℂ :=
  if (3 : O) ∣ Quotient.out r - 1 then χ r else 0

theorem primaryResidueValue_mk (c : O) (h3 : (3 : O) ∣ c)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (x : O) :
    primaryResidueValue c χ (Ideal.Quotient.mk (Ideal.span {c}) x) =
      if (3 : O) ∣ x - 1 then χ (Ideal.Quotient.mk (Ideal.span {c}) x) else 0 := by
  have hc : c ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x) - x :=
    Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))
  have hd := h3.trans hc
  have hp : (3 : O) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x) - 1 ↔
      (3 : O) ∣ x - 1 := by
    constructor
    · intro h
      convert dvd_sub h hd using 1 ; ring
    · intro h
      convert dvd_add hd h using 1 ; ring
  simp only [primaryResidueValue, hp]

theorem primary_lattice_eq_ideal_sum (c : O) (h3 : (3 : O) ∣ c)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑' z : O, primaryResidueValue c χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / X)) =
      ∑' I : GoodIdeal, primaryIdealCharacter c χ I.val *
        W ((Ideal.absNorm I.val : ℝ) / X) := by
  let f : O → ℂ := fun z => χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / X)
  have hleft : (∑' z : O, primaryResidueValue c χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / X)) =
      ∑' z : PrimaryLower, f z.val := by
    calc
      _ = ∑' z : O, ({z : O | (3 : O) ∣ z - 1} : Set O).indicator f z := by
        apply tsum_congr
        intro z
        rw [primaryResidueValue_mk c h3 χ z]
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, f]
        split_ifs <;> simp only [zero_mul]
      _ = _ := (tsum_subtype {z : O | (3 : O) ∣ z - 1} f).symm
  rw [hleft, ← primaryLowerIdealEquiv.symm.tsum_eq]
  apply tsum_congr
  intro I
  change χ (Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator I.val)) *
      W (‖eisEmbedding (primaryGenerator I.val)‖ ^ 2 / X) = _
  rw [primaryGenerator_norm_sq I.val I.property]
  rfl

theorem primary_ideal_volume_error (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : GoodIdeal, primaryIdealCharacter c χ I.val *
          W ((Ideal.absNorm I.val : ℝ) / X)) -
      (X / ‖eisEmbedding c‖ ^ 2 : ℝ) •
        ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) *
          EisensteinSchwartzPoisson.paperRadialFourier W 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) *
        QuadraticInitialBound.pvControl W := by
  rw [← primary_lattice_eq_ideal_sum c h3 χ W X]
  exact CenteredMomentLattice.periodic_lattice_volume_error W X hX c hc (primaryResidueValue c χ)

theorem primary_ideal_volume_error_all (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : Ideal O, primaryIdealCharacter c χ I *
          W ((Ideal.absNorm I : ℝ) / X)) -
      (X / ‖eisEmbedding c‖ ^ 2 : ℝ) •
        ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) *
          EisensteinSchwartzPoisson.paperRadialFourier W 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) *
        QuadraticInitialBound.pvControl W := by
  rw [← tsum_primaryIdealCharacter_all c χ (fun I => W ((Ideal.absNorm I : ℝ) / X))]
  exact primary_ideal_volume_error c hc h3 χ W X hX

end SevenEighths.CenteredMomentPrimary
end

end OAI
