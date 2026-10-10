import OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def norm (I : NonzeroIdeal) : ℝ := I.val.absNorm

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

def coefficient (χ : Character) (inverse : Bool) (I : Ideal O) : ℂ :=
  if inverse then (UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I else idealCoeff χ I

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

@[simp] theorem coefficient_zero (χ : Character) (inverse : Bool) : coefficient χ inverse 0 = 0 := by
  cases inverse
  · exact idealCoeff_zero χ
  · change (UniqueFactorizationMonoid.moebius (0 : Ideal O) : ℂ)*idealCoeff χ 0 = 0
    rw [idealCoeff_zero, mul_zero]

def shift (σ ω : ℝ) : ℂ := (σ : ℂ)-(ω : ℂ)*Complex.I

@[simp] theorem shift_re (σ ω : ℝ) : (shift σ ω).re = σ := by simp [shift]

def summand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ ω : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ ω)

def polynomial (χ : Character) (inverse : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ inverse W D σ ω I

theorem summand_finite_support (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b D σ ω : ℝ) (hD : 0 < D) (hW : Function.support W ⊆ Icc a b) :
    (Function.support (summand χ inverse W D σ ω)).Finite := by
  have hfin := Ideal.finite_setOfPred_absNorm_le (S := O) ⌈D*b⌉₊
  apply (Set.Finite.preimage (f := fun I : NonzeroIdeal => I.val) Subtype.val_injective.injOn hfin).subset
  intro I hI
  have hw : W (norm I/D) ≠ 0 := by
    intro h
    exact hI (by simp [summand, h])
  have hupper := (hW hw).2
  have hq : norm I ≤ D*b := by
    have h := (div_le_iff₀ hD).mp hupper
    linarith
  have hr : norm I ≤ (⌈D*b⌉₊ : ℝ) := hq.trans (Nat.le_ceil _)
  change I.val.absNorm ≤ ⌈D*b⌉₊
  dsimp [norm] at hr
  exact_mod_cast hr

def series (χ : Character) (inverse : Bool) (s : ℂ) : ℂ :=
  if inverse then HeckeReciprocal.reciprocal χ s else LFunction χ s

theorem series_eq_tsum (χ : Character) (inverse : Bool) {s : ℂ} (hs : 1 < s.re) :
    series χ inverse s =
      ∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, coefficient χ inverse I.val *
      CubicEisenstein.fullIdealWeight s I.val) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    apply tsum_subtype_eq_of_support_subset
      (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I)
    intro I hI hi
    subst I
    exact hI (by
      change coefficient χ inverse 0 * CubicEisenstein.fullIdealWeight s 0 = 0
      rw [coefficient_zero, zero_mul])
  have hc : (∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s)) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    rw [← he]
    apply tsum_congr
    intro I
    have hI : I.val ≠ 0 := I.property
    rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
    simp only [norm, Complex.ofReal_natCast]
  rw [hc]
  cases inverse
  · exact LFunction_eq_series χ hs
  · have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    change HeckeReciprocal.reciprocal χ s = _
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1, LFunction_eq_series χ hs,
      ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs]
    apply tsum_congr
    intro I
    simp only [coefficient,  ite_true, IdealEuler.weighted,
      IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring

end SevenEighths.HeckeDyadic

end

end OAI
