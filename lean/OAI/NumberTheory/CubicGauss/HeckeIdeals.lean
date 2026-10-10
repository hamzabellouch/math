import Mathlib
import OAI.NumberTheory.CubicGauss.HeckeFunctions
import OAI.NumberTheory.CubicGram.EuclideanDomain

namespace OAI

/-! Principal ideals, unit orbits and ideal-theoretic Hecke series. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma normNat_of_isUnit {u : Eisenstein} (hu : IsUnit u) : normNat u = 1 :=
  Nat.isUnit_iff.mp (hu.map normNatHom)

lemma norm_of_isUnit {u : Eisenstein} (hu : IsUnit u) : norm u = 1 := by
  rw [← normNat_cast, normNat_of_isUnit hu, Nat.cast_one]

namespace HeckeTheta

lemma norm_ofCoords_eq_one_iff (a b : ℤ) :
    norm (ofCoords a b)=1 ↔ a^2-a*b+b^2=1 := by
  rw [norm,ofCoords_coe,coordinates_norm]
  exact_mod_cast (Iff.rfl : a^2-a*b+b^2=1 ↔ a^2-a*b+b^2=1)

lemma norm_one_isUnit {z : Eisenstein} (hz : norm z=1) : IsUnit z := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective z
  have hh := (norm_ofCoords_eq_one_iff a b).mp hz
  apply isUnit_iff_exists_inv.mpr
  refine ⟨ofCoords (a-b) (-b), ?_⟩
  rw [ofCoords_mul, show a*(a-b)-b*(-b)=1 by nlinarith [hh],
    show a*(-b)+b*(a-b)-b*(-b)=0 by ring]
  simp [ofCoords]

def sixUnitCoords : Finset (ℤ × ℤ) :=
  {(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1)}

lemma mem_sixUnitCoords (a b : ℤ) :
    (a,b) ∈ sixUnitCoords ↔ a^2-a*b+b^2=1 := by
  constructor
  · intro h
    simp only [sixUnitCoords, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h
    rcases h with h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl⟩ <;> norm_num
  · intro h
    have ha : -1 ≤ a ∧ a ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (a-2*b),sq_nonneg (a-2),sq_nonneg (a+2)]
    have hb : -1 ≤ b ∧ b ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (b-2*a),sq_nonneg (b-2),sq_nonneg (b+2)]
    obtain ⟨ha1,ha2⟩ := ha
    obtain ⟨hb1,hb2⟩ := hb
    interval_cases a <;> interval_cases b <;> norm_num [sixUnitCoords] at *

def sixUnitsEquiv : {p : ℤ × ℤ // p ∈ sixUnitCoords} ≃ Eisensteinˣ :=
  Equiv.ofBijective
    (fun p => (norm_one_isUnit ((norm_ofCoords_eq_one_iff p.1.1 p.1.2).mpr
      ((mem_sixUnitCoords p.1.1 p.1.2).mp p.2))).unit) (by
    constructor
    · intro p r h
      apply Subtype.ext
      apply ofCoords_injective
      simpa only [IsUnit.unit_spec] using congrArg Units.val h
    · intro u
      obtain ⟨⟨a,b⟩,he⟩ := ofCoords_surjective (u : Eisenstein)
      change ofCoords a b = (u : Eisenstein) at he
      have hh : norm (ofCoords a b)=1 := by rw [he]; exact norm_of_isUnit u.isUnit
      refine ⟨⟨(a,b),(mem_sixUnitCoords a b).mpr
        ((norm_ofCoords_eq_one_iff a b).mp hh)⟩, ?_⟩
      apply Units.ext
      simpa only [IsUnit.unit_spec] using he)

instance : Fintype Eisensteinˣ := Fintype.ofEquiv _ sixUnitsEquiv

lemma card_eisenstein_units : Fintype.card Eisensteinˣ = 6 := by
  rw [← Fintype.card_congr sixUnitsEquiv, Fintype.card_coe]
  norm_num [sixUnitCoords]

open Submodule.IsPrincipal

lemma ideal_generator_ne_zero (I : Ideal Eisenstein) (hI : I ≠ ⊥) :
    generator I ≠ 0 := mt (eq_bot_iff_generator_eq_zero I).mpr hI

def modulusFiberEquiv (I : Ideal Eisenstein) (hI : I ≠ ⊥) :
    Eisensteinˣ ≃ {a : Eisenstein // modulus a=I} :=
  Equiv.ofBijective (fun u => ⟨generator I * u, by
    have ha : Associated (generator I) (generator I*u) := ⟨u,rfl⟩
    exact (Ideal.span_singleton_eq_span_singleton.mpr ha.symm).trans
      (Ideal.span_singleton_generator I)⟩) (by
    constructor
    · intro u v h
      apply Units.ext
      exact mul_left_cancel₀ (ideal_generator_ne_zero I hI) (congrArg Subtype.val h)
    · intro a
      have ha : Associated (generator I) a.1 :=
        Ideal.span_singleton_eq_span_singleton.mp
          ((Ideal.span_singleton_generator I).trans a.2.symm)
      obtain ⟨u,hu⟩ := ha
      exact ⟨u,Subtype.ext hu⟩)

lemma tsum_elements_eq_six_ideal_generators (f : Eisenstein → ℂ)
    (hf : Summable f) (h0 : f 0=0)
    (hu : ∀ (a : Eisenstein) (u : Eisensteinˣ), f (a*u)=f a) :
    ∑' a, f a = 6 * ∑' I : Ideal Eisenstein, f (generator I) := by
  let e := Equiv.sigmaFiberEquiv modulus
  have hs : Summable (fun p : (I : Ideal Eisenstein) × {a // modulus a=I} => f p.2.1) :=
    e.summable_iff.mpr hf
  calc
    _ = ∑' p : (I : Ideal Eisenstein) × {a // modulus a=I}, f p.2.1 :=
      (e.tsum_eq f).symm
    _ = ∑' I : Ideal Eisenstein, ∑' a : {a // modulus a=I}, f a.1 := hs.tsum_sigma
    _ = ∑' I : Ideal Eisenstein, 6*f (generator I) := by
      apply tsum_congr
      intro I
      by_cases hI : I=⊥
      · subst I
        have he (a : {a : Eisenstein // modulus a=⊥}) : a.1=0 :=
          Ideal.span_singleton_eq_bot.mp a.2
        simp only [he, h0, tsum_zero, generator_bot, mul_zero]
      · rw [← (modulusFiberEquiv I hI).tsum_eq]
        change ∑' u : Eisensteinˣ, f (generator I*u) = _
        simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ,
          card_eisenstein_units, nsmul_eq_mul, Nat.cast_ofNat]
    _ = 6 * ∑' I : Ideal Eisenstein, f (generator I) := tsum_mul_left

def TrivialInfinity (q : Eisenstein) (χ : MulChar (Residues q) ℂ) : Prop :=
  ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u)=1

lemma norm_mul_unit (a : Eisenstein) (u : Eisensteinˣ) : norm (a*u)=norm a := by
  change Complex.normSq ((a : ℂ)*(u : Eisenstein))=norm a
  rw [Complex.normSq_mul]
  change norm a * norm (u : Eisenstein) = _
  rw [norm_of_isUnit u.isUnit, mul_one]

def idealNorm (I : Ideal Eisenstein) : ℕ := Nat.card (Eisenstein ⧸ I)

lemma idealNorm_generator (I : Ideal Eisenstein) (hI : I ≠ ⊥) :
    idealNorm I = normNat (generator I) := by
  have hh := residues_card (ideal_generator_ne_zero I hI)
  simpa only [Residues, modulus, idealNorm, Ideal.span_singleton_generator] using hh

def idealHeckeSeries (q : Eisenstein) (χ : MulChar (Residues q) ℂ) (s : ℂ) : ℂ :=
  ∑' I : Ideal Eisenstein,
    χ (Ideal.Quotient.mk (modulus q) (generator I)) / (idealNorm I : ℂ)^s

theorem elementHeckeSeries_eq_idealSeries (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1) (hu : TrivialInfinity q χ)
    (s : ℂ) (hs : 1 < s.re) :
    elementHeckeSeries q χ s = idealHeckeSeries q χ s := by
  let f (a : Eisenstein) : ℂ := χ (Ideal.Quotient.mk (modulus q) a)/(norm a : ℂ)^s
  have hf : Summable f := elementHeckeSeries_summable q hq χ s hs
  have h0 : f 0=0 := by simp [f, mulChar_zero_of_nonprincipal χ hn]
  have hunit (a : Eisenstein) (u : Eisensteinˣ) : f (a*u)=f a := by
    simp only [f, map_mul, hu u, mul_one, norm_mul_unit]
  have he := tsum_elements_eq_six_ideal_generators f hf h0 hunit
  rw [elementHeckeSeries, show (∑' a : Eisenstein,
    χ (Ideal.Quotient.mk (modulus q) a)/(norm a : ℂ)^s) = ∑' a, f a from rfl, he]
  have hc : (1/6 : ℂ)*6=1 := by norm_num
  rw [← mul_assoc, hc, one_mul, idealHeckeSeries]
  apply tsum_congr
  intro I
  by_cases hI : I=⊥
  · subst I
    simp [f, mulChar_zero_of_nonprincipal χ hn]
  · rw [idealNorm_generator I hI]
    simp only [f, ← normNat_cast, Complex.ofReal_natCast]

theorem idealHeckeSeries_eq_nonzero_idealSum (q : Eisenstein)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1) (s : ℂ) :
    idealHeckeSeries q χ s = ∑' I : {I : Ideal Eisenstein // I ≠ ⊥},
      χ (Ideal.Quotient.mk (modulus q) (generator I.1)) / (idealNorm I.1 : ℂ)^s := by
  unfold idealHeckeSeries
  symm
  refine tsum_subtype_eq_of_support_subset (s := {I : Ideal Eisenstein | I ≠ ⊥})
    (f := fun I : Ideal Eisenstein =>
      χ (Ideal.Quotient.mk (modulus q) (generator I)) / (idealNorm I : ℂ)^s) ?_
  intro I hI
  change I ≠ ⊥
  intro h0
  subst I
  exact hI (by simp [mulChar_zero_of_nonprincipal χ hn])

lemma ideal_coefficient_eq_of_generator (q : Eisenstein)
    (χ : MulChar (Residues q) ℂ) (hu : TrivialInfinity q χ)
    (I : Ideal Eisenstein) (a : Eisenstein) (ha : modulus a=I) :
    χ (Ideal.Quotient.mk (modulus q) (generator I)) =
      χ (Ideal.Quotient.mk (modulus q) a) := by
  have hass : Associated (generator I) a :=
    Ideal.span_singleton_eq_span_singleton.mp
      ((Ideal.span_singleton_generator I).trans ha.symm)
  obtain ⟨u, hu'⟩ := hass
  rw [← hu']
  simp only [map_mul, hu u, mul_one]

lemma inverse_character_eq_conjugate (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (a : Residues q) :
    (χ⁻¹ : MulChar (Residues q) ℂ) a = star (χ a) := by
  let : Finite (Residues q) := finite_residues hq
  exact (MulChar.star_apply' χ a).symm

lemma TrivialInfinity.inv {q : Eisenstein} {χ : MulChar (Residues q) ℂ}
    (h : TrivialInfinity q χ) : TrivialInfinity q χ⁻¹ := by
  intro u
  rw [MulChar.inv_apply_eq_inv', h u, inv_one]

def conductorScale (q : Eisenstein) : ℝ := Real.sqrt (3*norm q)/(2*Real.pi)

lemma conductorScale_pos (q : Eisenstein) (hq : q ≠ 0) : 0 < conductorScale q := by
  unfold conductorScale
  positivity [norm_pos hq, Real.pi_pos]

def analyticHeckeL (q : Eisenstein) (χ : MulChar (Residues q) ℂ) (s : ℂ) : ℂ :=
  completedHeckeMellin q χ s * (conductorScale q : ℂ)^(-s) * (Complex.Gamma s)⁻¹

theorem analyticHeckeL_entire (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) (hn : χ ≠ 1) :
    Differentiable ℂ (analyticHeckeL q χ) := by
  have hc : (conductorScale q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (conductorScale_pos q hq).ne'
  exact ((completedHeckeMellin_entire q hq χ hχ hn).mul
    (differentiable_id.neg.const_cpow (Or.inl hc))).mul Complex.differentiable_one_div_Gamma

theorem analyticHeckeL_eq_idealSeries (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1) (hu : TrivialInfinity q χ)
    (s : ℂ) (hs : 1 < s.re) :
    analyticHeckeL q χ s = idealHeckeSeries q χ s := by
  have hc : (conductorScale q : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (conductorScale_pos q hq).ne'))
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  rw [analyticHeckeL, completedHeckeMellin_eq_exact_completion q hq χ hn s hs,
    elementHeckeSeries_eq_idealSeries q hq χ hn hu s hs]
  change (conductorScale q : ℂ)^s * Complex.Gamma s * idealHeckeSeries q χ s *
    (conductorScale q : ℂ)^(-s) * (Complex.Gamma s)⁻¹ = _
  rw [Complex.cpow_neg]
  field_simp

theorem exact_completion_identity (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (s : ℂ) (hγ : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    completedHeckeMellin q χ s = (conductorScale q : ℂ)^s * Complex.Gamma s *
      analyticHeckeL q χ s := by
  have hc : (conductorScale q : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (conductorScale_pos q hq).ne'))
  have hg := Complex.Gamma_ne_zero hγ
  rw [analyticHeckeL, Complex.cpow_neg]
  field_simp

theorem primitive_Hecke_analytic_input (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ)
    (hn : χ ≠ 1) (hu : TrivialInfinity q χ) :
    Differentiable ℂ (analyticHeckeL q χ) ∧
    Differentiable ℂ (completedHeckeMellin q χ) ∧
    (∀ s : ℂ, 1 < s.re → analyticHeckeL q χ s = idealHeckeSeries q χ s) ∧
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      completedHeckeMellin q χ s =
        ((Real.sqrt (3*norm q)/(2*Real.pi) : ℝ) : ℂ)^s * Complex.Gamma s *
          analyticHeckeL q χ s) ∧
    ‖heckeRootNumber q hq χ‖=1 ∧
    (∀ s : ℂ, completedHeckeMellin q χ s = heckeRootNumber q hq χ *
      completedHeckeMellin q χ⁻¹ (1-s)) := by
  exact ⟨analyticHeckeL_entire q hq χ hχ hn,
    completedHeckeMellin_entire q hq χ hχ hn,
    analyticHeckeL_eq_idealSeries q hq χ hn hu,
    exact_completion_identity q hq χ,
    heckeRootNumber_norm q hq χ hχ,
    completedHeckeMellin_functional_equation q hq χ hχ hn⟩

end HeckeTheta
end CubicFirstMoment
end

end OAI
