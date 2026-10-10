import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorCharacter
import OAI.NumberTheory.CubicGram.MixedPoisson

namespace OAI

/-! Modulo `9v` periodicity of the actual cubic numerator symbol.

The ramified factor is treated by reciprocity against an auxiliary primary
argument. The unit factor follows from Euler's finite-field definition. This
proves the elementary specialization recorded in DR v3, §1.2 (1.4)--(1.5),
including the zero values at common prime factors. -/
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma omega_ne_zero : omega ≠ 0 := omega_primitive.ne_zero (by decide)

private lemma primary_coprime_three' {a : Eisenstein} (ha : primary a) :
    IsCoprime a 3 := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨1, -k, by linear_combination hk⟩

/-- Reciprocity compares the value at three whenever both quotients are primary. -/
private lemma symbol_three_aux {a r x : Eisenstein}
    (ha : primary a) (hr : primary r) (hx : primary x)
    (hax : a - r = 3*x) (har : IsCoprime a r) :
    cubicSymbol a 3 = cubicSymbol r 3 := by
  have hrx : IsCoprime r x := by
    have h : IsCoprime r (3*x + r*1) := by
      rw [show 3*x + r*1 = a by linear_combination -hax]
      exact har.symm
    exact h.of_add_mul_left_right.of_mul_right_right
  have hn : cubicSymbol r x ≠ 0 := by
    intro hz
    have hh := norm_cubicSymbol_of_isCoprime hr hrx
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hleft : cubicSymbol a (3*x) = cubicSymbol a (-r) :=
    cubicSymbol_congr (residue_eq_of_dvd_sub ⟨1, by linear_combination -hax⟩)
  have hright : cubicSymbol r a = cubicSymbol r (3*x) :=
    cubicSymbol_congr (residue_eq_of_dvd_sub ⟨1, by linear_combination hax⟩)
  rw [cubicSymbol_mul_upper ha, cubicSymbol_neg ha,
    cubic_reciprocity ha hr, hright, cubicSymbol_mul_upper hr] at hleft
  have hxa : cubicSymbol x a = cubicSymbol x r :=
    cubicSymbol_congr (residue_eq_of_dvd_sub ⟨3, by linear_combination hax⟩)
  rw [cubic_reciprocity ha hx,hxa,cubic_reciprocity hx hr] at hleft
  exact mul_right_cancel₀ hn hleft

/-- The ramified supplementary factor depends only on the primary argument modulo nine. -/
lemma cubicSymbol_three_periodic {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : (9 : Eisenstein) ∣ a-b) : cubicSymbol a 3 = cubicSymbol b 3 := by
  obtain ⟨d, hd⟩ := hab
  obtain ⟨s, t, ht⟩ := (primary_coprime_three' hb).pow_right (n := 2)
  have ht' : s*b + t*9 = 1 := by convert ht using 1; norm_num
  let r := a - 3 - 9*a*t
  let x := 1 + 3*a*t
  let y := x - 3*d
  have hr : primary r := by
    obtain ⟨k,hk⟩ := ha
    exact ⟨k - 1 - 3*a*t, by dsimp [r]; linear_combination hk⟩
  have hx : primary x := ⟨a*t, by dsimp [x]; ring⟩
  have hy : primary y := ⟨a*t-d, by dsimp [y,x]; ring⟩
  have har : IsCoprime a r := by
    obtain ⟨u,v,hv⟩ := primary_coprime_three' ha
    refine ⟨u + v*(1-9*t), -v, ?_⟩
    dsimp [r]
    linear_combination hv
  have hbr : IsCoprime b r := by
    obtain ⟨u,v,hv⟩ := primary_coprime_three' hb
    refine ⟨u + v*a*s, -v, ?_⟩
    dsimp [r]
    linear_combination hv + v*a*ht'
  have hax : a-r = 3*x := by dsimp [r,x]; ring
  have hby : b-r = 3*y := by dsimp [r,y,x]; linear_combination -hd
  exact (symbol_three_aux ha hr hx hax har).trans
    (symbol_three_aux hb hr hy hby hbr).symm

lemma cubicSymbol_lambda_periodic {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : (9 : Eisenstein) ∣ a-b) : cubicSymbol a lambdaE = cubicSymbol b lambdaE := by
  have he := cubicSymbol_three_periodic ha hb hab
  have hsa : cubicSymbol a 3 = cubicSymbol a lambdaE ^ 2 := by
    rw [← neg_neg (3 : Eisenstein), ← lambdaE_sq, cubicSymbol_neg ha,
      cubicSymbol_pow_upper ha]
  have hsb : cubicSymbol b 3 = cubicSymbol b lambdaE ^ 2 := by
    rw [← neg_neg (3 : Eisenstein), ← lambdaE_sq, cubicSymbol_neg hb,
      cubicSymbol_pow_upper hb]
  rw [hsa,hsb] at he
  have hca := cubicSymbol_cube_of_isCoprime ha lambdaE (primary_coprime_lambda ha)
  have hcb := cubicSymbol_cube_of_isCoprime hb lambdaE (primary_coprime_lambda hb)
  calc
    cubicSymbol a lambdaE = (cubicSymbol a lambdaE ^ 2)^2 := by
      calc
        _ = cubicSymbol a lambdaE * cubicSymbol a lambdaE ^ 3 := by rw [hca,mul_one]
        _ = _ := by ring
    _ = (cubicSymbol b lambdaE ^ 2)^2 := congrArg (· ^ 2) he
    _ = cubicSymbol b lambdaE := by
      calc
        _ = cubicSymbol b lambdaE * cubicSymbol b lambdaE ^ 3 := by ring
        _ = _ := by rw [hcb,mul_one]

private lemma normNat_int (a : Eisenstein) : (normNat a : ℤ) = Algebra.norm ℤ a := by
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_natCast, normNat_cast] using (algebra_norm_cast a).symm

private lemma primary_norm_third {a : Eisenstein} (ha : primary a) :
    ∃ k : ℤ, (normNat a : ℤ) = 3*k+1 := by
  obtain ⟨z,hz⟩ := ha
  obtain ⟨⟨x,y⟩,rfl⟩ := ofCoords_surjective z
  have he : a = ofCoords (1+3*x) (3*y) := by
    dsimp only [ofCoords] at hz ⊢
    push_cast
    linear_combination hz
  rw [normNat_int,he,algebra_norm_ofCoords]
  refine ⟨2*x-y+3*(x^2-x*y+y^2),?_⟩
  ring

private lemma symbol_omega_prime {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbol p omegaE = omega ^ ((normNat p-1)/3) := by
  let k := (normNat p-1)/3
  let j : Fin 3 := ⟨k%3, Nat.mod_lt _ (by decide)⟩
  have he : omegaE^(j : ℕ) = omegaE^k := by
    change omegaE ^ (k%3) = _
    simpa only [← omegaE_primitive.eq_orderOf] using pow_mod_orderOf omegaE k
  rw [cubicSymbol_prime hp]
  have hu : IsUnit (Ideal.Quotient.mk (modulus p) omegaE) :=
    omegaE_isUnit.map (Ideal.Quotient.mk (modulus p))
  rw [cubicSymbol_euler_value hp hu j (congrArg (Ideal.Quotient.mk (modulus p)) he.symm)]
  change omega^(k%3) = omega^k
  simpa only [← omega_primitive.eq_orderOf] using pow_mod_orderOf omega k

/-- Euler's definition for the unit factor, with an integer exponent convenient for congruences. -/
lemma cubicSymbol_omega_norm {a : Eisenstein} (ha : primary a) :
    cubicSymbol a omegaE = omega ^ (((normNat a : ℤ)-1)/3) := by
  apply primary_induction (b := a) ?_ ?_ ha
  · norm_num [cubicSymbol_one_lower, normNat_of_isUnit isUnit_one]
  · intro p a hp ha ih
    obtain ⟨j,hj⟩ := primary_norm_third hp.1
    obtain ⟨k,hk⟩ := primary_norm_third ha
    have hpN : 1 ≤ normNat p := Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hp.2.ne_zero)
    have hcast : (((normNat p-1)/3 : ℕ) : ℤ) = j := by
      rw [Int.natCast_div, Int.natCast_sub hpN,hj]
      omega
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero ha), symbol_omega_prime hp, ih,
      ← zpow_natCast, hcast, normNat_mul, Nat.cast_mul, hj,hk]
    have hdiv : (((3*j+1)*(3*k+1)-1)/3 : ℤ) = j+k+3*(j*k) := by
      apply Int.ediv_eq_of_eq_mul_right (by decide : (3 : ℤ) ≠ 0)
      ring
    have hdk : (3*k+1-1)/3 = k := by omega
    rw [hdk,hdiv,zpow_add₀ omega_ne_zero,zpow_add₀ omega_ne_zero,
      zpow_mul,show omega ^ (3 : ℤ) = 1 by simpa using omega_cube,one_zpow,mul_one]

lemma cubicSymbol_omega_periodic {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : (9 : Eisenstein) ∣ a-b) : cubicSymbol a omegaE = cubicSymbol b omegaE := by
  obtain ⟨d,hd⟩ := hab
  obtain ⟨⟨x,y⟩,he⟩ := ofCoords_surjective b
  obtain ⟨⟨z,w⟩,hf⟩ := ofCoords_surjective d
  have ha' : a = ofCoords (x+9*z) (y+9*w) := by
    rw [← he,← hf] at hd
    dsimp only [ofCoords] at hd ⊢
    push_cast
    linear_combination hd
  have hn : (9 : ℤ) ∣ (normNat a : ℤ) - normNat b := by
    rw [normNat_int,normNat_int,ha',← he,algebra_norm_ofCoords,algebra_norm_ofCoords]
    refine ⟨2*x*z-x*w-z*y+2*y*w+9*(z^2-z*w+w^2),?_⟩
    ring
  obtain ⟨j,hj⟩ := primary_norm_third ha
  obtain ⟨k,hk⟩ := primary_norm_third hb
  obtain ⟨t,ht⟩ := hn
  have hjk : j = k+3*t := by omega
  rw [cubicSymbol_omega_norm ha,cubicSymbol_omega_norm hb,hj,hk]
  have hdj : (3*j+1-1)/3 = j := by omega
  have hdk : (3*k+1-1)/3 = k := by omega
  rw [hdj,hdk,hjk,zpow_add₀ omega_ne_zero,zpow_mul,
    show omega ^ (3 : ℤ) = 1 by simpa using omega_cube,one_zpow,mul_one]

private lemma unit_eq_signed_omega {u : Eisenstein} (hu : IsUnit u) :
    ∃ j : ℕ, u = omegaE^j ∨ u = -(omegaE^j) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective u
  have hn : a^2-a*b+b^2 = 1 := by
    have hh := norm_of_isUnit hu
    rw [norm,ofCoords_coe,coordinates_norm] at hh
    exact_mod_cast hh
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor
    · by_contra h
      have hh : a ≤ -2 := by omega
      nlinarith [sq_nonneg (a-2*b)]
    · by_contra h
      have hh : 2 ≤ a := by omega
      nlinarith [sq_nonneg (a-2*b)]
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor
    · by_contra h
      have hh : b ≤ -2 := by omega
      nlinarith [sq_nonneg (2*a-b)]
    · by_contra h
      have hh : 2 ≤ b := by omega
      nlinarith [sq_nonneg (2*a-b)]
  obtain ⟨ha0,ha1⟩ := ha
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num at hn
  · exact ⟨2, Or.inl (by dsimp [ofCoords]; push_cast; linear_combination -omegaE_quadratic)⟩
  · exact ⟨0, Or.inr (by norm_num [ofCoords])⟩
  · exact ⟨1, Or.inr (by norm_num [ofCoords])⟩
  · exact ⟨1, Or.inl (by norm_num [ofCoords])⟩
  · exact ⟨0, Or.inl (by norm_num [ofCoords])⟩
  · exact ⟨2, Or.inr (by dsimp [ofCoords]; push_cast; linear_combination omegaE_quadratic)⟩

lemma cubicSymbol_unit_periodic {a b u : Eisenstein} (ha : primary a) (hb : primary b)
    (hu : IsUnit u) (hab : (9 : Eisenstein) ∣ a-b) :
    cubicSymbol a u = cubicSymbol b u := by
  obtain ⟨j,hj | hj⟩ := unit_eq_signed_omega hu
  · rw [hj,cubicSymbol_pow_upper ha,cubicSymbol_pow_upper hb,
      cubicSymbol_omega_periodic ha hb hab]
  · rw [hj,cubicSymbol_neg ha,cubicSymbol_neg hb,cubicSymbol_pow_upper ha,
      cubicSymbol_pow_upper hb,cubicSymbol_omega_periodic ha hb hab]

private lemma unit_coprime_right (b : Eisenstein) {u : Eisenstein} (hu : IsUnit u) :
    IsCoprime b u := by
  obtain ⟨z,hz⟩ := isUnit_iff_exists_inv'.mp hu
  exact ⟨0,z,by simpa only [zero_mul,zero_add] using hz⟩

private lemma normNat_lambda : normNat lambdaE = 3 := by
  have hh := congrArg normNat lambdaE_sq
  rw [pow_two,normNat_mul] at hh
  have hn : normNat (-3 : Eisenstein) = 9 := by
    apply Nat.cast_injective (R := ℝ)
    rw [normNat_cast]
    change Complex.normSq (-(3 : ℂ)) = 9
    norm_num [Complex.normSq_apply]
  rw [hn] at hh
  nlinarith

private lemma lambda_irreducible : Irreducible lambdaE := by
  refine ⟨?_,?_⟩
  · intro hu
    have hh := normNat_of_isUnit hu
    rw [normNat_lambda] at hh
    norm_num at hh
  · intro x y h
    have hh : normNat x * normNat y = 3 := by rw [← normNat_mul,← h,normNat_lambda]
    have hor := (show Irreducible (3 : ℕ) from Nat.prime_three).isUnit_or_isUnit hh.symm
    have reflect {z : Eisenstein} (hz : IsUnit (normNat z)) : IsUnit z := by
      apply isUnit_of_norm_eq_one
      rw [← normNat_cast,Nat.isUnit_iff.mp hz]
      norm_num
    exact hor.imp reflect reflect

/-- Explicit classification of the six Eisenstein units. -/
lemma eisenstein_unit_eq_signed_omega {u : Eisenstein} (hu : IsUnit u) :
    ∃ j : ℕ, u = omegaE^j ∨ u = -(omegaE^j) := unit_eq_signed_omega hu

lemma lambdaE_prime : Prime lambdaE := irreducible_iff_prime.mp lambda_irreducible

/-- All nonzero numerators, with the usual zero extension at common factors. -/
theorem cubicSupplementaryPeriodicity_proved : CubicSupplementaryPeriodicity := by
  intro v hv
  have main : ∀ v : Eisenstein, v ≠ 0 → ∀ a b : Eisenstein,
      primary a → primary b → (9*v) ∣ a-b → cubicSymbol a v = cubicSymbol b v := by
    intro v
    induction v using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit u hu =>
      intro _ a b ha hb hab
      exact cubicSymbol_unit_periodic ha hb hu ((dvd_mul_right 9 u).trans hab)
    | mul v p hv hp ih =>
      intro _ a b ha hb hab
      have h9 : (9 : Eisenstein) ∣ a-b := (dvd_mul_right 9 (p*v)).trans hab
      rw [cubicSymbol_mul_upper ha,cubicSymbol_mul_upper hb]
      congr 1
      · by_cases hp3 : IsCoprime p 3
        · obtain ⟨u,hu,hprim⟩ := unit_lift_mod_three (residue_isUnit_of_isCoprime hp3.symm)
          have heA : cubicSymbol a (p*u) = cubicSymbol (p*u) a := cubic_reciprocity ha hprim
          have heB : cubicSymbol b (p*u) = cubicSymbol (p*u) b := cubic_reciprocity hb hprim
          have hpv : p ∣ a-b := (dvd_mul_right p v).trans
            ((dvd_mul_left (p*v) 9).trans hab)
          have hpu : p*u ∣ a-b := by
            exact (associated_mul_unit_right p u hu).dvd_iff_dvd_left.mp hpv
          have heq := cubicSymbol_congr (b := p*u) (residue_eq_of_dvd_sub hpu)
          rw [cubicSymbol_mul_upper ha] at heA
          rw [cubicSymbol_mul_upper hb] at heB
          have huu := cubicSymbol_unit_periodic ha hb hu h9
          rw [← heA,← heB,huu] at heq
          apply mul_right_cancel₀ _ heq
          intro hz
          have hnorm := norm_cubicSymbol_of_isCoprime hb
            (show IsCoprime b u from unit_coprime_right b hu)
          rw [hz,norm_zero] at hnorm
          norm_num at hnorm
        · have hpd : p ∣ (3 : Eisenstein) := by
            by_contra h
            exact hp3 (isRelPrime_iff_isCoprime.mp (hp.isRelPrime_iff_not_dvd.mpr h))
          have hpl : p ∣ lambdaE := hp.prime.dvd_of_dvd_pow
            (by rw [lambdaE_sq]; exact dvd_neg.mpr hpd)
          have hpunit : Associated p lambdaE :=
            (hp.associated_of_dvd lambda_irreducible hpl)
          obtain ⟨u,hu⟩ := hpunit
          have hunit := cubicSymbol_unit_periodic ha hb u.isUnit h9
          have hlam := cubicSymbol_lambda_periodic ha hb h9
          have he : cubicSymbol a (p*(u : Eisenstein)) =
              cubicSymbol b (p*(u : Eisenstein)) := by simpa only [hu] using hlam
          rw [cubicSymbol_mul_upper ha,cubicSymbol_mul_upper hb,hunit] at he
          apply mul_right_cancel₀ _ he
          intro hz
          have hnorm := norm_cubicSymbol_of_isCoprime hb (unit_coprime_right b u.isUnit)
          rw [hz,norm_zero] at hnorm
          norm_num at hnorm
      · apply ih hv a b ha hb
        apply dvd_trans _ hab
        refine ⟨p,?_⟩
        ring
  exact main v hv

end CubicFirstMoment

end

end OAI
