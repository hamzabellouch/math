import OAI.NumberTheory.DirichletL.Reciprocity.CubicJacobi
import OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

def cubicExp (n : ℤ) : O := omega ^ (n % 3).toNat

lemma cubicExp_eq_of_dvd_sub {a b : ℤ} (h : 3 ∣ a - b) : cubicExp a = cubicExp b := by
  obtain ⟨k, hk⟩ := h
  have heq : a % 3 = b % 3 := by omega
  simp only [cubicExp, heq]

lemma cubicExp_add (a b : ℤ) : cubicExp (a + b) = cubicExp a * cubicExp b := by
  simp only [cubicExp, ← pow_add]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  omega

@[simp] lemma cubicExp_zero : cubicExp 0 = 1 := by simp [cubicExp]

def linearRay (u v : ℤ) (x : O) : O :=
  cubicExp (u * (((ActualEisensteinCoordinates.coords x).1 - 1) / 3) +
    v * ((ActualEisensteinCoordinates.coords x).2 / 3))

lemma linearRay_primaryCoord (u v A B : ℤ) :
    linearRay u v (primaryCoord A B) = cubicExp (u*A + v*B) := by
  simp only [linearRay, primaryCoord, ShortDraftLatticeCount.coords_eval]
  rw [show (1 + 3*A - 1) / 3 = A by omega,
    show 3*B / 3 = B by omega]

lemma exists_primaryCoord (x : O) (hx : lambda ^ 2 ∣ x - 1) :
    ∃ A B : ℤ, x = primaryCoord A B := by
  have hthree : (3 : O) ∣ lambda ^ 2 := by
    refine ⟨-omega, ?_⟩
    rw [lambda_def]
    linear_combination omega_sq_for_norm
  obtain ⟨z, hz⟩ := hthree.trans hx
  obtain ⟨A, B, hAB⟩ := ActualEisensteinCoordinates.exists_coordinates z
  change z = (A : O) + (B : O) * omega at hAB
  refine ⟨A, B, ?_⟩
  rw [primaryCoord_eq]
  rw [hAB] at hz
  linear_combination hz

lemma primaryCoord_mul (A B C D : ℤ) :
    primaryCoord A B * primaryCoord C D =
      primaryCoord (A+C+3*(A*C-B*D)) (B+D+3*(A*D+B*C-B*D)) := by
  simp only [primaryCoord, ActualEisensteinCoordinates.eval_mul]
  congr 1 <;> ring

lemma linearRay_one (u v : ℤ) : linearRay u v 1 = 1 := by
  have hone : (1 : O) = primaryCoord 0 0 := by rw [primaryCoord_eq]; simp
  conv_lhs => rw [hone, linearRay_primaryCoord]
  simp

lemma linearRay_mul (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) :
    linearRay u v (x*y) = linearRay u v x * linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  rw [primaryCoord_mul]
  simp only [linearRay_primaryCoord]
  rw [← cubicExp_add]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*(A*C-B*D)+v*(A*D+B*C-B*D), ?_⟩
  ring

theorem symbol_eq_linearRay_of_prime (x : O) (u v : ℤ)
    (hprime : ∀ p : O, Prime p → lambda ^ 2 ∣ p-1 → symbol x p = linearRay u v p)
    (y : O) (hy : lambda ^ 2 ∣ y-1) : symbol x y = linearRay u v y := by
  obtain ⟨A,B,hyAB⟩ := exists_primaryCoord y hy
  have hy0 : y ≠ 0 := by rw [hyAB]; exact primaryCoord_ne_zero A B
  obtain ⟨s,hsprod,hs⟩ := exists_primary_prime_factorization y hy0 hy
  rw [← hsprod]
  clear hsprod hyAB hy hy0 A B y
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero, symbol_one, linearRay_one]
  | @cons p s ih =>
    have hp := hs p (Multiset.mem_cons_self _ _)
    have hss : ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r-1 :=
      fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    rw [Multiset.prod_cons, symbol_mul_denominator,
      hprime p hp.1 hp.2, ih hss,
      linearRay_mul u v p s.prod hp.2 (primary_multiset_prod s (fun r hr => (hss r hr).2))]

theorem symbol_lambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol lambda y = linearRay 1 0 y := by
  apply symbol_eq_linearRay_of_prime lambda 1 0 _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_lambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp]

theorem symbol_omega_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol omega y = linearRay 2 (-1) y := by
  apply symbol_eq_linearRay_of_prime omega 2 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_omega_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp, sub_eq_add_neg]

theorem cubicValue_traceLambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P traceLambda) = cubicExp (-B) := by
  have htrace : traceLambda = -omega * lambda := by
    change 1 + 2 * omega = -omega * (omega - 1)
    linear_combination omega_sq_for_norm
  rw [htrace, map_mul, map_mul, cubicValue_neg,
    cubicValue_omega_primary P hg A B hP, cubicValue_lambda_primary P hg A B hP]
  change cubicExp (2*A-B) * cubicExp A = cubicExp (-B)
  rw [← cubicExp_add]
  exact cubicExp_eq_of_dvd_sub ⟨A, by ring⟩

theorem symbol_traceLambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol traceLambda y = linearRay 0 (-1) y := by
  apply symbol_eq_linearRay_of_prime traceLambda 0 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_traceLambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp

theorem linearRay_congr_mod_nine (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    linearRay u v x = linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  obtain ⟨z,hz⟩ := hxy
  obtain ⟨E,F,hEF⟩ := ActualEisensteinCoordinates.exists_coordinates z
  change z = (E : O) + (F : O) * omega at hEF
  have hcoords : ActualEisensteinCoordinates.eval (3*(A-C)) (3*(B-D)) =
      ActualEisensteinCoordinates.eval (9*E) (9*F) := by
    have he (a b : ℤ) : ActualEisensteinCoordinates.eval a b =
        (a : O) + (b : O) * omega := rfl
    simp only [he]
    rw [hEF, primaryCoord_eq, primaryCoord_eq] at hz
    push_cast
    linear_combination hz
  have hab := ActualEisensteinCoordinates.unique_coordinates hcoords
  have ha : A-C = 3*E := by omega
  have hb : B-D = 3*F := by omega
  rw [linearRay_primaryCoord, linearRay_primaryCoord]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*E+v*F, ?_⟩
  linear_combination u*ha + v*hb

theorem symbol_lambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol lambda x = symbol lambda y := by
  rw [symbol_lambda_eq_linearRay x hx, symbol_lambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 1 0 x y hx hy hxy

theorem symbol_traceLambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol traceLambda x = symbol traceLambda y := by
  rw [symbol_traceLambda_eq_linearRay x hx, symbol_traceLambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 0 (-1) x y hx hy hxy

end CubicRamified

namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified

theorem primary_ne_zero (a : O) (ha : lambda ^ 2 ∣ a-1) : a ≠ 0 := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  exact primaryCoord_ne_zero A B

theorem symbol_one_numerator (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol 1 a = 1 := by
  apply idealSymbol_map_one
  rw [primaryGenerator_span a (primary_ne_zero a ha) ha]
  exact primary_ne_zero a ha

theorem symbol_mul_numerator (x y a : O) (ha : lambda ^ 2 ∣ a-1) :
    symbol (x*y) a = symbol x a * symbol y a := by
  apply idealSymbol_map_mul
  rw [primaryGenerator_span a (primary_ne_zero a ha) ha]
  exact primary_ne_zero a ha

theorem symbol_pow_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) (n : ℕ) :
    symbol (x^n) a = symbol x a ^ n := by
  induction n with
  | zero => simp only [pow_zero, symbol_one_numerator a ha]
  | succ n ih => rw [pow_succ, symbol_mul_numerator _ _ a ha, ih, pow_succ]

theorem symbol_neg_one (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol (-1) a = 1 := by
  have h := symbol_eq_linearRay_of_prime (-1) 0 0 (fun p hp hprimary => by
    let : (Ideal.span {p} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
      primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
    rw [symbol, idealSymbol_prime _ hg, map_neg, map_one, A3_cubicChar_neg_one]
    simp [linearRay]) a ha
  simpa [linearRay] using h

theorem symbol_neg_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) :
    symbol (-x) a = symbol x a := by
  rw [neg_eq_neg_one_mul, symbol_mul_numerator _ _ a ha, symbol_neg_one a ha, one_mul]

theorem symbol_isUnit_ne_zero (x a : O) (hx : IsUnit x) (ha : lambda ^ 2 ∣ a-1) :
    symbol x a ≠ 0 := by
  obtain ⟨u,rfl⟩ := hx
  have h : symbol (u : O) a * symbol (↑u⁻¹ : O) a = 1 := by
    rw [← symbol_mul_numerator _ _ a ha, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, symbol_one_numerator a ha]
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem symbol_unit_congr_mod_nine (x a b : O) (hx : IsUnit x)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b) :
    symbol x a = symbol x b := by
  obtain ⟨u,rfl⟩ := hx
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η^2, -η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega a = symbol omega b := by
    rw [symbol_omega_eq_linearRay a ha, symbol_omega_eq_linearRay b hb]
    exact linearRay_congr_mod_nine 2 (-1) a b ha hb hab
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · simp only [h, Units.val_one, symbol_one_numerator _ ha, symbol_one_numerator _ hb]
  · simp only [h, Units.val_neg, Units.val_one, symbol_neg_one _ ha, symbol_neg_one _ hb]
  · simpa only [h, hη] using hω
  · simpa only [h, Units.val_neg, hη, symbol_neg_numerator _ _ ha,
      symbol_neg_numerator _ _ hb] using hω
  · simpa only [h, Units.val_pow_eq_pow_val, hη, symbol_pow_numerator _ _ ha,
      symbol_pow_numerator _ _ hb] using congrArg (fun t : O => t^2) hω
  · simpa only [h, Units.val_neg, Units.val_pow_eq_pow_val, hη,
      symbol_neg_numerator _ _ ha, symbol_neg_numerator _ _ hb,
      symbol_pow_numerator _ _ ha, symbol_pow_numerator _ _ hb]
      using congrArg (fun t : O => t^2) hω

private theorem associated_congr_denominator {x y a b : O} (hxy : Associated x y)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b)
    (hy : symbol y a = symbol y b) : symbol x a = symbol x b := by
  obtain ⟨u,hu⟩ := hxy
  apply mul_right_cancel₀ (symbol_isUnit_ne_zero (u : O) a u.isUnit ha)
  calc
    symbol x a * symbol (u : O) a = symbol y a := by
      rw [← symbol_mul_numerator _ _ a ha, hu]
    _ = symbol y b := hy
    _ = symbol x b * symbol (u : O) b := by rw [← hu, symbol_mul_numerator _ _ b hb]
    _ = symbol x b * symbol (u : O) a := by
      rw [symbol_unit_congr_mod_nine (u : O) b a u.isUnit hb ha (by simpa only [neg_sub] using dvd_neg.mpr hab)]

private theorem ramified_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

private theorem symbol_prime_denominator_congr (p a b : O) (hp : Prime p)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hpab : p ∣ a-b) : symbol p a = symbol p b := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  by_cases hg : lambda ∉ (Ideal.span {p} : Ideal O)
  · obtain ⟨q,hq,hprimary,-⟩ := cubicJacobi_exists_primary_generator (Ideal.span {p}) hg
    have hpq : Associated p q := Ideal.span_singleton_eq_span_singleton.mp hq
    apply associated_congr_denominator hpq ha hb h9
    have hq0 : q ≠ 0 := (hpq.prime_iff.mp hp).ne_zero
    rw [symbol_reciprocity q a hq0 (primary_ne_zero a ha) hprimary ha,
      symbol_reciprocity q b hq0 (primary_ne_zero b hb) hprimary hb]
    exact symbol_congr (hpq.dvd'.trans hpab)
  · have hdiv : p ∣ lambda := Ideal.mem_span_singleton.mp (not_not.mp hg)
    apply associated_congr_denominator (hp.associated_of_dvd ramified_prime hdiv) ha hb h9
    exact symbol_lambda_congr_mod_nine a b ha hb h9

theorem symbol_denominator_congr (x a b : O)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hx : x ∣ a-b) : symbol x a = symbol x b := by
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => have heq : a = b := sub_eq_zero.mp (zero_dvd_iff.mp hx); rw [heq]
  | h₂ u hu => exact symbol_unit_congr_mod_nine u a b hu ha hb h9
  | h₃ x p hx0 hp ih =>
    have hpab : p ∣ a-b := (dvd_mul_right p x).trans hx
    have hxab : x ∣ a-b := (dvd_mul_left x p).trans hx
    rw [symbol_mul_numerator _ _ a ha, symbol_mul_numerator _ _ b hb,
      symbol_prime_denominator_congr p a b hp ha hb h9, ih hxab]
    exact hpab

end CubicJacobiGlobal

namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic ActualEisensteinCoordinates ShortDraftLatticeCount

def unitCoordinates : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

theorem q_eq_one_iff_unitCoordinates (z : ℤ × ℤ) : q z = 1 ↔ z ∈ unitCoordinates := by
  rcases z with ⟨a, b⟩
  constructor
  · intro h
    have hs := coordinate_squares a b 1 (by norm_num) (le_of_eq h)
    have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 1)]
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    interval_cases a <;> interval_cases b <;> norm_num [q, unitCoordinates] at *
  · intro h
    simp only [unitCoordinates, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h <;> rw [h] <;> norm_num [q]

theorem unit_coordinate_mem (u : Oˣ) : coords u.val ∈ unitCoordinates := by
  apply (q_eq_one_iff_unitCoordinates _).mp
  have hn := (rational_qNat_eq_one_iff u.val).mpr u.isUnit
  have hz := qO_nonneg u.val
  change (q (coords u.val)).toNat = 1 at hn
  have hi : ((q (coords u.val)).toNat : ℤ) = 1 := by exact_mod_cast hn
  simpa only [Int.toNat_of_nonneg hz] using hi

def unitCoordinateMap (u : Oˣ) : {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  ⟨coords u.val, unit_coordinate_mem u⟩

theorem unitCoordinateMap_bijective : Function.Bijective unitCoordinateMap := by
  constructor
  · intro u v huv
    apply Units.ext
    have hc := congrArg Subtype.val huv
    have he := congrArg (fun z : ℤ × ℤ => eval z.1 z.2) hc
    simpa only [unitCoordinateMap, eval_coords] using he
  · intro z
    have hq := (q_eq_one_iff_unitCoordinates z.val).mpr z.property
    have hu : IsUnit (eval z.val.1 z.val.2) := by
      apply (rational_qNat_eq_one_iff _).mp
      simp only [qNat, coords_eval, hq]
      norm_num
    refine ⟨hu.unit, Subtype.ext ?_⟩
    change coords hu.unit.val = z.val
    rw [hu.unit_spec, coords_eval]

def unitCoordinateEquiv : Oˣ ≃ {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  Equiv.ofBijective unitCoordinateMap unitCoordinateMap_bijective

theorem card_units_eq_six : Nat.card Oˣ = 6 := by
  rw [Nat.card_congr unitCoordinateEquiv, Nat.card_eq_fintype_card, Fintype.card_coe]
  norm_num [unitCoordinates]

end PrimaryIdealUnitReindex

open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss

theorem rowCoprimeMask_unit_mul {α : Type*} (R : α → Ideal O)
    (S : Finset α) (u : Oˣ) (z : O) :
    rowCoprimeMask R S (u.val * z) = rowCoprimeMask R S z := by
  simp only [rowCoprimeMask, Ideal.unit_mul_mem_iff_mem _ u.isUnit]

theorem rowCoprimeMask_norm_le_one {α : Type*} (R : α → Ideal O)
    (S : Finset α) (z : O) : ‖rowCoprimeMask R S z‖ ≤ 1 := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem masked_two_rows_radial_summable
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (Q : κ → Ideal O) [∀ i, (Q i).IsMaximal] (hgq : ∀ i, lambda ∉ Q i) (k : κ → ℕ)
    (R : α → Ideal O) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowCoprimeMask R S z *
      (finiteSexticRow P hg j z * finiteSexticRow Q hgq k z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hW
  intro z
  simp only [norm_mul]
  calc
    _ ≤ 1 * (1 * 1) * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ := by
      gcongr
      · exact rowCoprimeMask_norm_le_one R S z
      · exact QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j z
      · exact QuadraticInitialBound.finiteSexticRow_norm_le_one Q hgq k z
    _ = _ := by ring

theorem quadratic_pair_lattice_eq_primary_ideal_sum
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i))
    (R : α → Ideal O) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (primaryGenerator I.val)) *
      W ((Ideal.absNorm I.val : ℝ) / M) := by
  have hs := masked_two_rows_radial_summable (fun i => Ideal.span {p i}) hg (fun _ => 3)
    (fun i => Ideal.span {q i}) hgq (fun _ => 3) R S W M hM
  have hu (u : Oˣ) (I : GoodIdeal) :
      rowCoprimeMask R S (u.val * primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (u.val * primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (u.val * primaryGenerator I.val)) *
      W (‖eisEmbedding (u.val * primaryGenerator I.val)‖ ^ 2 / M) =
      rowCoprimeMask R S (primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (primaryGenerator I.val)) *
      W (‖eisEmbedding (primaryGenerator I.val)‖ ^ 2 / M) := by
    rw [rowCoprimeMask_unit_mul, quadratic_pair_unit_invariant p hp hcop hg hchar
      q hq hcopq hgq hcharq hray, norm_eisEmbedding_unit_mul]
  have ht := tsum_ramified_mask_unit_invariant _ hs hu
  have hn (I : GoodIdeal) := primaryGenerator_norm_sq I.val I.property
  simpa only [hn] using ht

end QuadraticUnitInvariance

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem canonical_masked_radial_poisson_product
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z * finiteSexticRow (fun i => Ideal.span {p i}) hg j z *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    ((M : ℂ) * canonicalProductGauss p hp hcop hg j / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator R E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
          finiteSexticRow (fun i => Ideal.span {p i}) hg j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by
  have ht := canonical_masked_radial_poisson_collected R hinj S
    (fun i => Ideal.span {p i}) hcop hg hchar j hj0 hj6 W M hM
  dsimp only at ht
  rw [finitePrimeModulus_norm_eq_product p] at ht
  rw [ht]
  let a : Finset α → ℂ := fun E =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
      finiteSexticRow (fun i => Ideal.span {p i}) hg j (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let F : Finset α → ℝ → ℂ := fun E t => paperRadialFourier W
    (M * t / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  have hu := gauss_weighted_finite_radial_sum_transport p hp hcop hg j S.powerset a F
  change ((M : ℂ) * canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j /
      (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (∑ E ∈ S.powerset, a E * ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          F E (‖eisEmbedding h‖ ^ 2)) = _
  calc
    _ = ((M : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j *
        ∑ E ∈ S.powerset, a E * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [hu]; ring
end GaussGeneratorTransport

namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson

theorem odd_of_quadraticRayValue_norm_eq_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : ‖quadraticRayValue r‖ = 1) : EisensteinEPrimaryPhase.odd r := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd, quadraticRayValue, breveGaussianFourTerms_formula,
      zpow_neg, Complex.I_sq, Complex.I_pow_three, Complex.inv_I, ZMod.val] at *

theorem quadraticBlock_union_eq_one_of_same_ray
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i)) :
    quadraticBlock p hp hg (A ∪ B) = 1 := by
  have hnorm := norm_quadraticBlock p hp hcop hg hchar A
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar A] at hnorm
  have hodd := odd_of_quadraticRayValue_norm_eq_one _ hnorm
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B), Finset.prod_union hd]
  exact quadraticRayValue_same_residue_product _ _ hodd hray

theorem same_ray_quadratic_pair_poisson
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i))
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := ∏ i ∈ A ∪ B, p i
    let χ := fun z => quadraticRow (fun i => Ideal.span {p i}) hg A z *
      quadraticRow (fun i => Ideal.span {p i}) hg B z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hcAB : Pairwise (Function.onFun IsCoprime
      (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})) := by
    intro i k hik
    exact hcop (fun h => hik (Subtype.ext h))
  have ht := canonical_masked_radial_poisson_product R hinj S
    (fun i : (A ∪ B : Finset ι) => p i.val) (fun i => hp i.val) hcAB
    (fun i => hg i.val) (fun i => hchar i.val) (fun _ => 3)
    (fun _ => by decide) (fun _ => by decide) W M hM
  have hγ := quadraticBlock_union_eq_one_of_same_ray p hp hcop hg hchar A B hd hray
  rw [quadraticBlock_eq_productGauss p hp hcop hg (A ∪ B)] at hγ
  rw [hγ, mul_one, Finset.prod_coe_sort] at ht
  have hrow (z : O) : finiteSexticRow (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})
      (fun i => hg i.val) (fun _ => 3) z =
      quadraticRow (fun i => Ideal.span {p i}) hg A z *
        quadraticRow (fun i => Ideal.span {p i}) hg B z := by
    rw [← quadraticRow_eq_canonical (fun i => Ideal.span {p i}) hg (A ∪ B) z,
      quadraticRow_disjoint_union _ _ _ _ hd]
  simp only [hrow, star_mul, quadraticRow_star] at ht
  simpa only [mul_comm] using ht

end QuadraticUnitInvariance

open scoped BigOperators Classical SchwartzMap
namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

theorem paperRadialFourier_nonzero_lattice_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        (∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let F : O → ℝ := fun h => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖
  have hs := paperRadialFourier_lattice_summable_norm W K hK0
  let f : {h : O // h ≠ 0} → {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, by nlinarith [one_le_eisenstein_norm_sq h.val h.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg
      (fun z : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // h ≠ 0}, F h.val) ≤
      ∑' h : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2}, F h.val := by
    exact (hs.subtype (fun h => h ≠ 0)).tsum_le_tsum_of_inj f hf
      (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  have ht := hb W K K hK0 hK0.le
  simpa only [min_eq_left hK, one_pow, one_mul] using hi.trans ht

theorem paperRadialFourier_nonzero_sum_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_lattice_decay A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hs := paperRadialFourier_lattice_summable_norm W K (lt_of_lt_of_le zero_lt_one hK)
  have he : (∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)) =
      ∑' h : {h : O // h ≠ 0}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [ite_eq_right h.property]
  rw [he]
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hb W K hK)

theorem principal_tail_scalar (A : ℕ) (B x N M : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxN : x ≤ N) (hM : 0 < M) :
    (M / x) * (B / (1 + M / x) ^ (A + 1)) ≤ B * (N / M) ^ A := by
  have hu : 0 < M / x := div_pos hM hx
  calc
    _ ≤ (M / x) * (B / (M / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / M) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (N / M) ^ A := by
      gcongr

theorem maskedPrincipalRemainder_large_scale (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) ≤ M →
        ‖maskedPrincipalRemainder P S W M‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_sum_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro α _ P _ S W M hM hsize
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hnN (E : Finset α) (hE : E ∈ S.powerset) : n E ≤ N := by
    have hd := Finset.prod_dvd_prod_of_subset E S P (Finset.mem_powerset.mp hE)
    have hdN := map_dvd Ideal.absNorm hd
    have hpos : 0 < Ideal.absNorm (∏ i ∈ S, P i) := by
      have hh := hn S
      dsimp only [n] at hh
      exact_mod_cast hh
    dsimp only [n, N]
    exact_mod_cast Nat.le_of_dvd hpos hdN
  have ht (E : Finset α) (hE : E ∈ S.powerset) :
      ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / n E)‖ ≤ B / (1 + M / n E) ^ (A + 1) := by
    have hscale : 1 ≤ M / n E := (le_div_iff₀ (hn E)).mpr (by simpa using (hnN E hE).trans hsize)
    have h := hb W (M / n E) hscale
    convert h using 1 ; congr 2 ; funext z ; congr 2 ; ring
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) (hE : E ∈ S.powerset) :
      ‖f E‖ ≤ (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
    dsimp [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    gcongr
    · exact QuadraticInitialBound.norm_ideal_moebius_le_one _
    · exact ht E hE
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ ≤ M * ∑ E ∈ S.powerset, (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      gcongr with E hE
      exact hf E hE
    _ = ∑ E ∈ S.powerset, (M / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ ≤ ∑ E ∈ S.powerset, B * (N / M) ^ A := by
      apply Finset.sum_le_sum
      intro E hE
      exact principal_tail_scalar A B (n E) N M hB (hn E) (hnN E hE) hM
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

end EisensteinSchwartzPoisson

end

end OAI
