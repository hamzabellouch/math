import OAI.NumberTheory.Jacobsthal.Primes.BadPrimeProduct
import OAI.NumberTheory.Jacobsthal.Primes.PrimeRationalList
import OAI.NumberTheory.Jacobsthal.Probability.PreciseIncidenceMoment
import OAI.NumberTheory.Jacobsthal.Sieve.LargePrimeDivisors

namespace OAI

namespace Erdos970


namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

noncomputable def sourceRationalList (P : Finset ℕ) (a : ℕ → ℤ) (Sq R Z c : ℝ) : Finset ℚ :=
  rationalList P a ⌊Sq*R*Z^10⌋₊ ⌊R*Z^10⌋₊ c

theorem mem_sourceRationalList (P : Finset ℕ) (a : ℕ → ℤ) {Sq R Z c : ℝ}
    (hSq : 0 ≤ Sq) (hR : 0 ≤ R) (q : ℚ) :
    q ∈ sourceRationalList P a Sq R Z c ↔
      (q.num.natAbs : ℝ) ≤ Sq*R*Z^10 ∧ (q.den : ℝ) ≤ R*Z^10 ∧
      c*(P.card : ℝ) ≤ ((P.filter (aligns a q)).card : ℝ) := by
  rw [sourceRationalList,mem_rationalList,
    Nat.le_floor_iff (show 0 ≤ Sq*R*Z^10 by positivity),
    Nat.le_floor_iff (show 0 ≤ R*Z^10 by positivity)]

theorem source_height_product_bound {Sq R Z : ℝ}
    (hSq : 0 ≤ Sq) (hR : 0 ≤ R) :
    ((2*⌊Sq*R*Z^10⌋₊*⌊R*Z^10⌋₊ : ℕ) : ℝ) ≤ 2*Sq*R^2*Z^20 := by
  push_cast
  calc
    _ ≤ (2*(Sq*R*Z^10))*(R*Z^10) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num))
        (Nat.floor_le (by positivity)) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem source_rational_list_bound (P : Finset ℕ) (a : ℕ → ℤ)
    {Sq R Z z α C c : ℝ} (hSq : 0 ≤ Sq) (hR : 0 ≤ R)
    (hz : 1 < z) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c)
    (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,z^α ≤ (p : ℝ))
    (hheight : 2*Sq*R^2*Z^20 ≤ z^C) (hPpos : 0 < P.card)
    (henough : 2*(C/α) ≤ c^2*(P.card : ℝ)) :
    (sourceRationalList P a Sq R Z c).card ≤ ⌈2/c^2⌉₊ := by
  exact prime_rational_list_card_le_ceil P a _ _ hz hα hC hc hP hlarge
    ((source_height_product_bound hSq hR).trans hheight) hPpos henough

end ErdosInverseAlignment



namespace ErdosPrimitiveIntercept
open ErdosRichLine

theorem InterceptReduction.denominator_le {l : PrimitiveIntegerLine} (r : InterceptReduction l) :
    r.rational.den ≤ l.denominator := by
  rw [r.denominator_eq]
  simpa using Nat.mul_le_mul_right r.rational.den (Nat.succ_le_of_lt r.factor_pos)

theorem InterceptReduction.numerator_abs_le {l : PrimitiveIntegerLine} (r : InterceptReduction l) :
    r.rational.num.natAbs ≤ l.intercept.natAbs := by
  rw [r.intercept_eq,Int.natAbs_mul,Int.natAbs_natCast]
  simpa using Nat.mul_le_mul_right r.rational.num.natAbs (Nat.succ_le_of_lt r.factor_pos)

theorem InterceptReduction.height_transfer {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (Hden Hnum : ℝ) (hd : (l.denominator : ℝ) ≤ Hden) (hn : |(l.intercept : ℝ)| ≤ Hnum) :
    (r.rational.den : ℝ) ≤ Hden ∧ |(r.rational.num : ℝ)| ≤ Hnum := by
  have hden : (r.rational.den : ℝ) ≤ l.denominator := by exact_mod_cast r.denominator_le
  have hnum : |(r.rational.num : ℝ)| ≤ |(l.intercept : ℝ)| := by
    have hh : (r.rational.num.natAbs : ℝ) ≤ l.intercept.natAbs := by exact_mod_cast r.numerator_abs_le
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  exact ⟨hden.trans hd,hnum.trans hn⟩

end ErdosPrimitiveIntercept



namespace ErdosPrimitiveIntercept
open ErdosRichLine

theorem exists_canonical_structured_intercept (l : PrimitiveIntegerLine) :
    ∃ (t : ℚ) (g : ℕ), 0 < g ∧ l.denominator = g*t.den ∧ l.intercept = (g : ℤ)*t.num ∧
      t = (l.intercept : ℚ)/(l.denominator : ℚ) ∧
      t.den ≤ l.denominator ∧ t.num.natAbs ≤ l.intercept.natAbs ∧
      (∀ p : ℤ × ℤ, l.Contains p → (g : ℤ) ∣ p.1) ∧
      ∀ (a : ℕ → ℤ) (q : ℕ) (b : ℤ), l.Contains ((q : ℤ),b) →
        (∀ ell ∈ q.primeFactors, (b : ZMod ell) = (a ell : ZMod ell)) →
        t.den*badPrimeProduct a t q ≤ l.denominator := by
  obtain ⟨r⟩ := exists_intercept_reduction l
  exact ⟨r.rational,r.factor,r.factor_pos,r.denominator_eq,r.intercept_eq,r.rational_value,
    r.denominator_le,r.numerator_abs_le,r.factor_dvd_abscissa,r.structure_bound⟩

end ErdosPrimitiveIntercept



namespace ErdosInverseStructured
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosRichLine

def Structured (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (p q : ℕ) : Prop :=
  ∃ t ∈ sourceRationalList P a S R Z cp, aligns a t p ∧
    ((t.den*badPrimeProduct a t q : ℕ) : ℝ) ≤ R*Z^10

def Nonstructured (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (p q : ℕ) : Prop :=
  ¬Structured P a S R Z cp p q

theorem structured_of_line_alignment {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (p q : ℕ) (b : ℤ)
    (hlist : r.rational ∈ sourceRationalList P a S R Z cp)
    (hden : (l.denominator : ℝ) ≤ R*Z^10) (hline : l.Contains ((q : ℤ),b))
    (hclass : ∀ ell ∈ q.primeFactors,(b : ZMod ell) = (a ell : ZMod ell))
    (halign : aligns a r.rational p) : Structured P a S R Z cp p q := by
  refine ⟨r.rational,hlist,halign,?_⟩
  have hh : ((r.rational.den*badPrimeProduct a r.rational q : ℕ) : ℝ) ≤ l.denominator :=
    Nat.cast_le.mpr (r.structure_bound a q b hline hclass)
  exact hh.trans hden

theorem nonstructured_not_aligned_on_line {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (a : ℕ → ℤ) (S R Z cp : ℝ) (p q : ℕ) (b : ℤ)
    (hlist : r.rational ∈ sourceRationalList P a S R Z cp)
    (hden : (l.denominator : ℝ) ≤ R*Z^10) (hline : l.Contains ((q : ℤ),b))
    (hclass : ∀ ell ∈ q.primeFactors,(b : ZMod ell) = (a ell : ZMod ell))
    (hnon : Nonstructured P a S R Z cp p q) : ¬aligns a r.rational p :=
  fun ha => hnon (structured_of_line_alignment r P a S R Z cp p q b hlist hden hline hclass ha)

end ErdosInverseStructured



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment

noncomputable def slopeClass (l : PrimitiveIntegerLine) (a : ℤ) (p : ℕ) (hp : Nat.Prime p) (s : ℤ) : ZMod p := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ((l.denominator : ZMod p)*(a : ZMod p)-(l.intercept : ZMod p))/
    ((l.slope : ZMod p)+(l.denominator : ZMod p)*(s : ZMod p))

theorem unaligned_numerator_ne_zero {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (a : ℕ → ℤ) (p : ℕ) (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator)
    (hna : ¬aligns a r.rational p) :
    (l.denominator : ZMod p)*(a p : ZMod p)-(l.intercept : ZMod p) ≠ 0 := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hpg : ¬p ∣ r.factor := fun h => hpd (h.trans r.factor_dvd_denominator)
  have hg : (r.factor : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr hpg
  have hdiff : (r.rational.den : ZMod p)*(a p : ZMod p)-(r.rational.num : ZMod p) ≠ 0 :=
    sub_ne_zero.mpr hna
  have he : (l.denominator : ZMod p)*(a p : ZMod p)-(l.intercept : ZMod p) =
      (r.factor : ZMod p)*((r.rational.den : ZMod p)*(a p : ZMod p)-(r.rational.num : ZMod p)) := by
    rw [r.denominator_eq,r.intercept_eq,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
    ring
  rw [he]
  exact mul_ne_zero hg hdiff

theorem point_residue_eq_slopeClass {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (a : ℕ → ℤ) (p : ℕ) (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator)
    (hna : ¬aligns a r.rational p) (v : ℤ × ℤ) (hv : l.Contains v) (s : ℤ)
    (hinc : (v.2 : ZMod p) = (a p : ZMod p)-(s : ZMod p)*(v.1 : ZMod p)) :
    (v.1 : ZMod p) = slopeClass l (a p) p hp s := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hnum := unaligned_numerator_ne_zero r a p hp hpd hna
  have hvZ : (l.denominator : ZMod p)*(v.2 : ZMod p) =
      (l.slope : ZMod p)*(v.1 : ZMod p)+(l.intercept : ZMod p) := by
    have h := congrArg (fun n : ℤ => (n : ZMod p)) hv
    simpa only [PrimitiveIntegerLine.Contains,Int.cast_mul,Int.cast_add,Int.cast_natCast] using h
  have he : ((l.slope : ZMod p)+(l.denominator : ZMod p)*(s : ZMod p))*(v.1 : ZMod p) =
      (l.denominator : ZMod p)*(a p : ZMod p)-(l.intercept : ZMod p) := by
    linear_combination (l.denominator : ZMod p)*hinc-hvZ
  have hcoeff : (l.slope : ZMod p)+(l.denominator : ZMod p)*(s : ZMod p) ≠ 0 := by
    intro hz
    exact hnum (by simpa only [hz,zero_mul] using he.symm)
  unfold slopeClass
  apply (eq_div_iff hcoeff).mpr
  simpa only [mul_comm] using he

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment

noncomputable def incidentPoints (X : Finset (ℤ × ℤ)) (a : ℤ) (p : ℕ) (T : Finset ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact X.filter (fun v => ∃ s ∈ T,
    (v.2 : ZMod p) = (a : ZMod p)-(s : ZMod p)*(v.1 : ZMod p))

noncomputable def occupiedClasses (X : Finset (ℤ × ℤ)) (a : ℤ) (p : ℕ) (T : Finset ℤ) : Finset (ZMod p) := by
  classical
  exact (incidentPoints X a p T).image (fun v => (v.1 : ZMod p))

theorem occupiedClasses_subset_slope_image {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (X : Finset (ℤ × ℤ)) (hline : ∀ v ∈ X, l.Contains v) (a : ℕ → ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator) (hna : ¬aligns a r.rational p) (T : Finset ℤ) :
    occupiedClasses X (a p) p T ⊆ T.image (slopeClass l (a p) p hp) := by
  classical
  intro t ht
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hvX,s,hs,hinc⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_image.mpr ⟨s,hs,(point_residue_eq_slopeClass r a p hp hpd hna v
    (hline v hvX) s hinc).symm⟩

theorem occupiedClasses_card_le {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (X : Finset (ℤ × ℤ)) (hline : ∀ v ∈ X, l.Contains v) (a : ℕ → ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpd : ¬p ∣ l.denominator) (hna : ¬aligns a r.rational p) (T : Finset ℤ) :
    (occupiedClasses X (a p) p T).card ≤ T.card := by
  classical
  exact (Finset.card_le_card (occupiedClasses_subset_slope_image r X hline a p hp hpd hna T)).trans
    (Finset.card_image_le)

end ErdosLineCollision



namespace ErdosLineCollision
attribute [local instance] Classical.propDecidable

noncomputable def occupiedRows (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) : Finset (ℕ × ℕ) := by
  classical
  exact P.biUnion (fun p => (occupiedClasses X (a p) p (T p)).image (fun c => (p,c.val)))

def RowIncidence (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v : ℤ × ℤ) (row : ℕ × ℕ) : Prop :=
  v ∈ incidentPoints X (a row.1) row.1 (T row.1) ∧ (v.1 : ZMod row.1).val = row.2

theorem row_modulus_mem {P : Finset ℕ} {X : Finset (ℤ × ℤ)} {a : ℕ → ℤ} {T : ℕ → Finset ℤ}
    {row : ℕ × ℕ} (hr : row ∈ occupiedRows P X a T) : row.1 ∈ P := by
  classical
  obtain ⟨p,hp,hpRow⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨c,hc,hrow⟩ := Finset.mem_image.mp hpRow
  subst row
  exact hp

theorem point_rows_eq (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v : ℤ × ℤ) :
    (occupiedRows P X a T).filter (RowIncidence X a T v) =
      (P.filter (fun p => v ∈ incidentPoints X (a p) p (T p))).image
        (fun p => (p,(v.1 : ZMod p).val)) := by
  classical
  ext row
  constructor
  · intro hr
    obtain ⟨hrow,hinc,hval⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_image.mpr ⟨row.1,Finset.mem_filter.mpr ⟨row_modulus_mem hrow,hinc⟩,
      Prod.ext rfl hval⟩
  · intro hr
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hpP,hv⟩ := Finset.mem_filter.mp hp
    have hclass : (v.1 : ZMod p) ∈ occupiedClasses X (a p) p (T p) :=
      Finset.mem_image.mpr ⟨v,hv,rfl⟩
    refine Finset.mem_filter.mpr ⟨?_,hv,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨p,hpP,Finset.mem_image.mpr ⟨(v.1 : ZMod p),hclass,rfl⟩⟩

theorem point_rows_card (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v : ℤ × ℤ) :
    ((occupiedRows P X a T).filter (RowIncidence X a T v)).card =
      (P.filter (fun p => v ∈ incidentPoints X (a p) p (T p))).card := by
  classical
  rw [point_rows_eq]
  apply Finset.card_image_of_injective
  intro p q he
  exact congrArg Prod.fst he

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem occupiedRows_card_le {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (hline : ∀ v ∈ X, l.Contains v) (hP : ∀ p ∈ P, Nat.Prime p)
    (hpd : ∀ p ∈ P, ¬p ∣ l.denominator) (hna : ∀ p ∈ P, ¬aligns a r.rational p) :
    (occupiedRows P X a T).card ≤ ∑ p ∈ P,(T p).card := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro p hp
  exact Finset.card_image_le.trans (occupiedClasses_card_le r X hline a p (hP p hp) (hpd p hp) (hna p hp) (T p))

noncomputable def commonRows (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (v w : ℤ × ℤ) : Finset (ℕ × ℕ) :=
  (occupiedRows P X a T).filter (fun row => RowIncidence X a T v row ∧ RowIncidence X a T w row)

theorem commonRows_modulus_injective (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (v w : ℤ × ℤ) :
    Set.InjOn Prod.fst (commonRows P X a T v w : Set (ℕ × ℕ)) := by
  intro row hr row' hr' he
  have hval := ((Finset.mem_filter.mp hr).2).1.2
  have hval' := ((Finset.mem_filter.mp hr').2).1.2
  rw [he] at hval
  exact Prod.ext he (hval.symm.trans hval')

theorem commonRows_modulus_divides (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (hP : ∀ p ∈ P, Nat.Prime p) (v w : ℤ × ℤ)
    (row : ℕ × ℕ) (hr : row ∈ commonRows P X a T v w) : (row.1 : ℤ) ∣ v.1-w.1 := by
  have hp := row_modulus_mem (Finset.mem_filter.mp hr).1
  let : Fact (Nat.Prime row.1) := ⟨hP row.1 hp⟩
  have hval := ((Finset.mem_filter.mp hr).2).1.2
  have hval' := ((Finset.mem_filter.mp hr).2).2.2
  have he : (v.1 : ZMod row.1) = (w.1 : ZMod row.1) :=
    ZMod.val_injective row.1 (hval.trans hval'.symm)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_sub,he,sub_self]

theorem commonRows_card_le (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (hP : ∀ p ∈ P, Nat.Prime p) (v w : ℤ × ℤ) (hx : v.1 ≠ w.1)
    (z alpha C : ℝ) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P,z^alpha ≤ (p : ℝ)) (hheight : |((v.1-w.1 : ℤ) : ℝ)| ≤ z^C) :
    ((commonRows P X a T v w).card : ℝ) ≤ C/alpha := by
  classical
  have hsub : (commonRows P X a T v w).image Prod.fst ⊆ dividingPrimes P (v.1-w.1) := by
    intro p hp
    obtain ⟨row,hrow,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨row_modulus_mem (Finset.mem_filter.mp hrow).1,
      commonRows_modulus_divides P X a T hP v w row hrow⟩
  have hc : (commonRows P X a T v w).card ≤ (dividingPrimes P (v.1-w.1)).card := by
    rw [← Finset.card_image_of_injOn (commonRows_modulus_injective P X a T v w)]
    exact Finset.card_le_card hsub
  apply (show ((commonRows P X a T v w).card : ℝ) ≤ (dividingPrimes P (v.1-w.1)).card by exact_mod_cast hc).trans
  exact dividingPrimes_card_bound P (v.1-w.1) (sub_ne_zero.mpr hx) hP z alpha C hz ha hlarge hheight

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosInverseIncidence
attribute [local instance] Classical.propDecidable

theorem row_multiplicity_sum (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) :
    (∑ row ∈ occupiedRows P X a T,multiplicity X (RowIncidence X a T) row) =
      ∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ) := by
  classical
  let R : (ℤ × ℤ) → ℕ → Prop := fun v p => v ∈ incidentPoints X (a p) p (T p)
  have hdegree (v : ℤ × ℤ) : degree (occupiedRows P X a T) (RowIncidence X a T) v = degree P R v :=
    by simpa only [ErdosInverseIncidence.degree,R] using point_rows_card P X a T v
  have hcount (p : ℕ) : multiplicity X R p = ((incidentPoints X (a p) p (T p)).card : ℝ) := by
    have he : X.filter (fun v => v ∈ incidentPoints X (a p) p (T p)) = incidentPoints X (a p) p (T p) := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
    have hh : (∑ v ∈ X,if v ∈ incidentPoints X (a p) p (T p) then (1 : ℝ) else 0) =
        ((X.filter (fun v => v ∈ incidentPoints X (a p) p (T p))).card : ℝ) :=
      Finset.sum_boole (fun v => v ∈ incidentPoints X (a p) p (T p)) X
    rw [he] at hh
    have hsum : multiplicity X R p =
        ∑ v ∈ X,if v ∈ incidentPoints X (a p) p (T p) then (1 : ℝ) else 0 := by
      unfold ErdosInverseIncidence.multiplicity
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hmem : v ∈ incidentPoints X (a p) p (T p) <;>
        simp [ErdosInverseIncidence.bit,R,hmem]
    exact hsum.trans hh
  calc
    _ = ∑ v ∈ X,(degree (occupiedRows P X a T) (RowIncidence X a T) v : ℝ) := multiplicity_sum _ _ _
    _ = ∑ v ∈ X,(degree P R v : ℝ) := by simp_rw [hdegree]
    _ = ∑ p ∈ P,multiplicity X R p := (multiplicity_sum X P R).symm
    _ = _ := Finset.sum_congr rfl (fun p _ => hcount p)

theorem total_incidence_le_product (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) :
    (∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤ (P.card : ℝ)*(X.card : ℝ) := by
  calc
    _ ≤ ∑ _p ∈ P,(X.card : ℝ) := Finset.sum_le_sum (fun p _ => by
      have hc : (incidentPoints X (a p) p (T p)).card ≤ X.card := Finset.card_filter_le X _
      exact Nat.cast_le.mpr hc)
    _ = _ := by simp

end ErdosLineCollision



namespace ErdosLineCollision
open ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosInverseIncidence ErdosConvexGraph

theorem actual_collision_bound {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (hline : ∀ v ∈ X,l.Contains v) (hP : ∀ p ∈ P,Nat.Prime p)
    (hpd : ∀ p ∈ P,¬p ∣ l.denominator) (hna : ∀ p ∈ P,¬aligns a r.rational p)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (S z alpha : ℝ)
    (hbox : ∀ v ∈ X,InSquare S v) (hz : 1 < z) (ha : 0 < alpha)
    (hlarge : ∀ p ∈ P,z^alpha ≤ (p : ℝ)) (hS : S ≤ z^3) :
    (∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ))^2 ≤
      (∑ p ∈ P,((T p).card : ℝ))*
        ((3/alpha)*(X.card : ℝ)^2+∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ)) := by
  classical
  have hK : (0 : ℝ) ≤ 3/alpha := by positivity
  have hB : 0 ≤ ∑ p ∈ P,((T p).card : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hQ : ((occupiedRows P X a T).card : ℝ) ≤ ∑ p ∈ P,((T p).card : ℝ) := by
    exact_mod_cast occupiedRows_card_le r P X a T hline hP hpd hna
  have hpair : ∀ v ∈ X,∀ w ∈ X,v ≠ w →
      (((occupiedRows P X a T).filter
        (fun row => RowIncidence X a T v row ∧ RowIncidence X a T w row)).card : ℝ) ≤ 3/alpha := by
    intro v hv w hw hne
    have hx : v.1 ≠ w.1 := fun he => hne (hinj hv hw he)
    have hh : |((v.1-w.1 : ℤ) : ℝ)| ≤ z^(3 : ℝ) := by
      have he : z^(3 : ℝ) = z^3 := Real.rpow_natCast z 3
      rw [he]
      exact (integer_difference_abs_le (hbox v hv).1 (hbox w hw).1).trans hS
    exact commonRows_card_le P X a T hP v w hx z alpha 3 hz ha hlarge hh
  have hh := precise_incidence_cauchy X (occupiedRows P X a T) (RowIncidence X a T)
    (3/alpha) (∑ p ∈ P,((T p).card : ℝ)) hK hB hQ hpair
  rwa [row_multiplicity_sum] at hh

end ErdosLineCollision


end Erdos970

end OAI
