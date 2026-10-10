import OAI.NumberTheory.Jacobsthal.Harmonic.OriginalSourcePolynomial
import OAI.NumberTheory.Jacobsthal.Primes.IgnoredDenominatorPrimes
import OAI.NumberTheory.Jacobsthal.Sieve.IntegerRichLine

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceLineBudget
open ErdosInverseBoxHeight ErdosSourcePolynomial ErdosAuxiliaryPolynomial ErdosInversePrimeBin
open ErdosRichLine ErdosConvexGraph

def RichPoint (R xi c : ℝ) (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ)
    (v : ℤ × ℤ) : Prop :=
  ∃ (I : Finset ℕ) (hIP : I ⊆ primeBin R xi), c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ) ∧
    ∀ r : I, IntegerLineIncidence (primeBin R xi) T a v.1 v.2 ⟨r.val,hIP r.property⟩

theorem uniform_original_rich_line (C Cparent eta alpha c : ℝ)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cparent) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → p ≤ 2*R →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ Cparent →
      ∀ (T : primeBin R xi → Finset ℤ) (a : primeBin R xi → ℤ),
        (∑ r : primeBin R xi, ((T r).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        ∀ X : Finset (ℤ × ℤ), (∀ v ∈ X, InSquare S v) →
          Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) →
          S/(sourceZ z)^4 ≤ (X.card : ℝ) → (∀ v ∈ X, RichPoint R xi c T a v) →
          ∃ (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)), Y ⊆ X ∧
            S/(R*(sourceZ z)^6) < (Y.card : ℝ) ∧ (∀ v ∈ Y, l.Contains v) ∧
            (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
            |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
            |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ) := by
  filter_upwards [uniform_original_source_polynomial C eta alpha c hC heta halpha hc,
    uniform_extraction_budget Cparent hCp] with z hz hb
  refine ⟨hz.1,?_⟩
  intro S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 hpR hlen T a hthin
    X hbox hinj hcard hrich
  obtain ⟨w⟩ := hz.2 S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 T a hthin
  have hp0 : 0 < p := by linarith
  have hqS : q ≤ S := (one_le_div hq).mp hratio
  have hS : 0 ≤ S := hq.le.trans hqS
  have hbudget := hb.2 p q R S hp0 hq hpR hRhi hqS hlen
  have hzero : ∀ v ∈ X, MvPolynomial.eval ![v.1,v.2] w.polynomial = 0 := by
    intro v hv
    obtain ⟨I,hIP,hI,hinc⟩ := hrich v hv
    exact w.rich_vanishing v.1 v.2 (hbox v hv).1 (hbox v hv).2 I hIP hI hinc
  exact integer_polynomial_rich_line w.polynomial w.nonzero (sourceDegree z R) w.degree_le
    S hS X hbox hzero hinj (S/(R*(sourceZ z)^6)) hbudget.2.1 (hbudget.2.2.trans_le hcard)

end ErdosSourceLineBudget

end

section

namespace ErdosSourceLineBudget
open ErdosRichLine

theorem source_line_heights (l : PrimitiveIntegerLine) (S R Z N : ℝ)
    (hS : 0 ≤ S) (hR : 0 < R) (hZ : 0 < Z) (hN : 0 < N)
    (hrich : S/(R*Z^6) < N) (hd : (l.denominator : ℝ) ≤ 2*S/N)
    (ha : |(l.slope : ℝ)| ≤ 2*S/N) (hb : |(l.intercept : ℝ)| ≤ 4*S^2/N) :
    (l.denominator : ℝ) ≤ 2*R*Z^6 ∧ |(l.slope : ℝ)| ≤ 2*R*Z^6 ∧
      |(l.intercept : ℝ)| ≤ 4*S*R*Z^6 := by
  have hmul : S < N*(R*Z^6) := (div_lt_iff₀ (by positivity : 0 < R*Z^6)).mp hrich
  have hratio : S/N ≤ R*Z^6 := (div_le_iff₀ hN).mpr (by nlinarith)
  have htwo : 2*S/N ≤ 2*R*Z^6 := by
    calc
      _ = 2*(S/N) := by ring
      _ ≤ 2*(R*Z^6) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = _ := by ring
  have hfour : 4*S^2/N ≤ 4*S*R*Z^6 := by
    calc
      _ = (4*S)*(S/N) := by ring
      _ ≤ (4*S)*(R*Z^6) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  exact ⟨hd.trans htwo,ha.trans htwo,hb.trans hfour⟩

theorem source_line_height_slack (l : PrimitiveIntegerLine) (S R Z : ℝ)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hZ : 2 ≤ Z)
    (hd : (l.denominator : ℝ) ≤ 2*R*Z^6) (ha : |(l.slope : ℝ)| ≤ 2*R*Z^6)
    (hb : |(l.intercept : ℝ)| ≤ 4*S*R*Z^6) :
    (l.denominator : ℝ) ≤ R*Z^10 ∧ |(l.slope : ℝ)| ≤ R*Z^10 ∧
      |(l.intercept : ℝ)| ≤ S*R*Z^10 := by
  have hZ0 : 0 ≤ Z := by linarith
  have hfour : 4 ≤ Z^4 := by nlinarith [sq_nonneg (Z^2-2)]
  have htwo : 2*R*Z^6 ≤ R*Z^10 := by
    nlinarith [mul_nonneg (mul_nonneg hR (pow_nonneg hZ0 6)) (show 0 ≤ Z^4-2 by linarith)]
  have hfour' : 4*S*R*Z^6 ≤ S*R*Z^10 := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hS hR) (pow_nonneg hZ0 6)) (sub_nonneg.mpr hfour)]
  exact ⟨hd.trans htwo,ha.trans htwo,hb.trans hfour'⟩

end ErdosSourceLineBudget

end

section

namespace ErdosInverseStructured
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosRichLine ErdosInversePrimeBin ErdosConvexGraph
attribute [local instance] Classical.propDecidable

def SlopeIncidence (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (v : ℤ × ℤ) (p : ℕ) : Prop :=
  ∃ s ∈ T p, (v.2 : ZMod p) = (a p : ZMod p)-(s : ZMod p)*(v.1 : ZMod p)

def NonstructuredIncidence (P : Finset ℕ) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (S R Z cp : ℝ) (v : ℤ × ℤ) (p : ℕ) : Prop :=
  SlopeIncidence a T v p ∧ Nonstructured P a S R Z cp p v.1.toNat

noncomputable def nonstructuredPrimes (P : Finset ℕ) (a : ℕ → ℤ) (T : ℕ → Finset ℤ)
    (S R Z cp : ℝ) (v : ℤ × ℤ) : Finset ℕ :=
  P.filter (NonstructuredIncidence P a T S R Z cp v)

noncomputable def nonstructuredPoints (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp : ℝ) (p : ℕ) : Finset (ℤ × ℤ) :=
  X.filter (fun v => NonstructuredIncidence P a T S R Z cp v p)

theorem nonstructured_richness_implies_polynomial_richness (R xi c S Z cp : ℝ)
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (v : ℤ × ℤ)
    (h : c*((primeBin R xi).card : ℝ) ≤
      ((nonstructuredPrimes (primeBin R xi) a T S R Z cp v).card : ℝ)) :
    ErdosSourceLineBudget.RichPoint R xi c (fun p => T p.val) (fun p => a p.val) v := by
  let I := nonstructuredPrimes (primeBin R xi) a T S R Z cp v
  have hIP : I ⊆ primeBin R xi := Finset.filter_subset _ _
  refine ⟨I,hIP,h,?_⟩
  intro p
  exact (Finset.mem_filter.mp p.property).2.1

theorem contains_nat_abscissa (l : PrimitiveIntegerLine) (v : ℤ × ℤ)
    (h0 : 0 ≤ (v.1 : ℝ)) (hv : l.Contains v) : l.Contains ((v.1.toNat : ℤ),v.2) := by
  have hv0 : 0 ≤ v.1 := by exact_mod_cast h0
  have he := Int.toNat_of_nonneg hv0
  simpa only [he] using hv

end ErdosInverseStructured

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosInverseBoxHeight

theorem uniform_actual_ignored_incidence (eta alpha eps : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ R xi : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ R*(sourceZ z)^10 →
        ∀ (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ),
          (∑ p ∈ ignoredPrimes (primeBin R xi) d,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
            eps*((primeBin R xi).card : ℝ)*(X.card : ℝ) := by
  let M : ℕ := ⌈(1/alpha)/eps⌉₊
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_many heta M)
  filter_upwards [sourceZ_le_small_power,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0] with z hz hzR
  refine ⟨hz.1,?_⟩
  intro R xi hRlo hRhi hxi hxi1 d hd hdheight X a T
  have hb := hR0 R (hzR.trans hRlo)
  have hRpos : 0 < R := by linarith [hb.1]
  have hxipos : 0 ≤ xi := heta.le.trans hxi
  have hheight := source_denominator_le_z hz.1 hRpos.le hz.2.1.le hRhi hz.2.2 hdheight
  have hprime (p : ℕ) (hp : p ∈ primeBin R xi) : Nat.Prime p :=
    ((mem_primeBin hRpos.le hxipos p).mp hp).1
  have hlarge (p : ℕ) (hp : p ∈ primeBin R xi) : z^alpha ≤ (p : ℝ) :=
    hRlo.trans (((mem_primeBin hRpos.le hxipos p).mp hp).2.1.le)
  have hcard := ignoredPrimes_card_le (primeBin R xi) d hd hprime z alpha hz.1 halpha hlarge hheight
  have hM : (M : ℝ) ≤ ((primeBin R xi).card : ℝ) := by exact_mod_cast hb.2 xi hxi hxi1
  have hceil : (1/alpha)/eps ≤ (M : ℝ) := Nat.le_ceil _
  have hsmall : 1/alpha ≤ eps*((primeBin R xi).card : ℝ) := by
    have hh := (div_le_iff₀ heps).mp (hceil.trans hM)
    nlinarith
  calc
    _ ≤ ((ignoredPrimes (primeBin R xi) d).card : ℝ)*(X.card : ℝ) :=
      total_incidence_le_product _ _ _ _
    _ ≤ (1/alpha)*(X.card : ℝ) := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)

end ErdosSourceCollision

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosInversePrimeBin ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseBoxHeight ErdosConvexGraph

theorem uniform_actual_bad_incidence (eta alpha eps : ℝ)
    (heta : 0 < eta) (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ R xi S : ℝ,
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      ∀ (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (l : PrimitiveIntegerLine) (r : InterceptReduction l)
        (X : Finset (ℤ × ℤ)), (∀ v ∈ X,l.Contains v) → (∀ v ∈ X,InSquare S v) →
        Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) → S ≤ z^3 → z^((93 : ℝ)/100) ≤ (X.card : ℝ) →
        (∑ p ∈ primeBin R xi,((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        (l.denominator : ℝ) ≤ R*(sourceZ z)^10 →
        (∑ p ∈ unalignedPrimes (primeBin R xi) a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
          (∑ p ∈ ignoredPrimes (primeBin R xi) l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
            eps*((primeBin R xi).card : ℝ)*(X.card : ℝ) := by
  filter_upwards [uniform_actual_unaligned_incidence eta alpha (eps/2) heta halpha (by positivity),
    uniform_actual_ignored_incidence eta alpha (eps/2) heta halpha (by positivity)] with z hu hi
  refine ⟨hu.1,?_⟩
  intro R xi S hRlo hRhi hxi hxi1 a T l r X hline hbox hinj hS hN hthin hden
  have hU := hu.2 R xi S hRlo hRhi hxi hxi1 a T l r X hline hbox hinj hS hN hthin
  have hI := hi.2 R xi hRlo hRhi hxi hxi1 l.denominator l.denominator_pos hden X a T
  linarith

end ErdosSourceCollision

end

section

namespace ErdosInverseStructured
open ErdosLineCollision
attribute [local instance] Classical.propDecidable

theorem nonstructured_double_count (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (S R Z cp : ℝ) :
    (∑ v ∈ X,((nonstructuredPrimes P a T S R Z cp v).card : ℝ)) =
      ∑ p ∈ P,((nonstructuredPoints P X a T S R Z cp p).card : ℝ) := by
  classical
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (NonstructuredIncidence P a T S R Z cp) (s := X) (t := P)
  change (∑ v ∈ X,((P.filter (NonstructuredIncidence P a T S R Z cp v)).card : ℝ)) =
    ∑ p ∈ P,((X.filter (fun v => NonstructuredIncidence P a T S R Z cp v p)).card : ℝ)
  exact_mod_cast hh

theorem nonstructuredPoints_subset_incident (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (S R Z cp : ℝ) (p : ℕ) :
    nonstructuredPoints P X a T S R Z cp p ⊆ incidentPoints X (a p) p (T p) := by
  intro v hv
  obtain ⟨hvX,hinc,_hnon⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvX,hinc⟩

theorem nonstructured_total_lower (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ)
    (T : ℕ → Finset ℤ) (S R Z cp c : ℝ)
    (hrich : ∀ v ∈ X,c*(P.card : ℝ) ≤ ((nonstructuredPrimes P a T S R Z cp v).card : ℝ)) :
    c*(P.card : ℝ)*(X.card : ℝ) ≤ ∑ p ∈ P,((nonstructuredPoints P X a T S R Z cp p).card : ℝ) := by
  rw [← nonstructured_double_count]
  calc
    _ = ∑ _v ∈ X,c*(P.card : ℝ) := by simp;ring
    _ ≤ _ := Finset.sum_le_sum hrich

theorem all_incidence_lower_of_nonstructured_richness (P : Finset ℕ) (X : Finset (ℤ × ℤ))
    (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp c : ℝ)
    (hrich : ∀ v ∈ X,c*(P.card : ℝ) ≤ ((nonstructuredPrimes P a T S R Z cp v).card : ℝ)) :
    c*(P.card : ℝ)*(X.card : ℝ) ≤ ∑ p ∈ P,((incidentPoints X (a p) p (T p)).card : ℝ) := by
  apply (nonstructured_total_lower P X a T S R Z cp c hrich).trans
  apply Finset.sum_le_sum
  intro p hp
  exact Nat.cast_le.mpr (Finset.card_le_card (nonstructuredPoints_subset_incident P X a T S R Z cp p))

end ErdosInverseStructured

end

end Erdos970

end OAI
