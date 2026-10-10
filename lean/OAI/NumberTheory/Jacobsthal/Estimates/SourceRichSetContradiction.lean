import OAI.NumberTheory.Jacobsthal.Primes.PrimePartitionCounts

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosConvexGraph
attribute [local instance] Classical.propDecidable

theorem nonstructuredPoints_eq_empty_of_aligned {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp : ℝ)
    (hlist : r.rational ∈ sourceRationalList P a S R Z cp) (hden : (l.denominator : ℝ) ≤ R*Z^10)
    (hline : ∀ v ∈ X,l.Contains v) (hbox : ∀ v ∈ X,InSquare S v)
    (hclass : ∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell))
    (p : ℕ) (halign : aligns a r.rational p) : nonstructuredPoints P X a T S R Z cp p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvX,_hslope,hnon⟩ := Finset.mem_filter.mp hv
  exact hnon (structured_of_line_alignment r P a S R Z cp p v.1.toNat v.2 hlist hden
    (contains_nat_abscissa l v (hbox v hvX).1.1 (hline v hvX)) (hclass v hvX) halign)

theorem nonstructured_total_le_bad {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z cp : ℝ)
    (hlist : r.rational ∈ sourceRationalList P a S R Z cp) (hden : (l.denominator : ℝ) ≤ R*Z^10)
    (hline : ∀ v ∈ X,l.Contains v) (hbox : ∀ v ∈ X,InSquare S v)
    (hclass : ∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell)) :
    (∑ p ∈ P,((nonstructuredPoints P X a T S R Z cp p).card : ℝ)) ≤
      (∑ p ∈ unalignedPrimes P a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
      (∑ p ∈ ignoredPrimes P l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) := by
  have hpart := prime_sum_partition_le r P a
    (fun p => ((nonstructuredPoints P X a T S R Z cp p).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
  have hzero : (∑ p ∈ P.filter (aligns a r.rational),
      ((nonstructuredPoints P X a T S R Z cp p).card : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [nonstructuredPoints_eq_empty_of_aligned r P X a T S R Z cp hlist hden hline hbox hclass p
      (Finset.mem_filter.mp hp).2,Finset.card_empty,Nat.cast_zero]
  rw [hzero,add_zero] at hpart
  apply hpart.trans
  apply add_le_add <;> apply Finset.sum_le_sum
  all_goals
    intro p hp
    exact Nat.cast_le.mpr (Finset.card_le_card (nonstructuredPoints_subset_incident P X a T S R Z cp p))

end ErdosInverseStructured

end

section

namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment ErdosConvexGraph

theorem no_rich_nonstructured_line {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (P : Finset ℕ) (X : Finset (ℤ × ℤ)) (a : ℕ → ℤ) (T : ℕ → Finset ℤ) (S R Z c : ℝ)
    (hc : 0 < c) (hP : 0 < P.card) (hX : 0 < X.card) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hline : ∀ v ∈ X,l.Contains v) (hbox : ∀ v ∈ X,InSquare S v)
    (hclass : ∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell))
    (hden : (l.denominator : ℝ) ≤ R*Z^10) (hnum : |(l.intercept : ℝ)| ≤ S*R*Z^10)
    (hrich : ∀ v ∈ X,c*(P.card : ℝ) ≤ ((nonstructuredPrimes P a T S R Z (c/4) v).card : ℝ))
    (hbad : (∑ p ∈ unalignedPrimes P a r,((incidentPoints X (a p) p (T p)).card : ℝ))+
      (∑ p ∈ ignoredPrimes P l.denominator,((incidentPoints X (a p) p (T p)).card : ℝ)) ≤
      (c/2)*(P.card : ℝ)*(X.card : ℝ)) : False := by
  classical
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX
  have htotal := all_incidence_lower_of_nonstructured_richness P X a T S R Z (c/4) c hrich
  have halign := many_aligners_of_richness r P X a T c (c/2) hX htotal hbad
  have hcp : (c/4)*(P.card : ℝ) ≤ ((P.filter (aligns a r.rational)).card : ℝ) := by
    have hfrac : c/4 ≤ c-c/2 := by linarith
    exact (mul_le_mul_of_nonneg_right hfrac hPpos.le).trans halign
  have hlist := intercept_mem_fixed_list r P a S R Z (c/4) hS hR hden hnum hcp
  have hlow := nonstructured_total_lower P X a T S R Z (c/4) c hrich
  have hup := (nonstructured_total_le_bad r P X a T S R Z (c/4) hlist hden hline hbox hclass).trans hbad
  have hpos : 0 < c*(P.card : ℝ)*(X.card : ℝ) := mul_pos (mul_pos hc hPpos) hXpos
  linarith

end ErdosInverseStructured

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseStructured
open ErdosSourceCollision ErdosLineCollision ErdosRichLine ErdosPrimitiveIntercept ErdosInverseAlignment
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosSourcePolynomial ErdosSourceLineBudget ErdosConvexGraph

theorem uniform_no_rich_nonstructured_set (C Cparent eta alpha c : ℝ)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cparent) (heta : 0 < eta) (halpha : 0 < alpha) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ ∀ S R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ S/q → S/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → eta ≤ xi → xi ≤ 1 → p ≤ 2*R →
      Real.logb (sourceW z) ((sourceY z : ℝ)/(p*q)) ≤ Cparent →
      ∀ (a : ℕ → ℤ) (T : ℕ → Finset ℤ),
        (∑ p ∈ primeBin R xi,((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 →
        ∀ X : Finset (ℤ × ℤ), (∀ v ∈ X,InSquare S v) →
          Set.InjOn Prod.fst (X : Set (ℤ × ℤ)) → S/(sourceZ z)^4 ≤ (X.card : ℝ) →
          (∀ v ∈ X,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell)) →
          (∀ v ∈ X,c*((primeBin R xi).card : ℝ) ≤
            ((nonstructuredPrimes (primeBin R xi) a T S R (sourceZ z) (c/4) v).card : ℝ)) → False := by
  classical
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_many heta 1)
  filter_upwards [uniform_original_rich_line C Cparent eta alpha c hC hCp heta halpha hc,
    uniform_actual_bad_incidence eta alpha (c/2) heta halpha (by positivity),
    uniform_extraction_budget Cparent hCp,uniform_source_square_scale C hC,source_Z_ge_two,
    (tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z hRich hBad hBudget hScale hZ2 hzR
  refine ⟨hRich.1,?_⟩
  intro S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 hpR hlen a T hthin
    X hbox hinj hsize hclass hrich
  have hcounts := hR0 R (hzR.trans hRlo)
  have hR1 : 1 ≤ R := by linarith [hcounts.1]
  have hRpos : 0 < R := by linarith
  have hPpos : 0 < (primeBin R xi).card := by
    have hh := hcounts.2 xi hxi hxi1
    omega
  have hqS : q ≤ S := (one_le_div hq).mp hratio
  have hS0 : 0 ≤ S := hq.le.trans hqS
  have hZpos : 0 < sourceZ z := by linarith
  have hbudget := hBudget.2 p q R S (by linarith) hq hpR hRhi hqS hlen
  have hthin' : (∑ r : primeBin R xi,((T r.val).card : ℝ)) ≤
      ((primeBin R xi).card : ℝ)*R/(Real.log z)^6 := by
    calc
      _ = ∑ p ∈ primeBin R xi,((T p).card : ℝ) :=
        Finset.sum_coe_sort (primeBin R xi) (fun p : ℕ => ((T p).card : ℝ))
      _ ≤ _ := hthin
  have hpolyRich : ∀ v ∈ X,RichPoint R xi c (fun r => T r.val) (fun r => a r.val) v :=
    fun v hv => nonstructured_richness_implies_polynomial_richness R xi c S (sourceZ z) (c/4) a T v (hrich v hv)
  obtain ⟨l,Y,hsub,hlarge,hline,hdN,haN,hbN⟩ := hRich.2 S R p q xi hp hq hpq hratio hinfl hRlo hRhi hxi hxi1 hpR hlen
    (fun r => T r.val) (fun r => a r.val) hthin' X hbox hinj hsize hpolyRich
  have hYposR : (0 : ℝ) < Y.card := by linarith [hbudget.2.1]
  have hYpos : 0 < Y.card := by exact_mod_cast hYposR
  have hYbox : ∀ v ∈ Y,InSquare S v := fun v hv => hbox v (hsub hv)
  have hYinj : Set.InjOn Prod.fst (Y : Set (ℤ × ℤ)) := fun _ hv _ hw he => hinj (hsub hv) (hsub hw) he
  have hYclass : ∀ v ∈ Y,∀ ell ∈ v.1.toNat.primeFactors,(v.2 : ZMod ell) = (a ell : ZMod ell) :=
    fun v hv => hclass v (hsub hv)
  have hYrich : ∀ v ∈ Y,c*((primeBin R xi).card : ℝ) ≤
      ((nonstructuredPrimes (primeBin R xi) a T S R (sourceZ z) (c/4) v).card : ℝ) :=
    fun v hv => hrich v (hsub hv)
  have hYsize : z^((93 : ℝ)/100) ≤ (Y.card : ℝ) := hbudget.1.trans hlarge.le
  have hSupper := hScale.2.2 S R p q xi hp hq hpq hratio hinfl hR1 hRhi (heta.le.trans hxi) hxi1
  obtain ⟨hd6,ha6,hb6⟩ := source_line_heights l S R (sourceZ z) (Y.card : ℝ) hS0 hRpos hZpos hYposR hlarge hdN haN hbN
  obtain ⟨hd10,_ha10,hb10⟩ := source_line_height_slack l S R (sourceZ z) hS0 hRpos.le hZ2 hd6 ha6 hb6
  obtain ⟨r⟩ := exists_intercept_reduction l
  have hbad := hBad.2 R xi S hRlo hRhi hxi hxi1 a T l r Y hline hYbox hYinj hSupper hYsize hthin hd10
  exact no_rich_nonstructured_line r (primeBin R xi) Y a T S R (sourceZ z) c hc hPpos hYpos hS0 hRpos.le
    hline hYbox hYclass hd10 hb10 hYrich hbad

end ErdosInverseStructured

end

end Erdos970

end OAI
