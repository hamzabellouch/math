import OAI.NumberTheory.Jacobsthal.Partitions.OmissionPartition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def signedWeight (ps : List ℕ) : ℝ := (-1 : ℝ)^ps.length*prefixWeight ps
noncomputable def survivorProduct (P : Finset ℕ) : ℝ := ∏ p ∈ P,(1-(p : ℝ)⁻¹)

theorem signedWeight_append (pre suf : List ℕ) : signedWeight (pre++suf) = signedWeight pre*signedWeight suf := by
  unfold signedWeight prefixWeight
  rw [List.length_append,pow_add,List.map_append,List.prod_append]
  ring

theorem sum_signedWeight (P : Finset ℕ) :
    (∑ ps ∈ decreasingPrefixes P,signedWeight ps) = survivorProduct P := by
  have h := sum_sorted_products P (fun p : ℕ => (-1 : ℝ)*(p : ℝ)⁻¹)
  simp_rw [VariablePrimeTilt.variable_tilt_weight] at h
  simpa only [signedWeight,survivorProduct,neg_one_mul,sub_eq_add_neg] using h

theorem sum_completion_signedWeight (P : Finset ℕ) (pre : List ℕ) :
    (∑ ps ∈ completions P pre,signedWeight ps) = signedWeight pre*survivorProduct (suffixPrimes P pre) := by
  unfold completions
  rw [Finset.sum_image]
  · simp_rw [signedWeight_append]
    rw [← Finset.mul_sum,sum_signedWeight]
  · intro a _ b _ h
    exact List.append_cancel_left h

end NumberTheoryLean.ReferencePruning

end

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open FinitePathGeometry ReferenceAdmission ErdosPrimeInputs.PrimePrefixMass

theorem product_minus_reference (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    survivorProduct P-referencePolynomial w P i r =
      ∑ ps ∈ rejectedPrefixes w P i r,signedWeight ps := by
  have h := Finset.sum_filter_add_sum_filter_not (decreasingPrefixes P) (admitted w i r) signedWeight
  rw [sum_signedWeight] at h
  have he : referencePolynomial w P i r + (∑ ps ∈ rejectedPrefixes w P i r,signedWeight ps) =
      survivorProduct P := by
    simpa only [referencePolynomial,referencePrefixes,rejectedPrefixes,signedWeight] using h
  linarith only [he]

theorem pruning_identity (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    survivorProduct P-referencePolynomial w P i r =
      ∑ pre ∈ firstOmissions w P i r,signedWeight pre*survivorProduct (suffixPrimes P pre) := by
  rw [product_minus_reference,rejected_eq_omission_completions,
    Finset.sum_biUnion (omission_completions_disjoint w P i r)]
  exact Finset.sum_congr rfl (fun pre _ => sum_completion_signedWeight P pre)

noncomputable def belowLast (P : Finset ℕ) (pre : List ℕ) : Finset ℕ :=
  P.filter (fun q => q < pre.getLastD 0)

theorem suffixPrimes_eq_belowLast {w r : ℝ} {P : Finset ℕ} {i : Side} {ps : List ℕ}
    (hp : ps ∈ firstOmissions w P i r) : suffixPrimes P ps = belowLast P ps := by
  obtain ⟨hD,hfirst⟩ := Finset.mem_filter.mp hp
  obtain ⟨pre,p,he,_,_⟩ := hfirst
  rw [he] at hD ⊢
  simpa only [belowLast,List.getLastD_concat] using suffixPrimes_append_singleton hD

theorem pruning_identity_last (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    (∏ p ∈ P,(1-(p : ℝ)⁻¹))-referencePolynomial w P i r =
      ∑ ps ∈ firstOmissions w P i r,((-1 : ℝ)^ps.length*prefixWeight ps)*
        ∏ q ∈ P.filter (fun q => q < ps.getLastD 0),(1-(q : ℝ)⁻¹) := by
  rw [show (∏ p ∈ P,(1-(p : ℝ)⁻¹)) = survivorProduct P from rfl,pruning_identity]
  apply Finset.sum_congr rfl
  intro ps hp
  rw [suffixPrimes_eq_belowLast hp]
  rfl

end NumberTheoryLean.ReferencePruning

end

section

open scoped BigOperators
namespace NumberTheoryLean.ReferencePruning
open FinitePathGeometry ReferenceAdmission VariablePrimeTilt
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem reciprocal_le_one {p : ℕ} (hp : 1 ≤ p) : (p : ℝ)⁻¹ ≤ 1 := by
  have h : (1 : ℝ) ≤ p := by exact_mod_cast hp
  simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h

theorem survivorProduct_bounds (P : Finset ℕ) (hP : ∀ p ∈ P,1 ≤ p) :
    0 ≤ survivorProduct P ∧ survivorProduct P ≤ 1 := by
  have h0 : ∀ p ∈ P,0 ≤ 1-(p : ℝ)⁻¹ := fun p hp => sub_nonneg.mpr (reciprocal_le_one (hP p hp))
  have h1 : ∀ p ∈ P,1-(p : ℝ)⁻¹ ≤ 1 := fun p _ =>
    sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))
  exact ⟨Finset.prod_nonneg h0,Finset.prod_le_one₀ h0 h1⟩

theorem abs_signedWeight (ps : List ℕ) : |signedWeight ps| = prefixWeight ps := by
  simp only [signedWeight,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (prefixWeight_nonneg ps)]

theorem pruning_discrepancy_bound (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ)
    (hP : ∀ p ∈ P,1 ≤ p) :
    |referencePolynomial w P i r-survivorProduct P| ≤
      ∑ ps ∈ firstOmissions w P i r,prefixWeight ps := by
  rw [abs_sub_comm,pruning_identity]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro pre _hpre
  have hprod := survivorProduct_bounds (suffixPrimes P pre)
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)
  rw [abs_mul,abs_signedWeight,abs_of_nonneg hprod.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod.2 (prefixWeight_nonneg pre)

theorem boundary_reference_discrepancy (w r : ℝ) (i : Side) :
    |referencePolynomial w (boundaryPrimes w) i r-
      (∏ p ∈ boundaryPrimes w,(1-(p : ℝ)⁻¹))| ≤ omissionMass w r i := by
  apply pruning_discrepancy_bound w (boundaryPrimes w) i r
  intro p hp
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  exact le_trans (by norm_num : 1 ≤ 2) (Nat.mem_primesLE.mp hpp).2.two_le

end NumberTheoryLean.ReferencePruning

end

section

namespace NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable
open _root_.Finset
open ReferencePruning ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.MertensStrong

noncomputable def availablePrimes (a x : ℝ) (closed : Bool) : Finset ℕ :=
  (primesBetween a x).filter (fun p => closed=true ∨ (p:ℝ)<x)

noncomputable def availableProduct (a x : ℝ) (closed : Bool) : ℝ :=
  survivorProduct (availablePrimes a x closed)

@[simp] theorem availablePrimes_closed (a x : ℝ) : availablePrimes a x true=primesBetween a x := by
  simp [availablePrimes]

theorem primeProduct_eq_survivor (x : ℝ) : primeProduct x=survivorProduct (Nat.primesLE ⌊x⌋₊) := by
  have he : (Ioc 0 ⌊x⌋₊).filter Nat.Prime=Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [mem_filter,mem_Ioc,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_,hpx⟩,hp⟩
      exact ⟨hpx,hp⟩
    · rintro ⟨hpx,hp⟩
      exact ⟨⟨hp.pos,hpx⟩,hp⟩
  unfold primeProduct survivorProduct
  rw [he]
  simp only [one_div]

theorem prime_factor_pos {p : ℕ} (hp : p.Prime) : 0 < 1-(p:ℝ)⁻¹ := by
  apply sub_pos.mpr
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem actual_primeProduct_pos (x : ℝ) : 0 < primeProduct x := by
  rw [primeProduct_eq_survivor]
  exact Finset.prod_pos (fun p hp => prime_factor_pos (Nat.mem_primesLE.mp hp).2)

theorem availableProduct_pos (a x : ℝ) (closed : Bool) : 0 < availableProduct a x closed := by
  unfold availableProduct survivorProduct
  apply Finset.prod_pos
  intro p hp
  exact prime_factor_pos (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2

theorem primesBetween_eq_sdiff {a x : ℝ} (ha : 0 ≤ a) :
    primesBetween a x=Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊a⌋₊ := by
  ext p
  simp only [primesBetween,Finset.mem_filter,Finset.mem_sdiff,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpx,hp⟩,hap⟩
    refine ⟨⟨hpx,hp⟩,?_⟩
    intro hpa
    have h : (p:ℝ) ≤ a := (Nat.le_floor_iff ha).mp hpa.1
    linarith
  · rintro ⟨⟨hpx,hp⟩,hnot⟩
    refine ⟨⟨hpx,hp⟩,?_⟩
    by_contra hn
    exact hnot ⟨(Nat.le_floor_iff ha).mpr (le_of_not_gt hn),hp⟩

theorem closed_product_ratio {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) :
    availableProduct a x true=primeProduct x/primeProduct a := by
  have hsub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ := by
    intro p hp
    obtain ⟨hpa,hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpa.trans (Nat.floor_mono hax),hp⟩
  apply (eq_div_iff (ne_of_gt (actual_primeProduct_pos a))).mpr
  rw [availableProduct,availablePrimes_closed,primesBetween_eq_sdiff ha,
    primeProduct_eq_survivor,primeProduct_eq_survivor]
  exact Finset.prod_sdiff hsub

theorem endpoint_card_le_one (P : Finset ℕ) (x : ℝ) :
    (P.filter (fun p : ℕ => (p:ℝ)=x)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have he := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  exact_mod_cast he

theorem endpoint_product_factor {a x : ℝ} (hx : 0 ≤ x) :
    availableProduct a x true = availableProduct a x false ∨
    availableProduct a x true = availableProduct a x false*(1-x⁻¹) := by
  let P := primesBetween a x
  have hpx : ∀ p ∈ P,(p:ℝ) ≤ x := by
    intro p hp
    exact (Nat.le_floor_iff hx).mp (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
  have hfilter : P.filter (fun p : ℕ => ¬(p:ℝ)<x)=P.filter (fun p : ℕ => (p:ℝ)=x) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp,hn⟩
      exact ⟨hp,le_antisymm (hpx p hp) (le_of_not_gt hn)⟩
    · rintro ⟨hp,he⟩
      exact ⟨hp,by rw [he]; exact lt_irrefl _⟩
  have hprod := Finset.prod_filter_mul_prod_filter_not P (fun p : ℕ => (p:ℝ)<x) (fun p => 1-(p:ℝ)⁻¹)
  rw [hfilter] at hprod
  have hbd : (∏ p ∈ P.filter (fun p : ℕ => (p:ℝ)=x),(1-(p:ℝ)⁻¹)) =
      (1-x⁻¹)^(P.filter (fun p : ℕ => (p:ℝ)=x)).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [hbd] at hprod
  have hopen : availableProduct a x false=survivorProduct (P.filter (fun p : ℕ => (p:ℝ)<x)) := by
    simp only [availableProduct,availablePrimes,Bool.false_eq_true,false_or,P]
  have hclosed : availableProduct a x true=survivorProduct P := by
    simp only [availableProduct,availablePrimes_closed,P]
  have hcard := endpoint_card_le_one P x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hzero | hone
  · left
    rw [hzero,pow_zero,mul_one] at hprod
    exact hclosed.trans (hprod.symm.trans hopen.symm)
  · right
    rw [hone,pow_one] at hprod
    rw [hclosed,hopen]
    exact hprod.symm

theorem endpoint_relative_bound {a x : ℝ} (hx : 2 ≤ x) :
    |availableProduct a x false/availableProduct a x true-1| ≤ 2/x := by
  have hc := availableProduct_pos a x true
  have ho := availableProduct_pos a x false
  rcases endpoint_product_factor (a:=a) (by linarith : 0 ≤ x) with he | he
  · rw [he,div_self (ne_of_gt ho),sub_self,abs_zero]
    positivity
  · have hx0 : 0 < x := by linarith
    have hx1 : x⁻¹ ≤ 1/2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hx
    have hfac : 0 < 1-x⁻¹ := by linarith
    have hratio : availableProduct a x false/availableProduct a x true-1=x⁻¹/(1-x⁻¹) := by
      rw [he,div_mul_eq_div_div,div_self (ne_of_gt ho)]
      rw [div_sub_one (ne_of_gt hfac)]
      congr 1
      ring
    rw [hratio,abs_of_nonneg (div_nonneg (inv_nonneg.mpr hx0.le) hfac.le)]
    apply (div_le_iff₀ hfac).mpr
    have hsmall : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    rw [div_eq_mul_inv]
    nlinarith

end NumberTheoryLean.ReferenceProductsBasics

end

end Erdos970

end OAI
