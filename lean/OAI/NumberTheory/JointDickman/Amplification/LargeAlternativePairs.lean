import OAI.NumberTheory.JointDickman.Amplification.LargeHighClass
import OAI.NumberTheory.JointDickman.Amplification.OmissionEnvelope
import OAI.NumberTheory.JointDickman.Amplification.RegularPrefixChoices

namespace OAI

/-! # Actual alternative coefficient pairs in a large-addition class -/

namespace JointDickman
open Finset Classical

noncomputable def largeHighAlternativePairs (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).product
    (regularSmallAlternatives B L k τ C D V)).filter (fun XY =>
      (XY.1 \ A).card = d ∧ (XY.2 \ D).card = f ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (∏ p ∈ XY.1 \ A, p : ℕ) ∧
      (∏ p ∈ XY.1, p : ℕ) ≤ 2*(∏ p ∈ XY.2, p : ℕ) ∧
      ((∏ p ∈ XY.1, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ((∏ p ∈ XY.2, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ∃ c : ℕ, 0 < c ∧ (∏ p ∈ XY.1, p) = (∏ p ∈ XY.2, p)+j*c ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c))

theorem retained_addition_product (A X : Finset ℕ) :
    (∏ p ∈ X, p : ℕ) = (∏ p ∈ A \ (A \ X), p)*(∏ p ∈ X \ A, p) := by
  have he : A \ (A \ X) ∪ (X \ A) = X := by
    ext p
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hd : Disjoint (A \ (A \ X)) (X \ A) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (mem_sdiff.mp hq).2 (mem_sdiff.mp hp).1
  rw [← prod_union hd,he]

theorem alternative_additions_subset_remainder {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) : X \ A ⊆ U := by
  intro p hp
  have h := (mem_powerset.mp (mem_filter.mp hX).1) (mem_sdiff.mp hp).1
  exact (mem_union.mp h).resolve_left (mem_sdiff.mp hp).2

/-- Every actual pair maps to a fixed old-prime choice, a fixed opposite
addition, and an element of the numerically sieved class. -/
theorem largeHighAlternativePairs_encoding {B L k j d f : ℕ} {τ C Δ : ℝ}
    {A U D V X Y : Finset ℕ} (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B) (hU : U ⊆ auxiliaryPrimes B \ A)
    (hAr : RegularPrimeSet B L τ C A) (hUr : RegularPrimeSet B L τ C U)
    (hDr : RegularPrimeSet B L τ C D) (hVr : RegularPrimeSet B L τ C V)
    (hXY : (X,Y) ∈ largeHighAlternativePairs B L k j d f τ C Δ A U D V) :
    A \ X ∈ omissionEnvelope B L k τ A d ∧
    D \ Y ∈ omissionEnvelope B L k τ D f ∧
    Y \ D ∈ regularPrefixChoices B L k V f ∧
    X \ A ∈ (activeHighAdditionClass B L k τ C Δ A
      (∏ p ∈ A \ (A \ X), p) j
      ((∏ p ∈ D \ (D \ Y), p)*(∏ p ∈ Y \ D, p)) d).filter (fun Z => Z ⊆ U) := by
  obtain ⟨hXY,hd,hf,hlarge,hsize,hXsize,hYsize,c,hc,hrel,hcr⟩ := mem_filter.mp hXY
  obtain ⟨hX,hY⟩ := mem_product.mp hXY
  have hZA := alternative_additions_subset_remainder hX
  have hYV := alternative_additions_subset_remainder hY
  have hZP : X \ A ⊆ auxiliaryPrimes B := hZA.trans (hU.trans sdiff_subset)
  have hXP : X ⊆ auxiliaryPrimes B :=
    (mem_powerset.mp (mem_filter.mp hX).1).trans (union_subset hA (hU.trans sdiff_subset))
  have hepos : 0 < (∏ p ∈ A \ (A \ X), p : ℕ) :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA ((mem_sdiff.mp hp).1))).pos)
  have her : (0 : ℝ) < (∏ p ∈ A \ (A \ X), p : ℕ) := by exact_mod_cast hepos
  have hzpos : 0 < (∏ p ∈ X \ A, p : ℕ) :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hZP hp)).pos)
  have hdecomp := retained_addition_product A X
  have hydecomp := retained_addition_product D Y
  let e := (∏ p ∈ A \ (A \ X), p : ℕ)
  let b := (∏ p ∈ D \ (D \ Y), p : ℕ)*(∏ p ∈ Y \ D, p : ℕ)
  let z := (∏ p ∈ X \ A, p : ℕ)
  have heq : e*z = b+j*c := by
    dsimp only [e,b,z]
    rw [← hdecomp,← hydecomp]
    exact hrel
  have hbound : (e*z : ℕ) ≤ 2*b := by
    dsimp only [e,b,z]
    rw [← hdecomp,← hydecomp]
    exact hsize
  have hlo : highAdditionWindow e b ≤ (z : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*e)).mpr
    have hrelr : (b : ℝ) ≤ e*z := by exact_mod_cast (by omega : b ≤ e*z)
    change (b : ℝ) ≤ (z : ℝ)*(2*e)
    nlinarith [show (0 : ℝ) ≤ e*z by positivity]
  have hhi : (z : ℝ) ≤ 4*highAdditionWindow e b := by
    have hr : (e : ℝ)*z ≤ 2*b := by exact_mod_cast hbound
    calc
      _ ≤ (2*(b : ℝ))/(e : ℝ) := (le_div_iff₀ her).mpr (by nlinarith [hr])
      _ = _ := by unfold highAdditionWindow; ring
  have hactive : (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ))/4 ≤ highAdditionWindow e b := by
    refine ⟨?_,?_⟩
    · dsimp only [b]
      rwa [← hydecomp]
    · have hl : Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (z : ℝ) := hlarge
      linarith
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hd] using regular_omission_mem_envelope hk hτ hℓ hAr hUr hX
  · simpa only [hf] using regular_omission_mem_envelope hk hτ hℓ hDr hVr hY
  · exact mem_filter.mpr ⟨mem_powerset.mpr
      ((mem_filter.mp hY).2.2.trans (primePrefix_mono B _ hYV)),hf⟩
  · apply mem_filter.mpr
    refine ⟨?_,hZA⟩
    change X \ A ∈ activeHighAdditionClass B L k τ C Δ A e j b d
    rw [activeHighAdditionClass,ite_eq_left hactive]
    apply mem_filter.mpr
    refine ⟨mem_numericAdditionClass.mpr ⟨hZP,hd,hlo,hhi,c,hc,heq,hcr⟩,
      hZA.trans hU,?_,(mem_filter.mp hX).2.2⟩
    have hdiv : z ∣ ∏ p ∈ X, p := prod_dvd_prod_of_subset _ _ id sdiff_subset
    have hprodpos : 0 < ∏ p ∈ X, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hXP hp)).pos)
    exact (show (z : ℝ) ≤ (∏ p ∈ X, p : ℕ) by exact_mod_cast Nat.le_of_dvd hprodpos hdiv).trans hXsize

end JointDickman

end OAI
