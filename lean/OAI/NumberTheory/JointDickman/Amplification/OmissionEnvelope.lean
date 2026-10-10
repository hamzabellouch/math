import OAI.NumberTheory.JointDickman.Amplification.RegularOmissionEntropy

namespace OAI

/-! # An omission envelope independent of the random remainder -/

namespace JointDickman
open Finset Classical

/-- The old-prime choices can be enumerated before drawing the other
remainder.  This is essential when applying the inclusion bound to a fixed
numeric addition. -/
noncomputable def omissionEnvelope (B L k : ℕ) (τ : ℝ) (A : Finset ℕ) (d : ℕ) : Finset (Finset ℕ) :=
  let Q := primePrefix B ((k : ℝ)/L) A
  let r := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  A.powerset.filter (fun O =>
    |((O ∩ Q).card : ℝ)/auxiliaryLogLength B-((k : ℝ)/L)*r| ≤ 3*τ ∧
      ((O \ Q).card : ℝ) ≤ 4*τ*auxiliaryLogLength B)

theorem regular_omission_mem_envelope {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hU : RegularPrimeSet B L τ C U)
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    A \ X ∈ omissionEnvelope B L k τ A (X \ A).card := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ U)
  let P := primePrefix B ((k : ℝ)/L) A
  have hi : (A \ X) ∩ Q = (A \ X) ∩ P := by
    dsimp only [Q,P]
    rw [← primePrefix_inter,← primePrefix_inter,
      inter_eq_left.mpr (sdiff_subset.trans subset_union_left),inter_eq_left.mpr sdiff_subset]
  have hs : (A \ X) \ Q = (A \ X) \ P := by
    ext p
    have hh := Finset.ext_iff.mp hi p
    simp only [Finset.mem_inter,Finset.mem_sdiff] at *
    tauto
  apply mem_filter.mpr
  refine ⟨mem_powerset.mpr sdiff_subset,?_,?_⟩
  · have hh := regular_omission_clipped_window hk hτ hℓ hA hU hX
    change |(((A \ X) ∩ Q).card : ℝ)/auxiliaryLogLength B-
      ((k : ℝ)/L)*clippedAdditionDensity B ((k : ℝ)/L) (X \ A)| ≤ 3*τ at hh
    rw [hi] at hh
    exact hh
  · have hh := regularSmallAlternatives_omissions
      ((mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2) hk hA hX
    change (((A \ X) \ Q).card : ℝ) ≤ _ at hh
    rw [hs] at hh
    exact hh

theorem omissionEnvelope_count (B L k : ℕ) (τ : ℝ) (A : Finset ℕ) (d : ℕ) :
    (omissionEnvelope B L k τ A d).card ≤
      (subsetCardWindow (primePrefix B ((k : ℝ)/L) A) (auxiliaryLogLength B) ((k : ℝ)/L)
        (min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)) τ).card *
      (((A \ primePrefix B ((k : ℝ)/L) A).powerset).filter
        (fun O => (O.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card := by
  let Q := primePrefix B ((k : ℝ)/L) A
  let r := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  let target := (subsetCardWindow Q (auxiliaryLogLength B) ((k : ℝ)/L) r τ).product
    (((A \ Q).powerset).filter (fun O => (O.card : ℝ) ≤ 4*τ*auxiliaryLogLength B))
  let enc := fun O : Finset ℕ => (O ∩ Q,O \ Q)
  have hmap (O : Finset ℕ) (hO : O ∈ omissionEnvelope B L k τ A d) : enc O ∈ target := by
    obtain ⟨hO,hpre,hhigh⟩ := mem_filter.mp hO
    have hOA := mem_powerset.mp hO
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr inter_subset_right,hpre⟩,
      mem_filter.mpr ⟨mem_powerset.mpr (sdiff_subset_sdiff hOA subset_rfl),hhigh⟩⟩
  have hinj : Set.InjOn enc (omissionEnvelope B L k τ A d) := by
    intro O _ R _ he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change O ∩ Q = R ∩ Q at h₁
    change O \ Q = R \ Q at h₂
    ext p
    have h₁ := Finset.ext_iff.mp h₁ p
    have h₂ := Finset.ext_iff.mp h₂ p
    simp only [Finset.mem_inter,Finset.mem_sdiff] at *
    tauto
  have hc := card_le_card_of_injOn enc hmap hinj
  simpa only [target,Finset.product_eq_sprod,card_product,Q,r] using hc

theorem omissionEnvelope_entropy {L k : ℕ} (hk : k ∈ Icc 1 L) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ τ₀ →
      ∀ (B : ℕ) (C : ℝ) (A : Finset ℕ) (d : ℕ), 0 < auxiliaryLogLength B →
        RegularPrimeSet B L τ C A →
        ((omissionEnvelope B L k τ A d).card : ℝ) ≤
          ((A.card : ℝ)+1)*Real.exp
            (((((k : ℝ)/L)/2)*Real.binEntropy
              (2*min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2))+
                ε+highOmissionExponent τ)*auxiliaryLogLength B) := by
  have hL : 1 ≤ L := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  have hg : 0 < (k : ℝ)/L := div_pos
    (by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 0 < k))
    (by exact_mod_cast (by omega : 0 < L))
  obtain ⟨τ₁,hτ₁,hwin⟩ := subset_card_window_entropy hg hε
  refine ⟨min τ₁ (1/100),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall B C A d hℓ hA
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hsmall : τ ≤ 1/100 := hτsmall.trans (min_le_right _ _)
  let Q := primePrefix B ((k : ℝ)/L) A
  let r := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  have hr : 0 ≤ r := le_min (div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le) (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hP : |(Q.card : ℝ)/auxiliaryLogLength B-((k : ℝ)/L)/2| ≤ τ := by
    have hlo := (le_div_iff₀ hℓ).mpr (hA.1 k hk).1
    have hup := (div_le_iff₀ hℓ).mpr (hA.1 k hk).2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hpre := hwin Q (auxiliaryLogLength B) r τ hℓ hτ.le hτ₁' hr hr1 hP
  have hregion : ((A \ Q).card : ℝ) ≤ (1/2+τ)*auxiliaryLogLength B :=
    (show ((A \ Q).card : ℝ) ≤ A.card by exact_mod_cast card_le_card sdiff_subset).trans (hA.total_upper hL)
  have hhigh := high_omission_count_bound (A \ Q) hτ hsmall hℓ.le hregion
  have hc : ((omissionEnvelope B L k τ A d).card : ℝ) ≤
      (subsetCardWindow Q (auxiliaryLogLength B) ((k : ℝ)/L) r τ).card*
        (((A \ Q).powerset.filter (fun O => (O.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card : ℝ) := by
    exact_mod_cast omissionEnvelope_count B L k τ A d
  have hQsub : Q ⊆ A := by
    dsimp only [Q,primePrefix]
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  have hcA : (Q.card : ℝ)+1 ≤ (A.card : ℝ)+1 := by
    have hh : (Q.card : ℝ) ≤ A.card := by exact_mod_cast card_le_card hQsub
    linarith
  have hpre' := hpre.trans (mul_le_mul_of_nonneg_right hcA (Real.exp_pos _).le)
  refine hc.trans ((mul_le_mul hpre' hhigh (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (Real.exp_pos _).le)).trans_eq ?_)
  rw [mul_assoc,← Real.exp_add]
  congr 2
  dsimp [highOmissionExponent,r]
  ring

end JointDickman

end OAI
