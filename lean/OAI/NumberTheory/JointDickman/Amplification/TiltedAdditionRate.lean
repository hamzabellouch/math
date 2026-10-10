import OAI.NumberTheory.JointDickman.Amplification.TiltedAdditionTail
import OAI.NumberTheory.JointDickman.Amplification.TiltedPrefixMeans
import OAI.NumberTheory.JointDickman.Amplification.MultiplicityChernoff

namespace OAI

/-! # The large-addition availability estimate from Mertens -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def clippedAdditionDensity (B : ℕ) (g : ℝ) (Z : Finset ℕ) : ℝ :=
  min ((Z.card : ℝ)/(g*auxiliaryLogLength B)) (1/2)

/-- Both the inclusion cost and the lower-tail cost are present. The first
remainder's regularity is inside the probability, as in (27) of moments.tex. -/
theorem tilted_addition_rate_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {τ δ ε : ℝ} (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (A Z : Finset ℕ),
      A ⊆ auxiliaryPrimes B → Z ⊆ auxiliaryPrimes B \ A →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
      (∏ p ∈ Z, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
      Z ⊆ primePrefix B ((k : ℝ)/L) Z →
      (∑ R ∈ (auxiliaryPrimes B \ A).powerset,
        if Z ⊆ R ∧ RegularPrimeSet B L τ C R then
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) R else 0) ≤
        Real.exp 1*((1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ))*
          Real.exp ((-((k : ℝ)/L)*halfPoissonRate
            (1/2-clippedAdditionDensity B ((k : ℝ)/L) Z)+((k : ℝ)/L)*δ+
              (-Real.log (2*δ))*τ+ε)*auxiliaryLogLength B) := by
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hkL : k ≤ L := (mem_Icc.mp hk).2
  have hL : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hg : 0 < (k : ℝ)/L := div_pos (by exact_mod_cast (by omega : 0 < k)) hLr
  have hg1 : (k : ℝ)/L ≤ 1 := (div_le_one hLr).mpr (by exact_mod_cast hkL)
  filter_upwards [tilted_prefix_mean_uniform hM (by norm_num : (0 : ℝ) < 32/5) hg hg1 hε,
    tilted_required_product_bound, auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hmean hprod hℓ
  intro C A Z hA hZ hAsize hZsize hprefix
  have hZA : Disjoint A Z := disjoint_left.mpr (fun p hpA hpZ => (mem_sdiff.mp (hZ hpZ)).2 hpA)
  have hAZ : A ∪ Z ⊆ auxiliaryPrimes B := union_subset hA (hZ.trans sdiff_subset)
  have hAZsize : (∏ p ∈ A ∪ Z, p : ℕ) ≤ Real.exp ((32/5 : ℝ)*B) := by
    rw [prod_union hZA,Nat.cast_mul]
    calc
      _ ≤ Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B) :=
        mul_le_mul hAsize hZsize (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hm := hmean (A ∪ Z) hAZ hAZsize
  have hs : (auxiliaryPrimes B \ A) \ Z = auxiliaryPrimes B \ (A ∪ Z) := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  let g : ℝ := (k : ℝ)/L
  let r := clippedAdditionDensity B g Z
  let m := ∑ p ∈ ((auxiliaryPrimes B \ A) \ Z) ∩ primePrefix B g (auxiliaryPrimes B),
    1/(2*(p : ℝ)-1)
  let t := -Real.log (2*max δ (1/2-r))
  have hr : 0 ≤ r := le_min (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hg.le hℓ.le)) (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hω : g*r*auxiliaryLogLength B ≤ Z.card := by
    have hh : r ≤ (Z.card : ℝ)/(g*auxiliaryLogLength B) := min_le_left _ _
    have hh' := (le_div_iff₀ (mul_pos hg hℓ)).mp hh
    nlinarith
  have hm' : (g/2-ε)*auxiliaryLogLength B ≤ m := by
    have he : g/2-ε ≤ m/auxiliaryLogLength B := by
      dsimp only [m,g]
      rw [hs]
      linarith [(abs_le.mp hm).1]
    exact (le_div_iff₀ hℓ).mp he
  have ht : 0 ≤ t := (halfPoisson_clamped_chernoff (u := 1/2-r) (by linarith)
    (by linarith) hδ hδ1).1
  have hrate := multiplicity_chernoff_exponent hg.le hℓ.le hτ hε.le hδ hδ1 hr hr1 hω hm'
  have hprob := tilted_addition_regular_tail (τ := τ) (C := C) A Z hZ hk hprefix ht
  have hprod' := hprod Z (hZ.trans sdiff_subset) hZsize
  refine hprob.trans ?_
  exact mul_le_mul hprod' (Real.exp_le_exp.mpr hrate) (Real.exp_pos _).le
    (mul_nonneg (Real.exp_pos _).le (by positivity))

end JointDickman

end OAI
