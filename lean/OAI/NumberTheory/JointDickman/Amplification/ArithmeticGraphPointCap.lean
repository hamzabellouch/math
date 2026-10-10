import OAI.NumberTheory.JointDickman.Amplification.GraphCandidateDecoding
import OAI.NumberTheory.JointDickman.Probability.QuotientSiteUnion
import OAI.NumberTheory.JointDickman.Amplification.CandidateWeightCap

namespace OAI

/-! # A pointwise graph bound valid even on site-square exceptions -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem graphTripleWeight_le_one {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T n : ℕ) (g : GraphCoefficientTriple),
      graphTripleWeight B L τ C T g n/(B : ℝ) ≤ 1 := by
  filter_upwards [six_regular_weights_small hL hτ hτsmall,eventually_ge_atTop 1] with B hB hB1
  intro C T n g
  let a := ∏ p ∈ g.2.1, p
  let b := ∏ p ∈ g.2.2, p
  let c := ∏ p ∈ g.1, p
  let j := graphTripleLag g
  let W := fun d m => regularCoefficientWeight B L τ C d*arithmeticResidueWeight B L τ C m
  have hW d m : 0 ≤ W d m := mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
    (regularResidueWeight_nonneg _ _ _ _ _)
  have hc : amplificationOuterWeight B c*W c (divisorEdgeInverse a b c n) ≤
      W c (divisorEdgeInverse a b c n) :=
    mul_le_of_le_one_left (hW _ _) (amplificationBump_bounds _).2
  have ha : W a (n/b)*amplificationInnerWeight T a c ≤ W a (n/b) :=
    mul_le_of_le_one_right (hW _ _) (amplificationBump_bounds _).2
  have hb : W b (((n : ℤ)+j).toNat/a)*amplificationInnerWeight T b c ≤ W b (((n : ℤ)+j).toNat/a) :=
    mul_le_of_le_one_right (hW _ _) (amplificationBump_bounds _).2
  have hp : graphTripleWeight B L τ C T g n ≤
      W c (divisorEdgeInverse a b c n)*W a (n/b)*W b (((n : ℤ)+j).toNat/a) := by
    change (amplificationOuterWeight B c*regularCoefficientWeight B L τ C c*
      arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n))*
      (W a (n/b)*amplificationInnerWeight T a c)*
      (W b (((n : ℤ)+j).toNat/a)*amplificationInnerWeight T b c) ≤ _
    rw [mul_assoc (amplificationOuterWeight B c)]
    exact mul_le_mul (mul_le_mul hc ha (mul_nonneg (hW _ _) (amplificationBump_bounds _).1)
      (hW _ _)) hb (mul_nonneg (hW _ _) (amplificationBump_bounds _).1)
        (mul_nonneg (hW _ _) (hW _ _))
  calc
    _ ≤ (W c (divisorEdgeInverse a b c n)*W a (n/b)*W b (((n : ℤ)+j).toNat/a))/(B : ℝ) :=
      div_le_div_of_nonneg_right hp (Nat.cast_nonneg B)
    _ ≤ (B : ℝ)^(-(7/100 : ℝ)) := hB C c a b _ _ _
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hB1) (by norm_num)

theorem graph_endpoint_prime_subsets {B T M N u : ℕ} {i k : Fin M}
    (hik : i < k) {g : GraphCoefficientTriple} (hg : g ∈ arithmeticGraphTriples B T)
    (hlag : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ))
    (hn : u+(i.val+1) ∈ graphTripleEdges N g) :
    g.2.2 ⊆ coefficientPrimeSet B (u+(i.val+1)) ∧
      g.2.1 ⊆ coefficientPrimeSet B (u+(k.val+1)) := by
  have hs := graphTriple_subsets hg
  have hbdiv : (∏ p ∈ g.2.2, p) ∣ u+(i.val+1) := (mem_filter.mp hn).2.1
  have hadiv : (∏ p ∈ g.2.1, p) ∣ u+(k.val+1) := by
    have h := (mem_filter.mp hn).2.2.1
    have he : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g) = (u+(k.val+1) : ℕ) := by
      rw [hlag,Int.ofNat_sub hik.le]
      push_cast
      ring
    rw [he] at h
    exact_mod_cast h
  exact ⟨(primeProduct_dvd_site_iff hs.2.2).mp hbdiv,
    (primeProduct_dvd_site_iff hs.2.1).mp hadiv⟩

theorem graph_regular_endpoint_count {B L T M N u : ℕ} {τ C : ℝ}
    (hcount : ∀ S R : Finset ℕ, RegularPrimeSet B L τ C S → RegularPrimeSet B L τ C R →
      2^(S ∪ R).card ≤ B)
    {i k : Fin M} (hik : i < k) {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T)
    (hlag : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ))
    (hn : u+(i.val+1) ∈ graphTripleEdges N g)
    (hw : graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0) :
    2^(coefficientPrimeSet B (u+(i.val+1))).card ≤ B ∧
      2^(coefficientPrimeSet B (u+(k.val+1))).card ≤ B := by
  have hs := graphTriple_subsets hg
  have hr := graphTripleWeight_nonzero_regular hg hw
  have hbdiv : (∏ p ∈ g.2.2, p) ∣ u+(i.val+1) := (mem_filter.mp hn).2.1
  have hshift : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g).toNat = u+(k.val+1) := by
    rw [hlag,Int.ofNat_sub hik.le]
    omega
  have hsub := graph_endpoint_prime_subsets hik hg hlag hn
  have hadiv := (primeProduct_dvd_site_iff hs.2.1).mpr hsub.2
  have hlo := hcount g.2.2 _ hr.2.2.1 hr.2.2.2.1
  have hhi := hcount g.2.1 _ hr.2.1 hr.2.2.2.2
  rw [coefficientPrimeSet_union_quotient hs.2.2 hbdiv] at hlo
  rw [hshift,coefficientPrimeSet_union_quotient hs.2.1 hadiv] at hhi
  exact ⟨hlo,hhi⟩

end JointDickman

end OAI
