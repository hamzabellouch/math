import OAI.NumberTheory.JointDickman.Arithmetic.MixedAffineHarmonic
import OAI.NumberTheory.JointDickman.Arithmetic.SievePrefixProduct

namespace OAI

/-! # The harmonic sieve at the actual large-addition prefix cutoff -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def numericAdditionSieveCutoff (B : ℕ) (g : ℝ) : ℕ :=
  ⌊Real.exp ((B : ℝ)^g)⌋₊

/-- The prime cutoff and the Euler-product estimate are instantiated;
only the concrete progression geometry is left for an application. -/
theorem numeric_prefix_harmonic_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {κ g ε : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hg1 : g < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (E : Finset ℕ) (a b c d : ℤ) (q W : ℝ) (u v : ℕ),
        E ⊆ auxiliaryPrimes B → (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) →
        0 ≤ q → q ≤ 1 → 0 < W → u ≤ v →
        (∀ p ∈ primePrefix B g (auxiliaryPrimes B) \ E,
          (b : ZMod p) ≠ 0 ∧ (d : ZMod p) ≠ 0 ∧ (a : ZMod p)*d-c*b ≠ 0) →
        (∀ n ∈ Ico u v, W ≤ (a : ℝ)+(b : ℝ)*n) →
        (∑ n ∈ Ico u v, (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ E,
          residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n))/
            ((a : ℝ)+(b : ℝ)*n)) ≤
          K*((v : ℝ)-u)/W*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+
            2*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W := by
  obtain ⟨K,hK,hbound⟩ := mixed_affine_harmonic_sieve hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [numeric_sieve_prefix_product hM hκ hg hg1.le hε,
    eventually_ge_atTop 1, auxiliaryCutoff_tendsto.eventually_ge_atTop 4] with B hprod hB hcut
  intro E a b c d q W u v hE hEsize hq hq1 hW huv hdet hden
  let P := primePrefix B g (auxiliaryPrimes B) \ E
  let Z := numericAdditionSieveCutoff B g
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hZ : 2 ≤ Z := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ Real.exp ((B : ℝ)^g)
    have hp : (1 : ℝ) ≤ (B : ℝ)^g := Real.one_le_rpow hB1 hg.le
    have he := Real.add_one_le_exp ((B : ℝ)^g)
    linarith
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Z ∧ 4 ≤ p := by
    have hpre := mem_sdiff.mp hp
    have hmemb : p ∈ (auxiliaryPrimes B).filter (fun p : ℕ => Real.log p ≤ (B : ℝ)^g) := by
      simpa only [primePrefix,ite_eq_left hg1] using hpre.1
    have hpA : p ∈ auxiliaryPrimes B := (mem_filter.mp hmemb).1
    have hprime := auxiliaryPrimes_prime B p hpA
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : Real.log p ≤ (B : ℝ)^g := (mem_filter.mp hmemb).2
    have hpZ : p ≤ Z := Nat.le_floor (by
      simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hlog)
    have hp4 : 4 ≤ p := by
      have hh := (mem_filter.mp hpA).2
      have hNat : auxiliaryCutoff B < p := by exact_mod_cast hh
      omega
    exact ⟨hprime,hpZ,hp4⟩
  have hh := hbound P a b c d q W u v Z hq hq1 hW huv hZ hP hdet hden
  have he := hprod E q hE hEsize hq hq1
  have hnon : 0 ≤ K*((v : ℝ)-u) := mul_nonneg hK.le (sub_nonneg.mpr (by exact_mod_cast huv))
  refine hh.trans ?_
  calc
    _ ≤ (K*((v : ℝ)-u)*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+2*(Z+1 : ℝ)*(Z : ℝ)^2)/W :=
      div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left he hnon) le_rfl) hW.le
    _ = _ := by dsimp [Z]; ring

end JointDickman

end OAI
