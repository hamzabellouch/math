import OAI.NumberTheory.JointDickman.Amplification.LargeLowNumericAddition
import OAI.NumberTheory.JointDickman.Amplification.LargeAdditionAvailability

namespace OAI

/-! # First-remainder availability for the large low-endpoint addition -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def availableLowNumericAdditionClass (B L k : ℕ) (τ C : ℝ)
    (A : Finset ℕ) (e j b d : ℕ) (W : ℝ) : Finset (Finset ℕ) :=
  (lowNumericAdditionClass B L τ C e j b d W).filter (fun Z =>
    Z ⊆ auxiliaryPrimes B \ A ∧
    (∏ p ∈ Z, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
    Z ⊆ primePrefix B ((k : ℝ)/L) Z)

/-- The Poisson penalty in the first remainder and the numeric Rankin
exponent cancel to half the binary entropy, as in equations (27)--(29).
The expectation keeps the first remainder's full regularity condition. -/
theorem large_low_addition_availability_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g κ Δ δ τ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hκ : 0 < κ) (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (C : ℝ) (A : Finset ℕ) (e j b d : ℕ) (W : ℝ),
        A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e*b : ℕ) ≤ Real.exp (κ*B) → (j : ℝ) ≤ (B : ℝ)^2 →
        2*(j : ℝ) ≤ W → Real.exp ((B : ℝ)^(g-Δ))/4 ≤ W →
        tiltedRegularSubsetCount B L τ C A
          (availableLowNumericAdditionClass B L k τ C A e j b d W) ≤
          K/(j : ℝ)*Real.exp
            (largeAvailabilityExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B) := by
  obtain ⟨K,hK,hnumeric⟩ := large_low_numeric_addition_bound hFord hM hk hkg hg hg1 hκ hΔ hgap hδ hδ1 hε
  refine ⟨Real.exp 1*K,by positivity,?_⟩
  filter_upwards [hnumeric,tilted_addition_rate_bound hM hk hτ hδ hδ1 hε] with B hn hp
  intro C A e j b d W hA hAsize he hb hj hcut hej hsize hjB hW hWlarge
  let ℓ := auxiliaryLogLength B
  let r := min ((d : ℝ)/(g*ℓ)) (1/2)
  let E := -g*halfPoissonRate (1/2-r)+g*δ+(-Real.log (2*δ))*τ+ε
  let F := availableLowNumericAdditionClass B L k τ C A e j b d W
  have hpoint (Z : Finset ℕ) (hZ : Z ∈ F) :
      (∑ R ∈ (auxiliaryPrimes B \ A).powerset,
        if Z ⊆ R ∧ RegularPrimeSet B L τ C R then
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) R else 0) ≤
        (Real.exp 1*Real.exp (E*ℓ))*((1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ)) := by
    obtain ⟨hZ,hsub,hprod,hpre⟩ := mem_filter.mp hZ
    have hd := (mem_lowNumericAdditionClass.mp hZ).2.1
    have hh := hp C A Z hA hsub hAsize hprod hpre
    rw [hkg] at hh
    simp only [clippedAdditionDensity,hd] at hh
    convert hh using 1; dsimp only [E,r,ℓ]; ring
  have hsub : F ⊆ lowNumericAdditionClass B L τ C e j b d W := filter_subset _ _
  have hsum : tiltedRegularSubsetCount B L τ C A F ≤
      (Real.exp 1*Real.exp (E*ℓ))*
        ∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
          (1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ) := by
    rw [tiltedRegularSubsetCount_eq_sum]
    calc
      _ ≤ ∑ Z ∈ F, (Real.exp 1*Real.exp (E*ℓ))*((1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ)) :=
        sum_le_sum hpoint
      _ = (Real.exp 1*Real.exp (E*ℓ))*∑ Z ∈ F, (1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ) :=
        (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) (by positivity)
  have hnum := hn τ C e j b d W hτ hτ1 he hb hj hcut hej hsize hjB hW hWlarge
  refine hsum.trans ((mul_le_mul_of_nonneg_left hnum (by positivity)).trans_eq ?_)
  have heq : E+largeAdditionExponent g Δ δ τ ε ℓ d =
      largeAvailabilityExponent g Δ δ τ ε ℓ d := by
    have hh := halfRankin_sub_halfPoisson r
    dsimp only [E,largeAdditionExponent,largeAvailabilityExponent,r] at *
    nlinarith
  calc
    _ = (Real.exp 1*K)/(j : ℝ)*
        Real.exp ((E+largeAdditionExponent g Δ δ τ ε ℓ d)*ℓ) := by
      have hexp : Real.exp ((E+largeAdditionExponent g Δ δ τ ε ℓ d)*ℓ) =
          Real.exp (E*ℓ)*Real.exp (largeAdditionExponent g Δ δ τ ε ℓ d*ℓ) := by
        rw [add_mul,Real.exp_add]
      rw [hexp]
      ring
    _ = _ := by rw [heq]

end JointDickman

end OAI
