import OAI.NumberTheory.JointDickman.Amplification.CandidateMultiplicityAverage
import OAI.NumberTheory.JointDickman.Amplification.GridMultiplicityBounds

namespace OAI

/-! # Uniform expected multiplicity of actual coefficient representations -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- The entire representation count, including both large-addition
orientations, is at most twice the small-addition power under the two
first-representation remainder laws. Only Ford's sieve and Mertens enter. -/
theorem tiltedCandidatePairCount_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ) (i t : Fin M) (A D : Finset ℕ),
        (T : ℝ) ≤ Real.exp B →
        A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
        RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
        (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        (∏ p ∈ D, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        0 < t.val-i.val → t.val-i.val ≤ auxiliaryCutoff B →
        ((t.val-i.val : ℕ) : ℝ) ≤ (B : ℝ)^2 →
        η*(B : ℝ)^(32/100 : ℝ) ≤ ((t.val-i.val : ℕ) : ℝ) →
        tiltedCandidatePairCount B L T H τ C i t A D ≤ 2*(B : ℝ)^(8/1000 : ℝ) := by
  obtain ⟨τ,hτ,hτcap,hτsampling,hsmall,E,hEnn,hElim,hbound⟩ :=
    exists_grid_multiplicity_bounds hFord hM hL hη hcap
  let Etot := fun B => 2*∑ k ∈ Icc 4 L, E k B
  have hEtot : Tendsto Etot atTop (𝓝 0) := by
    have hh := (tendsto_finsetSum (Icc 4 L) hElim).const_mul 2
    simpa only [sum_const_zero,mul_zero] using hh
  have hL3 : 3 ≤ L := by omega
  refine ⟨τ,hτ,hτcap,hτsampling,?_⟩
  filter_upwards [hbound,smallCandidateAlternatives_power_bound hL3 hτ hτsampling hsmall.le,
    hEtot.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),eventually_ge_atTop 5]
    with B hB hsmallB hE hB5
  intro T H M C i t A D hT hA hD hAr hDr hAsize hDsize hj hcut hjB hjlow
  have hp : (1 : ℝ) ≤ (B : ℝ)^(8/1000 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ B)) (by norm_num)
  calc
    _ ≤ (B : ℝ)^(8/1000 : ℝ)+
        ∑ k ∈ Icc 4 L,
          (regularTiltAverage B L τ C D (fun V =>
            tiltedAllLargeLowPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) A D V) +
          regularTiltAverage B L τ C A (fun U =>
            tiltedAllLargeHighPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) D A U)) :=
      tiltedCandidatePairCount_le_classes hB5 hL3 hT i t A D hA hD
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun U V hUr hVr => hsmallB T H M C i t A D U V hAr hDr hUr hVr)
    _ ≤ (B : ℝ)^(8/1000 : ℝ)+Etot B := by
      apply add_le_add le_rfl
      dsimp only [Etot]
      rw [mul_sum]
      apply sum_le_sum
      intro k hk
      have hlo : regularTiltAverage B L τ C D (fun V =>
          tiltedAllLargeLowPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) A D V) ≤ E k B := by
        apply regularTiltAverage_bound (hEnn k B)
        intro V hV hVr
        exact (hB k hk C A D V (t.val-i.val) hA hD
          ((mem_powerset.mp hV).trans sdiff_subset) hAr hDr hVr hAsize hj hcut hjB hjlow).1
      have hhi : regularTiltAverage B L τ C A (fun U =>
          tiltedAllLargeHighPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) D A U) ≤ E k B := by
        apply regularTiltAverage_bound (hEnn k B)
        intro U hU hUr
        exact (hB k hk C D A U (t.val-i.val) hD hA
          ((mem_powerset.mp hU).trans sdiff_subset) hDr hAr hUr hDsize hj hcut hjB hjlow).2
      linarith
    _ ≤ 2*(B : ℝ)^(8/1000 : ℝ) := by linarith

end JointDickman

end OAI
