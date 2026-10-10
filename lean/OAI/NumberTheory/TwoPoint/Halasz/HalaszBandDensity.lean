import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalCount
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandSeparation

namespace OAI

/-! Literal natural-indexed MRT bands in the dyadic density and
pairwise-disjointness interfaces used by the energy estimates. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma halasz_actual_bands_disjoint (P Q : ℝ) (J : ℕ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Icc 1 J : Set ℕ)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  have hh := mrt_actual_bands_pairwise_disjoint P Q J hP hPQ hlogP
  intro i hi j hj hij
  exact @hh ⟨i, hi⟩ (Set.mem_univ _) ⟨j, hj⟩ (Set.mem_univ _)
    (fun he => hij (congrArg Subtype.val he))

theorem halasz_actual_band_density : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      ∀ N : ℕ, 0 < N →
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (((Ioc N (2*N)).filter (fun n => ¬mrtTypical (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) n)).card : ℝ) / N ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC, hd⟩ := mrt_typical_density
  refine ⟨C, hC, ?_⟩
  filter_upwards [hd] with L hd
  intro P Q J hP hPQ hlogQ hmax N hN hscale
  have : NeZero N := ⟨hN.ne'⟩
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  have heq (n : ℕ) :
      mrtTypical univ (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) n ↔
        mrtTypical (Icc 1 J) V n := by simp [mrtTypical]
  have hp := hd P Q J hP hPQ hlogQ hmax (N+1) N hscale
  change (uniformFiniteLaw (Fin N)).probability
    (fun n => ¬mrtTypical univ
      (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) (N+1+n.val)) ≤ _ at hp
  have hp' : (uniformFiniteLaw (Fin N)).probability
      (fun n => ¬mrtTypical (Icc 1 J) V (N+1+n.val)) ≤
        C * Real.log P / Real.log Q := by simpa only [heq] using hp
  exact halasz_typical_dyadic_density_bound (Icc 1 J) V _ hp'

end TwoPointCorrelations

end OAI
