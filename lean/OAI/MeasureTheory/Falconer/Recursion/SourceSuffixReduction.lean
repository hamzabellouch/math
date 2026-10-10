import OAI.MeasureTheory.Falconer.Recursion.SuffixPowerLoss
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem source_positive_distance_suffix {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
      d.StronglySeparated → d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i+1 ≤ d.J →
      let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
      let p := policyDepth A d.N d.q d.a d.t
      d.a+d.t < 2*p →
      d.coincidence ≤ ENNReal.ofReal (((2:ℝ)^d.N)^
        (A p-intervalMin A p d.t+4000*(lam+sig)+eps)) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₀,hN₀⟩ := uniform_actual_suffix_reduction hsig heps
    (sourceSmoothingLevels_pos hsig hkap)
  refine ⟨N₀,?_⟩
  intro d hlam' hsig' hq' hJ' hN hQ hs hX hY B δ hprof hw htN hi A p hsuffix
  have hq : 0 < d.q := by
    rw [hq']
    exact sourcePolicyBlock_pos (by omega : 0 < d.N) hkap
  have hh := hN₀ d hsig' hJ' hN hQ hs hq (hlam' ▸ hlam) hX hY B δ hprof hw htN
    (by omega : d.i ≤ sourceSmoothingLevels sig kap) hsuffix
  simpa only [hlam'] using hh

end PlanarFalconer

end OAI
