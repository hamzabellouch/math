import OAI.MeasureTheory.Falconer.Radial.ActualSuffixProjection
import OAI.MeasureTheory.Falconer.Recursion.SuffixLocalBins
import OAI.MeasureTheory.Falconer.Recursion.SuffixRetainedPairs

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_actual_suffix_local_bins {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
      d.a+d.t < 2*p → ∀ c ∈ d.suffixRetained p,
      (binL2Norm (d.suffixData c).distance d.width)^2 ≤
        (((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
          (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
            2000*(d.lam+sig)+12*d.lam))) * (d.suffixFullDistance c univ)^2 := by
  obtain ⟨N₀,hN₀⟩ := uniform_actual_suffix_projection hsig hJ 1
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq B δ hprof hw htN hi p hsuffix c hc
  let := hprof.probability
  obtain ⟨hP,hC,hPX,hCY,x,hx,y,hy,hg⟩ := d.suffix_retained_spec hc
  have hproj := hN₀ d hsig' hJ' hN hQ hs hq B δ hprof hw htN hi hsuffix
    c.1 c.2 hP hC hPX hCY x hx y hy hg
  have hh := d.suffix_local_bin_sq hQ hs (by omega : d.a+d.t ≤ 2*p) hP hC hPX hCY hproj
  apply hh.trans_eq
  rw [PositiveDistanceData.suffixFullDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [preimage_univ,PositiveDistanceData.cellPair]
  rw [← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ]
  ring

end PlanarFalconer

end OAI
