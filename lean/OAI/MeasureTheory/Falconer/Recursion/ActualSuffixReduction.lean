import OAI.MeasureTheory.Falconer.Recursion.SuffixBinAssembly
import OAI.MeasureTheory.Falconer.Recursion.SuffixNormalization

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_suffix_reduction_explicit {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
      let p := policyDepth A d.N d.q d.a d.t
      d.a+d.t < 2*p →
      d.coincidence ≤ 2255*ENNReal.ofReal (((2:ℝ)^d.N)^
        (A p-intervalMin A p d.t+2000*(d.lam+sig)+12*d.lam)) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₀,hN₀⟩ := uniform_suffix_bin_assembly hsig hJ
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq hX hY B δ hprof hw htN hi A p hsuffix
  have := hprof.probability
  have hb := hN₀ d hsig' hJ' hN hQ hs hq hX hY B δ hprof hw htN hi hsuffix
  have hn := d.suffix_normalized_from_bins p _ hb
  have hpow : ((2:ℝ)^d.N)^(-(d.mass d.t-d.mass p)+height A p d.t+2000*(d.lam+sig)+12*d.lam)*
      (2:ℝ)^((d.t:ℝ)-p) =
      ((2:ℝ)^d.N)^(A p-intervalMin A p d.t+2000*(d.lam+sig)+12*d.lam) := by
    simpa only [A,add_assoc] using suffix_profile_power_identity d.mass
      (by omega : 0 < d.N) p d.t (2000*(d.lam+sig)+12*d.lam)
  have hc : ((bandOffsets 100).card : ℝ≥0∞)*((bandOffsets 3).card : ℝ≥0∞) = 2255 := by
    norm_num [bandOffsets]
  apply hn.trans_eq
  congr 1
  calc
    _ = (((bandOffsets 100).card : ℝ≥0∞)*((bandOffsets 3).card : ℝ≥0∞))*
        (ENNReal.ofReal (((2:ℝ)^d.N)^(-(d.mass d.t-d.mass p)+height A p d.t+2000*(d.lam+sig)+12*d.lam))*
          ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-p))) := by ring
    _ = 2255*ENNReal.ofReal
        (((2:ℝ)^d.N)^(-(d.mass d.t-d.mass p)+height A p d.t+2000*(d.lam+sig)+12*d.lam)*
          (2:ℝ)^((d.t:ℝ)-p)) := by
      rw [hc,← ENNReal.ofReal_mul (by positivity)]
    _ = _ := by rw [hpow]

end PlanarFalconer

end OAI
