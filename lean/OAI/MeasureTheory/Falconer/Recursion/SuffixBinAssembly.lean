import OAI.MeasureTheory.Falconer.Recursion.ActualSuffixLocalBins
import OAI.MeasureTheory.Falconer.Recursion.SuffixCoarseDomination
import OAI.MeasureTheory.Falconer.Recursion.SuffixBinGeometry
import OAI.MeasureTheory.Falconer.Geometry.FiniteBinComparison

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_suffix_bin_assembly {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
      d.a+d.t < 2*p →
      (binL2Norm d.distance d.width)^2 ≤
        (((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
          (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
            2000*(d.lam+sig)+12*d.lam))) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹ *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₁,h₁⟩ := uniform_actual_suffix_local_bins hsig hJ
  obtain ⟨N₂,h₂⟩ := uniform_suffix_coarse_domination hsig hJ
  refine ⟨max N₁ N₂,?_⟩
  intro d hsig' hJ' hN hQ hs hq hX hY B δ hprof hw htN hi p hsuffix
  have := hprof.probability
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hp := policyDepth_interior (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq
    (policyBlocks_nonempty hq htN hw)
  have hap : d.a ≤ p := by dsimp [p]; omega
  have hpt : p ≤ d.t := by dsimp [p]; omega
  let e : PositiveDistanceData := {d with t := p,i := d.i+1}
  let E : Set (ℝ × ℝ) := {z | |z.1-z.2| ≤ 100/(2:ℝ)^p}
  let F : ℝ≥0∞ := ((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
    (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
      2000*(d.lam+sig)+12*d.lam))
  have hnorm := h₁ d hsig' hJ' ((le_max_left _ _).trans hN) hQ hs hq B δ hprof hw htN hi hsuffix
  have hdom := h₂ d hsig' hJ' ((le_max_right _ _).trans hN) hQ hs hq hX hY p hap hpt htN
  have hbin := finite_bin_collision_comparison (d.suffixRetained p)
    (fun c => (d.suffixData c).distance) d.suffixFullDistance d.width E F hnorm
    (fun c hc b hb hcommon => d.shared_bin_full_coarse_collision hQ hpt hc hb hcommon)
  rw [← d.distance_split_retained hside hap hX hY] at hbin
  have he : (e.distance.prod e.distance) E = e.normalization⁻¹*e.coincidence := by
    have hwidth : 100/(2:ℝ)^p = 100*e.width := by
      simp only [e,PositiveDistanceData.width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_natCast,div_eq_mul_inv]
    change (e.distance.prod e.distance) {z | |z.1-z.2| ≤ 100/(2:ℝ)^p} = _
    rw [hwidth,e.distance_collision,e.unnormalized_coincidence]
  calc
    _ ≤ F*((∑ c ∈ d.suffixRetained p, d.suffixFullDistance c).prod
        (∑ c ∈ d.suffixRetained p, d.suffixFullDistance c)) E := hbin
    _ ≤ F*(e.distance.prod e.distance) E := mul_le_mul' le_rfl (Measure.prod_mono hdom hdom E)
    _ = _ := by rw [he]; dsimp only [F,e]; ring

end PlanarFalconer

end OAI
