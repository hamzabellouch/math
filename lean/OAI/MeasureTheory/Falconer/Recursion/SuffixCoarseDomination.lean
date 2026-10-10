import OAI.MeasureTheory.Falconer.Recursion.SuffixRetainedPairs
import OAI.MeasureTheory.Falconer.Recursion.SuffixGoodTransport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem suffix_full_pair_le_coarse (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (hgood : ∀ c ∈ d.suffixRetained p, ∀ x ∈ (d.Q.descendant c.1).carrier,
      ∀ y ∈ (d.Q.descendant c.2).carrier,
      (x,y) ∈ ({d with t := p,i := d.i+1} : PositiveDistanceData).good) :
    (∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair) ≤
      ({d with t := p,i := d.i+1} : PositiveDistanceData).pair := by
  classical
  let e : PositiveDistanceData := {d with t := p,i := d.i+1}
  have hle : (∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair) ≤ d.cellPair := by
    rw [d.cellPair_split_suffix hQ hap hX hY]
    intro s
    simp only [Measure.finsetSum_apply]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have he : (∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair).restrict e.good =
      ∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair := by
    rw [finite_measure_restrict_sum]
    apply Finset.sum_congr rfl
    intro c hc
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [(d.suffixData c).ae_cellPair_mem] with z hz
    exact hgood c hc z.1 hz.1 z.2 hz.2
  rw [← he]
  exact Measure.restrict_mono_measure hle e.good

theorem suffix_full_distance_le_coarse (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (hgood : ∀ c ∈ d.suffixRetained p, ∀ x ∈ (d.Q.descendant c.1).carrier,
      ∀ y ∈ (d.Q.descendant c.2).carrier,
      (x,y) ∈ ({d with t := p,i := d.i+1} : PositiveDistanceData).good) :
    (∑ c ∈ d.suffixRetained p, d.suffixFullDistance c) ≤
      ({d with t := p,i := d.i+1} : PositiveDistanceData).distance := by
  have hh := Measure.map_mono (d.suffix_full_pair_le_coarse hQ hap hX hY hgood)
    (continuous_fst.dist continuous_snd).measurable
  rw [Measure.map_finset_sum (by fun_prop)] at hh
  exact hh

end PositiveDistanceData

theorem uniform_suffix_coarse_domination {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
      d.sig = sig → d.J = J → N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated →
      0 < d.q → d.X.length = d.a → d.Y.length = d.a →
      ∀ p : ℕ, d.a ≤ p → p ≤ d.t → d.t ≤ d.N →
      (∑ c ∈ d.suffixRetained p, d.suffixFullDistance c) ≤
        ({d with t := p,i := d.i+1} : PositiveDistanceData).distance := by
  obtain ⟨N₀,hN₀⟩ := uniform_suffix_good_transport hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hsig' hJ' hN hQ hs hq hX hY p hap hpt htN
  apply d.suffix_full_distance_le_coarse (by rw [hQ]; norm_num) hap hX hY
  intro c hc x' hx' y' hy'
  obtain ⟨hP,hC,hPX,hCY,x,hx,y,hy,hg⟩ := d.suffix_retained_spec hc
  exact hN₀ d hsig' hJ' hN hQ hs hq p hap hpt htN c.1 c.2 hP hC hPX hCY x hx y hy hg x' hx' y' hy'

end PlanarFalconer

end OAI
