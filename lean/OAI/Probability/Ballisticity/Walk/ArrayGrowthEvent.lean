import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryArrayLaw
import OAI.Probability.Ballisticity.Stationary.ArrayDust

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma stationary_ae_integer_family {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (P : ℤ → Ω → Prop) (hp : ∀ i, MeasurableSet {ω | P i ω})
    (hs : ∀ i, ∀ᵐ ω ∂μ, P i (T ω) ↔ P (i+1) ω)
    (h0 : ∀ᵐ ω ∂μ, P 0 ω) : ∀ᵐ ω ∂μ, ∀ i, P i ω := by
  apply ae_all_iff.mpr
  have hb (i : ℤ) : (∀ᵐ ω ∂μ, P i ω) ↔ ∀ᵐ ω ∂μ, P (i+1) ω := by
    have he : (∀ᵐ ω ∂μ, P i (T ω)) ↔ ∀ᵐ ω ∂μ, P (i+1) ω := eventually_congr (hs i)
    rw [←ae_map_iff hT.measurable.aemeasurable (hp i),hT.map_eq] at he
    exact he
  intro i
  induction i using Int.induction_on with
  | zero => exact h0
  | succ n ih => exact (hb n).mp ih
  | pred n ih =>
    apply (hb (-(n:ℤ)-1)).mpr
    simpa only [sub_add_cancel] using ih

structure ArrayGrowthSector {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e)) where
  event : Set (ActualEpisodeArray e)
  measurable_event : MeasurableSet event
  positive_event : 0<μ event
  invariant : ∀ᵐ Y ∂μ, StationaryCompact.shift Y∈event ↔ Y∈event
  symmetric : ∀ σ, ∀ᵐ Y ∂μ, arrayPerm e σ Y∈event ↔ Y∈event
  ζ : ℝ
  positive_ζ : 0<ζ
  sequence : ℕ → ℕ
  strictMono : StrictMono sequence
  growth : ∀ᵐ Y ∂μ, Y∈event → ∀ᶠ k in atTop,
    ζ*(sequence k:ℝ)<(arrayWindowCost e 0 (sequence k) Y).toReal
  no_dust : ∀ᵐ Y ∂μ, Y∈event → ∀ i a, ¬arrayDust e i a Y

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

theorem growth_sector (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    Nonempty (ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) := by
  let μ := (L.law : Measure (ActualEpisodeArray e))
  obtain ⟨g,hgm,hgb,hgT,ζ,hζ,hE,ns,hns,hlim,hgrowth⟩ := stationary_positive_growth μ
    L.preserving (arrayRealCost e) (arrayRealCost_measurable e) (arrayRealCost_nonneg e)
      L.integrable_cost L.positive_cost
  let E := {Y | ζ<g Y}
  have hmE : MeasurableSet E := measurableSet_lt measurable_const hgm
  have heT : ∀ᵐ Y ∂μ, StationaryCompact.shift Y∈E ↔ Y∈E := by
    filter_upwards [hgT] with Y hY
    change ζ<g (StationaryCompact.shift Y) ↔ ζ<g Y
    rw [hY]
  have heP (σ : Equiv.Perm ℕ) : ∀ᵐ Y ∂μ, arrayPerm e σ Y∈E ↔ Y∈E := by
    filter_upwards [array_growth_symmetry e μ g ns hlim L.symmetric σ] with Y hY
    change ζ<g (arrayPerm e σ Y) ↔ ζ<g Y
    rw [hY]
  have hc : ∀ᵐ Y ∂μ, ∀ j, (Y.1 j).2.2≠⊤ := L.finite_marks.mono fun Y hY j => (hY j).2.2.2.ne
  have hd : ∀ᵐ Y ∂μ, Y∈E → ∀ ε : ℝ, 0<ε → ∃ m,
      (expNeg (arrayWindowCost e 0 m Y)).toReal<ε := by
    filter_upwards [hc,hgrowth] with Y hY hg hy
    exact array_cost_decay_of_growth e Y hY ζ hζ ns hns (hg hy)
  have hn0 := array_no_dust_on_cost_decay e ν hue htrans μ L.consistent L.zero_sampling
    L.entropy_finite (L.finite_marks.mono fun Y hY j => (hY j).2.1) L.survival L.symmetric 0 E hmE heP hd
  have hnd : ∀ᵐ Y ∂μ, Y∈E → ∀ i a, ¬arrayDust e i a Y := by
    have hh := stationary_ae_integer_family μ L.preserving (fun i Y => Y∈E → ∀ a, ¬arrayDust e i a Y)
      (fun i => hmE.imp (by
        simpa only [Set.ofPred_forall, Set.compl_ofPred] using MeasurableSet.iInter fun a => (arrayDust_measurable e i a).compl))
      (fun i => heT.mono fun Y hY => by
        rw [hY]
        rfl) hn0
    filter_upwards [hh] with Y hY hy i
    exact hY i hy
  refine ⟨⟨E,hmE,hE,heT,heP,ζ,hζ,ns,hns,?_,hnd⟩⟩
  filter_upwards [hc,hgrowth] with Y hY hg hy
  simpa only [arrayWindowCost_toReal e Y hY] using hg hy

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
