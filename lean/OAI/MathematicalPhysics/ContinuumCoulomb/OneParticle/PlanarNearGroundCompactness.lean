import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarCompactnessEstimates

namespace OAI

/-! Compactness of normalized near-ground sequences for the actual well.
The positive free form makes compactness of the potential multiplier enough. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instPlanarNearGroundCompactnessMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarNearGroundCompactnessBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarNearGroundCompactnessMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

theorem nearGround_cauchy_of_potential_cauchy (u : ℕ → Sobolev)
    (hm : ∀ n, ‖(u n).val.1‖ ≤ 1)
    (hs : Tendsto (fun n => shiftedForm (u n).val) atTop (𝓝 0))
    (hw : CauchySeq (fun n => wellMultiplier (u n).val.1)) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε^2/16 := by positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hs (ε^2/16) hδ
  obtain ⟨M,hM⟩ := Metric.cauchySeq_iff.mp hw (ε^2/16) hδ
  refine ⟨max N M,fun n hn m hm' => ?_⟩
  have hn' : shiftedForm (u n).val < ε^2/16 := by
    have h := hN n ((le_max_left _ _).trans hn)
    simpa only [dist_zero_right,Real.norm_eq_abs,
      abs_of_nonneg (shiftedForm_nonnegative (u n))] using h
  have hm'' : shiftedForm (u m).val < ε^2/16 := by
    have h := hN m ((le_max_left _ _).trans hm')
    simpa only [dist_zero_right,Real.norm_eq_abs,
      abs_of_nonneg (shiftedForm_nonnegative (u m))] using h
  have hd := hM n ((le_max_right _ _).trans hn) m ((le_max_right _ _).trans hm')
  have he := nearGround_distance_bound (u n) (u m) (hm n) (hm m)
  nlinarith [(dist_nonneg : 0 ≤ dist (u n) (u m))]

theorem nearGround_subsequence (u : ℕ → Sobolev)
    (hm : ∀ n, ‖(u n).val.1‖ ≤ 1) (hb : ∀ n, shiftedForm (u n).val ≤ 1)
    (hs : Tendsto (fun n => shiftedForm (u n).val) atTop (𝓝 0)) :
    ∃ v : Sobolev, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 v) := by
  let W := wellMultiplier.comp (h1ToL2 (μ := volume) (E := PlanarPosition))
  obtain ⟨K,hK,hWK⟩ := wellMultiplier_compact.image_closedBall_subset_compact
    (3+2*‖wellMultiplier‖)
  have hmem (n : ℕ) : W (u n) ∈ K := by
    apply hWK
    refine ⟨u n,?_,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact nearGround_norm_bound (u n) (hm n) (hb n)
  obtain ⟨w,_hw,φ,hφ,hlim⟩ := hK.tendsto_subseq hmem
  have hW : CauchySeq (fun n => wellMultiplier (u (φ n)).val.1) := hlim.cauchySeq
  have hc := nearGround_cauchy_of_potential_cauchy (u ∘ φ)
    (fun n => hm (φ n)) (hs.comp hφ.tendsto_atTop) hW
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨v,φ,hφ,hv⟩

end ContinuumCoulomb.PlanarSobolev

end

end OAI
