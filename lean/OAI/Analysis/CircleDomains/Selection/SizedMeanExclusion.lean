import OAI.Analysis.CircleDomains.Selection.MeanExclusionRadius
import OAI.Analysis.CircleDomains.Transfer.SelectedMixedModels

namespace OAI

/-! Record the exterior model radius in the same second countable test
space. An open radius interval retains the quantitative Stokes exclusion
under subsequent common-model selection. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 def sizedNeighborhood (B : ℝ) : Set (MapDiskData G × ℝ) :=
  W.neighborhood ×ˢ Ioo B (R / 5)

 theorem isOpen_sizedNeighborhood (B : ℝ) : IsOpen (W.sizedNeighborhood B) :=
  W.isOpen_neighborhood.prod isOpen_Ioo

 theorem mem_sizedNeighborhood {B ρ : ℝ} (hB : B < ρ) (hρ : 5 * ρ < R) :
    ((finiteSourceMap F₀ hF₀, c, r), ρ) ∈ W.sizedNeighborhood B :=
  ⟨W.member, hB, by linarith⟩

 theorem not_mem_sizedNeighborhood
    (hgreen : UnorientedFiniteCircleGreenFormula) (hsch : PlanarSchoenflies)
    (harea : ExteriorCoefficientAreaTheorem)
    {J : Type*} [LinearOrder J] {d : CountableRealCoordinates G π σ}
    {data : J → MaskedCoordinateData G d.source π σ} {retained : ℕ → J} {ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ}
    (L : AssignedMixedModelLimit M)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hU : d.source = U) (j : J) (hN : HEq (data j) N)
    (B : ℝ) (hbound : ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ ≤ 4 * B) :
    ((finiteSourceMap L.function L.continuousOn, L.center (data j).singular,
      (⟨L.radius (data j).singular, (L.bounds _).2.1⟩ : ℝ≥0)), M.real.radius) ∉
        W.sizedNeighborhood B := by
  intro hp
  apply W.not_mem_of_radius_le hgreen hsch harea L hG hinf hπ hclosed hU j hN
    (by have h := hp.2.2; linarith) (fun z hz => (hbound z hz).trans (by have h := hp.2.1; linarith))
  exact hp.1

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
