import OAI.Analysis.CircleDomains.Transfer.RoundOuterCore
import OAI.Analysis.CircleDomains.Transfer.RealEndCorrespondence

namespace OAI

/-!
# Collapse from a selected cover by local real plateaus

Arbitrarily small anchored one-plateaus force each target component with
an unmarked source address to be a singleton, by the line-payment estimate.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (L : AssignedRealModelLimit M)

/-- Original energy and original band norm of one real coordinate. -/
def CountableRealCoordinates.barrierNorm (d : CountableRealCoordinates G π σ) (l : ℕ) : ℝ :=
  Real.sqrt (∫ x in realChartDomain G,
    gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
  Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2)

theorem RealTargetEnd.eq_singleton_of_plateau_cover
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (V : ℕ → ℕ → Set Sphere) (hV : ∀ k l, IsOpen (V k l))
    (hone : ∀ k l, ∀ x ∈ V k l ∩ d.source, d.coordinate l x = 1)
    (hzero : ∀ k l, (V k l).Nonempty → ∀ z ∈ sphere (0 : ℂ) (2 * M.radius),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    (hnorm : ∀ k l, (V k l).Nonempty → d.barrierNorm l < modelError k)
    {q : Sphere} (hq : q ∈ Gᶜ) (E : RealTargetEnd L q)
    (hcover : ∀ k, ∃ l, π q ∈ V k l) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  apply E.target_eq_singleton_of_small_anchored_plateaus hsard hsch harea
    hG hconn hε hπ hr hq M.outerCore 0 (M.component_inside_outerCore q)
  intro δ hδ
  obtain ⟨k, hk⟩ := ((tendsto_order.1 modelError_tendsto).2 δ hδ).exists
  obtain ⟨l, hl⟩ := hcover k
  refine ⟨l, V k l, hV k l, hl, hone k l, ?_, (hnorm k l ⟨π q, hl⟩).trans hk⟩
  intro z hz
  rw [M.outerCore_interior, frontier_ball _ (ne_of_gt (mul_pos (by norm_num) M.radius_pos))] at hz
  exact hzero k l ⟨π q, hl⟩ z hz

/-- All non-singleton limit components carry a marked source address,
and each contains its corresponding round limiting disk. -/
theorem AssignedRealModelLimit.singleton_or_marked_disk
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (V : ℕ → ℕ → Set Sphere) (hV : ∀ k l, IsOpen (V k l))
    (hone : ∀ k l, ∀ x ∈ V k l ∩ d.source, d.coordinate l x = 1)
    (hzero : ∀ k l, (V k l).Nonempty → ∀ z ∈ sphere (0 : ℂ) (2 * M.radius),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    (hnorm : ∀ k l, (V k l).Nonempty → d.barrierNorm l < modelError k)
    (hcover : ∀ b ∈ (π '' Gᶜ) \ range σ, ∀ k, ∃ l, b ∈ V k l)
    {p : Sphere} (hp : p ∈ (extendAtInfinity L.function '' G)ᶜ) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ p = {p} ∨
      ∃ s, ((↑) : ℂ → Sphere) '' closedBall (L.center s) (L.radius s) ⊆
        connectedComponentIn (extendAtInfinity L.function '' G)ᶜ p := by
  classical
  obtain ⟨q, hq, E, hE⟩ := L.exists_source_end hG hp
  by_cases hm : π q ∈ range σ
  · obtain ⟨s, hs⟩ := hm
    exact Or.inr ⟨s, hE ▸ E.marked_disk_subset hr hq hs.symm⟩
  · left
    have hc := RealTargetEnd.eq_singleton_of_plateau_cover L hsard hsch harea hG hconn hε
      hπ hr V hV hone hzero hnorm hq E (fun k => hcover (π q) ⟨⟨q, hq, rfl⟩, hm⟩ k)
    simpa only [hE] using hc

end CircleDomainRigidity.FiniteTransfer

end

end OAI
