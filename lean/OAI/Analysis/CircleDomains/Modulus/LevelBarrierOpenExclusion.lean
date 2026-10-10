import OAI.Analysis.CircleDomains.Selection.LocalFixedRealExclusion
import OAI.Analysis.CircleDomains.Modulus.LevelBarrierLocalizedNorm

namespace OAI

/-! Apply the open real-barrier exclusion to the actual compatible barrier. Its compact
omitted source set is constructed as the inverse image of the closed quotient penalty. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleLevelBarrier
 theorem exists_open_exclusion
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hπG : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain → π (z : Sphere) ∈ base.quotientDomain)
    (hpre : π ⁻¹' base.quotientDomain ⊆ base.physicalDomain)
    (hinf : π OnePoint.infty ∈ base.anchor)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} {E : RealTargetEnd A q}
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    {previous : PriorLevelFamily base.physicalDomain π} {flags EStar : Set Sphere}
    {regions : ℕ → Set Sphere} {f : base.quotientDomain → Sphere} {W : Set Sphere}
    (R : CompatibleLevelBarrier base π previous flags EStar regions f W)
    (hregions : ∀ n, IsOpen (regions n)) (hqregions : ∀ n, π q ∈ regions n)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar)
    (hf : ∀ (z : ℂ) (hz : (z : Sphere) ∈ base.physicalDomain),
      f ⟨π (z : Sphere), hπG z hz⟩ = (A.function z : Sphere))
    (hW : ((↑) : ℂ → Sphere) '' closedBall T.center T.radius ⊆ W)
    (hsmall : R.controlledSize.toReal < T.barrierThreshold) :
    ∃ V : Set C(FiniteSource base.physicalDomain, ℂ), IsOpen V ∧
      finiteSourceMap A.function (A.plane_open_embedding hG).1 ∈ V ∧
      ∀ {S' : Type*} {π' : Sphere → Sphere} {σ' : S' → Sphere}
        {d' : CountableRealCoordinates base.physicalDomain π' σ'}
        {O' : ℕ → S' → Set Sphere} {ε' : ℕ → ℝ}
        (M' : RealModelExhaustion d' O' ε') (A' : AssignedRealModelLimit M') (l : ℕ),
        Tendsto ε' atTop (𝓝 0) → 3 * M'.radius ≤ T.boundRadius →
        d'.physical l = R.coordinate.physical →
        Real.sqrt (∑' s, (d'.upper l s - d'.lower l s) ^ 2) ≤
          (countingSquareNorm R.weight).toReal →
        finiteSourceMap A'.function (A'.plane_open_embedding hG).1 ∉ V := by
  let P : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' closure R.penalty)
  have hP : IsCompact P := isCompact_finite_preimage
    (isClosed_closure.preimage hπ) (fun hz => Set.disjoint_left.mp R.penalty_disjoint hinf hz)
  have hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain := by
    intro z hz
    exact hpre (R.penalty_inside hz)
  have hPW : Disjoint (A.function '' P) (closedBall T.center T.radius) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    have hn := R.penalty_avoids ⟨π (x : Sphere), R.penalty_inside hx⟩ hx
    rw [hf x (hPG hx)] at hn
    exact hn (hW (mem_image_of_mem _ hz))
  have hPcontains :
      (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' R.penalty ⊆
        Complex.equivRealProdCLM '' P := by
    intro x hx
    exact ⟨Complex.equivRealProdCLM.symm x, subset_closure hx,
      Complex.equivRealProdCLM.apply_symm_apply x⟩
  have hnorm := R.localized_norm_le_controlledSize hPcontains
  apply T.exists_open_real_barrier_exclusion hsch harea hG hconn hπ hr hq
    (hregions R.level) (hqregions R.level) R.coordinate.physical
    (fun z hz hzu => (R.coordinate.pullback z hz).trans
      (R.one _ ⟨subset_closure hzu, hπG z hz⟩))
    (fun z hz => (R.coordinate.pullback z (T.source_inside hz)).trans
      (R.zero _ (hzero z hz))) hP hPG hPW ENNReal.toReal_nonneg
    (hnorm.trans_lt hsmall)

end CompatibleLevelBarrier
end CircleDomainRigidity

end

end OAI
