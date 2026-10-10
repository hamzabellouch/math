import OAI.Analysis.CircleDomains.Topology.RelativelyClosedGates
import OAI.Analysis.CircleDomains.Modulus.NormalizedLimitEquivalence

namespace OAI

/-! The actual normalized map on the quotient domain. Its finite physical
formula is required only over the bounded target gate, which misses infinity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 def quotientNormalizedMap {G U : Set Sphere} (e : G ≃ₜ U) (F : ℂ → ℂ) : U → Sphere :=
  fun x => extendAtInfinity F (e.symm x).val

 theorem quotientNormalizedMap_continuous {G U : Set Sphere} (e : G ≃ₜ U) (F : ℂ → ℂ)
    (hF : IsConformalOn (extendAtInfinity F) G) : Continuous (quotientNormalizedMap e F) := by
  have hc : Continuous (fun x : G => extendAtInfinity F x.val) :=
    continuousOn_iff_continuous_domRestrict.mp (fun x hx => (hF x hx).1.continuousWithinAt)
  exact hc.comp e.symm.continuous

 theorem quotientNormalizedMap_finite_gate {G U : Set Sphere} (e : G ≃ₜ U) (F : ℂ → ℂ)
    (y₀ : Sphere) {W : Set Sphere} (hW : OnePoint.infty ∉ W) :
    ∀ x : U, quotientNormalizedMap e F x ∈ W →
      quotientNormalizedMap e F x =
        (F (finiteCoord (physicalValue e y₀ x.val)) : Sphere) := by
  intro x hx
  have hphys : physicalValue e y₀ x.val = (e.symm x).val := by
    simp only [physicalValue, dite_eq_left x.property]
  rw [hphys]
  change extendAtInfinity F (e.symm x).val = _
  cases hy : (e.symm x).val using OnePoint.rec with
  | infty =>
    apply (hW ?_).elim
    simpa only [quotientNormalizedMap, hy, extendAtInfinity_infty] using hx
  | coe z => simp only [extendAtInfinity_coe, finiteCoord_coe]

 theorem quotientNormalizedMap_physical {G U : Set Sphere} (e : G ≃ₜ U)
    (π : Sphere → Sphere) (he : ∀ x : G, (e x).val = π x.val) (F : ℂ → ℂ)
    (z : ℂ) (hz : (z : Sphere) ∈ G) :
    quotientNormalizedMap e F ⟨π (z : Sphere), (he ⟨_, hz⟩) ▸ (e ⟨_, hz⟩).property⟩ =
      (F z : Sphere) := by
  have h : (⟨π (z : Sphere), (he ⟨_, hz⟩) ▸ (e ⟨_, hz⟩).property⟩ : U) = e ⟨_, hz⟩ :=
    Subtype.ext (he ⟨(z : Sphere), hz⟩).symm
  simp only [quotientNormalizedMap, h, e.symm_apply_apply, extendAtInfinity_coe]

 theorem exists_uniform_infDist_gap {K : Set ℂ} (hK : IsCompact K) (hKn : K.Nonempty)
    {D : Set ℂ} (hD : IsClosed D) (hDn : D.Nonempty) (hKD : Disjoint K D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ infDist z D := by
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hKn (continuous_infDist_pt D).continuousOn
  exact ⟨infDist z D, (hD.notMem_iff_infDist_pos hDn).mp
    (fun hd => disjoint_left.mp hKD hz hd), hmin⟩

end CircleDomainRigidity

end

end OAI
