import OAI.Analysis.CircleDomains.Topology.MeanIndexCircle
import OAI.Analysis.CircleDomains.Transfer.PeriodicFilling

namespace OAI

/-! The actual perturbed mean retains the integer winding of a lifted
circuit. This is the period used by the finite filling and Stokes steps. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_mean_period_circuit
    {X : Type*} [TopologicalSpace X]
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : X → ℂ) (c : C(unitInterval, X))
    (hc : c 1 = c 0) (L : C(unitInterval, ClosedUpperHalfPlane))
    (hproj : ∀ t, diskRayProjection (L t).val = F (c t))
    (hmiss : ∀ t, ∀ᵐ γ : K ∂(η : Measure K), F (c t) ∉ range γ.val)
    (R : X → ℝ) (hR : Continuous (R ∘ c))
    (k : ℤ) (hperiod : L 1 = (L 0).translate k) :
    ∃ (v : C(unitInterval, ℝ)) (γ : C(unitInterval, UnitAddCircle)),
      (∀ t, v t = meanGeometricIndex hsch K hKS η (L t) + R (c t)) ∧
      (∀ t, γ t = diskMeanCircle hsch K hKS η (F (c t)) + (R (c t) : UnitAddCircle)) ∧
      γ 1 = γ 0 ∧ v 1 - v 0 = (k : ℝ) ∧
      FiniteTransfer.circlePathIncrement γ = (k : ℝ) := by
  have hmean : Continuous (fun t => meanGeometricIndex hsch K hKS η (L t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L t)
      (by simpa only [hproj t] using hmiss t)).comp L.continuous.continuousAt
  let v : C(unitInterval, ℝ) := ⟨fun t => meanGeometricIndex hsch K hKS η (L t) + R (c t),
    hmean.add hR⟩
  let γ : C(unitInterval, UnitAddCircle) :=
    ⟨fun t => (v t : UnitAddCircle), (AddCircle.continuous_mk' (1 : ℝ)).comp v.continuous⟩
  have hinc : v 1 - v 0 = (k : ℝ) := by
    change meanGeometricIndex hsch K hKS η (L 1) + R (c 1) -
      (meanGeometricIndex hsch K hKS η (L 0) + R (c 0)) = (k : ℝ)
    rw [hc, hperiod, meanGeometricIndex_translate hsch hsep K hK hKS η]
    ring
  refine ⟨v, γ, fun _ => rfl, ?_, ?_, hinc, ?_⟩
  · intro t
    change ((meanGeometricIndex hsch K hKS η (L t) + R (c t) : ℝ) : UnitAddCircle) = _
    rw [AddCircle.coe_add]
    have hm := (diskMeanCircle_projection hsch hsep K hK hKS η (L t)).symm
    rw [hproj t] at hm
    rw [hm]
  · change (v 1 : UnitAddCircle) = (v 0 : UnitAddCircle)
    apply (FiniteTransfer.addCircle_eq_iff_exists_int 1 _ _).mpr
    exact ⟨k, by simpa only [mul_one, add_comm] using (sub_eq_iff_eq_add.mp hinc)⟩
  · rw [FiniteTransfer.circlePathIncrement_eq_lift γ v (fun _ => rfl)]
    exact hinc

end CircleDomainRigidity

end

end OAI
