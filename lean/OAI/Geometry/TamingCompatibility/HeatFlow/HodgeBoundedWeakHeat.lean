import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatIdentification
import OAI.Geometry.TamingCompatibility.Hodge.HodgeWeakCompact

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma hodgeResolvent_laplacian_core (a : PreL2 A J α hs ht true) :
    hodgeResolvent A J α hs ht 1
      (smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)) =
    smoothL2 A J α hs ht true a -
      hodgeResolvent A J α hs ht 1 (smoothL2 A J α hs ht true a) := by
  have hi := hodgeResolvent_differential_inverse A J α hs ht 1 zero_lt_one a
  simp only [one_pow,one_smul,map_add] at hi
  exact eq_sub_of_add_eq' hi

omit [T2Space X] in
lemma hodgeSpectralHeat_resolvent (t : ℝ) (f : L2 A J α hs ht true) :
    hodgeSpectralHeat A J α hs ht D hD t (hodgeResolvent A J α hs ht 1 f) =
      hodgeResolvent A J α hs ht 1 (hodgeSpectralHeat A J α hs ht D hD t f) := by
  have he := hodgeBoundedSpectralMultiplier_commutes A J α hs ht D hD
    (hodgeHeatMultiplier t) 1 zero_le_one
    (fun x => (abs_of_pos (hodgeHeatMultiplier_pos t x)).trans_le (hodgeHeatMultiplier_le_one t x))
    (hodgeResolvent A J α hs ht 1) (fun _ => rfl)
  exact congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f) he

include D hD in
lemma hodgeBoundedWeakHeat_eq_spectral (f : L2 A J α hs ht true)
    (U : ℝ → L2 A J α hs ht true) {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hU : ∀ t ∈ Icc 0 T, ‖U t‖ ≤ C)
    (hc : ∀ a : PreL2 A J α hs ht true,
      ContinuousOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T))
    (hzero : U 0 = f)
    (hweak : ∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
        (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) :
    ∀ t ∈ Icc 0 T, U t = hodgeSpectralHeat A J α hs ht D hD t f := by
  let R := hodgeResolvent A J α hs ht 1
  have hcont : ContinuousOn (fun t => R (U t)) (Icc 0 T) :=
    WeakHeat.compact_symmetric_continuousOn R
      (hodgeResolvent_compact A J α hs ht D hD 1 zero_lt_one)
      (hodgeResolvent_symmetric A J α hs ht 1)
      (smoothL2 A J α hs ht true) (smoothL2_dense A J α hs ht true)
      U (Icc 0 T) hC hU hc
  have he := hodgeWeakHeat_eq_spectral A J α hs ht D hD (R f)
    (fun t => R (U t)) hT hcont (congrArg R hzero) ?_
  · intro t ht'
    apply hodgeResolvent_injective A J α hs ht 1 zero_lt_one
    exact (he t ht').trans (hodgeSpectralHeat_resolvent A J α hs ht D hD t f)
  · intro a t ht'
    obtain ⟨b,hb,hDb⟩ := hodgeResolvent_smooth_core A J α hs ht D hD a
    have hh := hweak b t ht'
    rw [hDb,hb] at hh
    dsimp only [R]
    have hsym (u v : L2 A J α hs ht true) :
        ⟪hodgeResolvent A J α hs ht 1 u,v⟫ = ⟪u,hodgeResolvent A J α hs ht 1 v⟫ :=
      hodgeResolvent_symmetric A J α hs ht 1 u v
    simp_rw [hsym]
    rw [hodgeResolvent_laplacian_core A J α hs ht a]
    exact hh

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
