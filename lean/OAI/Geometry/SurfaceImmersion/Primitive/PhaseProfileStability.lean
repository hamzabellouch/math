import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.CompactCompositionBound

namespace OAI

/-! Stability of the five derivative profiles after a fixed nonlinear change
of coordinates, with a constant independent of the fast scale. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates WeightedEstimates PeriodicExpansion

lemma primitiveJetProfile_bound_on {f : JetPolynomial.Base → Euclidean}
    {S : Set JetPolynomial.Base} (hS : IsOpen S)
    (hf : ContDiff ℝ ∞ f) {C z : ℝ} (hC : 0 ≤ C) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hb : WeightedBound S 1 2 C f) {p : JetPolynomial.Base} (hp : p ∈ S) :
    ‖primitiveJetProfile f z p‖ ≤ C := by
  have hw (vs : List (Fin 2)) (hlen : vs.length ≤ 2) :
      ‖iteratedDirectional (vs.map coordinateVector) f p‖ ≤ C := by
    have hv : ∀ v ∈ vs.map coordinateVector, ‖v‖ ≤ 1 := by
      intro v hv
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hv
      exact norm_coordinateVector_le j
    have hb' : WeightedBound S 1 (0+(vs.map coordinateVector).length) C f :=
      hb.mono_order (by simpa only [zero_add,List.length_map] using hlen)
    have hh := hb'.iteratedDirectional hS zero_lt_one hC hf.contDiffOn
      (vs.map coordinateVector) hv 0
    simpa only [one_pow,div_one] using hh.norm_le hp
  have hx : ‖directionalMap f (coordinateVector 0) p‖ ≤ C := by
    dsimp only [directionalMap]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [0] (by decide)
  have hy : ‖directionalMap f (coordinateVector 1) p‖ ≤ C := by
    dsimp only [directionalMap]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [1] (by decide)
  have hdir (v : JetPolynomial.Base) : directionalMap f v = (fun q => fderiv ℝ f q v) := rfl
  have hxx : ‖directionalMap (directionalMap f (coordinateVector 0)) (coordinateVector 0) p‖ ≤ C := by
    dsimp only [directionalMap]
    rw [hdir]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [0,0] (by decide)
  have hxy : ‖directionalMap (directionalMap f (coordinateVector 0)) (coordinateVector 1) p‖ ≤ C := by
    dsimp only [directionalMap]
    rw [hdir]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [1,0] (by decide)
  have hyy : ‖directionalMap (directionalMap f (coordinateVector 1)) (coordinateVector 1) p‖ ≤ C := by
    dsimp only [directionalMap]
    rw [hdir]
    simpa only [List.map_cons,List.map_nil,iteratedDirectional,directionalMap] using hw [1,1] (by decide)
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hyy
  · exact hxy
  · change ‖z • directionalMap (directionalMap f (coordinateVector 0)) (coordinateVector 0) p‖ ≤ C
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
    exact (mul_le_mul_of_nonneg_left hxx hz).trans (mul_le_of_le_one_left hC hz1)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_profile_correction_bound (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ∀ C z : ℝ, 0 ≤ C → 0 ≤ z → z ≤ 1 → A.WeightedBound 1 2 C (G-F) →
      ∀ p ∈ S,
      ‖primitiveJetProfile (A.vectorChartRead i G ∘ T) z p-
        primitiveJetProfile (A.vectorChartRead i F ∘ T) z p‖ ≤ D*C := by
  obtain ⟨D₀,hD₀,hd⟩ := A.vectorChartRead_bound (V := Space) i 2
  obtain ⟨D₁,hD₁,hcomp⟩ := compact_composition_bound (E := Space) hT hS hSc 2
  refine ⟨D₁*D₀,mul_nonneg (by linarith) hD₀,?_⟩
  intro F G hF hG C z hC hz hz1 hdiff p hp
  have hb := hd (G-F) 1 C zero_lt_one le_rfl hC (hG.sub hF) hdiff
  have hc := hcomp (A.vectorChartRead i (G-F)) (D₀*C)
    (mul_nonneg hD₀ hC) (A.vectorChartRead_smooth i (hG.sub hF)) hb
  have hid : A.vectorChartRead i (G-F) ∘ T =
      (A.vectorChartRead i G ∘ T)-(A.vectorChartRead i F ∘ T) := by
    rw [A.vectorChartRead_sub]
    rfl
  rw [hid] at hc
  rw [← primitiveJetProfile_sub ((A.vectorChartRead_smooth i hG).comp hT)
    ((A.vectorChartRead_smooth i hF).comp hT)]
  have hh := primitiveJetProfile_bound_on hS
    (((A.vectorChartRead_smooth i hG).comp hT).sub ((A.vectorChartRead_smooth i hF).comp hT))
    (mul_nonneg (by linarith : 0 ≤ D₁) (mul_nonneg hD₀ hC)) hz hz1 hc hp
  change ‖primitiveJetProfile ((A.vectorChartRead i G ∘ T)-(A.vectorChartRead i F ∘ T)) z p‖ ≤
    D₁*(D₀*C) at hh
  exact hh.trans_eq (mul_assoc D₁ D₀ C).symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
