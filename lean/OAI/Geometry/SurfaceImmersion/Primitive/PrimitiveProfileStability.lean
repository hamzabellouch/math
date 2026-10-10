import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveProfiles
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedActualJets
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds

namespace OAI

/-! The five primitive derivative components are stable under a global C2
correction.  Their bound is uniform in the fast scale between zero and one. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates WeightedEstimates PeriodicExpansion

lemma primitiveJetProfile_bound {f : JetPolynomial.Base → Euclidean}
    (hf : ContDiff ℝ ∞ f) {C z : ℝ} (hC : 0 ≤ C) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hb : WeightedBound univ 1 2 C f) (p : JetPolynomial.Base) :
    ‖primitiveJetProfile f z p‖ ≤ C := by
  have hw (vs : List (Fin 2)) (hlen : vs.length ≤ 2) :
      ‖iteratedDirectional (vs.map coordinateVector) f p‖ ≤ C := by
    have hv : ∀ v ∈ vs.map coordinateVector, ‖v‖ ≤ 1 := by
      intro v hv
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hv
      exact norm_coordinateVector_le j
    have hb' : WeightedBound univ 1 (0+(vs.map coordinateVector).length) C f :=
      hb.mono_order (by simpa only [zero_add,List.length_map] using hlen)
    have hh := hb'.iteratedDirectional isOpen_univ zero_lt_one hC hf.contDiffOn
      (vs.map coordinateVector) hv 0
    simpa only [one_pow,div_one] using hh.norm_le (mem_univ p)
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

private lemma directional_sub {f g : JetPolynomial.Base → Euclidean}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v : JetPolynomial.Base) :
    directionalMap (f-g) v = directionalMap f v-directionalMap g v := by
  funext p
  change (fderiv ℝ (fun q => f q-g q) p) v = (fderiv ℝ f p) v-(fderiv ℝ g p) v
  rw [fderiv_fun_sub (hf.differentiable (by simp) p) (hg.differentiable (by simp) p)]
  rfl

lemma primitiveJetProfile_sub {f g : JetPolynomial.Base → Euclidean}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : ℝ) (p : JetPolynomial.Base) :
    primitiveJetProfile (f-g) z p = primitiveJetProfile f z p-primitiveJetProfile g z p := by
  have hsecond (v w : JetPolynomial.Base) :
      directionalMap (directionalMap (f-g) v) w =
        directionalMap (directionalMap f v) w-directionalMap (directionalMap g v) w := by
    rw [directional_sub hf hg,directional_sub (directionalMap_smooth hf v) (directionalMap_smooth hg v)]
  unfold primitiveJetProfile
  simp only [hsecond]
  simp only [directional_sub hf hg]
  ext i
  fin_cases i <;> simp [smul_sub]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorChartRead_sub (i : A.centers) (F G : M → Space) :
    A.vectorChartRead i (G-F) = A.vectorChartRead i G-A.vectorChartRead i F := by
  funext x
  unfold vectorChartRead localize
  by_cases hx : x ∈ (chart (i : M)).target <;> simp [hx,smul_sub]

theorem primitive_profile_correction_bound (i : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ∀ C z : ℝ, 0 ≤ C → 0 ≤ z → z ≤ 1 → A.WeightedBound 1 2 C (G-F) →
      ∀ p : JetPolynomial.Base,
      ‖primitiveJetProfile (A.vectorChartRead i G) z p-
        primitiveJetProfile (A.vectorChartRead i F) z p‖ ≤ D*C := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := Space) i 2
  refine ⟨D,hD,?_⟩
  intro F G hF hG C z hC hz hz1 hdiff p
  have hb := hd (G-F) 1 C zero_lt_one le_rfl hC (hG.sub hF) hdiff
  rw [A.vectorChartRead_sub] at hb
  rw [← primitiveJetProfile_sub (A.vectorChartRead_smooth i hG) (A.vectorChartRead_smooth i hF)]
  exact primitiveJetProfile_bound ((A.vectorChartRead_smooth i hG).sub
    (A.vectorChartRead_smooth i hF)) (mul_nonneg hD hC) hz hz1 hb p

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
