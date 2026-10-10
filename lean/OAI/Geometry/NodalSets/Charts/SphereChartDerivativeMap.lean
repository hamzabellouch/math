import OAI.Geometry.NodalSets.Charts.SphereL2LocalPullback
import OAI.Geometry.NodalSets.Elliptic.RealCompactL2
import OAI.Geometry.NodalSets.Elliptic.RealTransportDerivatives

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry
noncomputable section

abbrev SphereChartCubeL2 := Lp ℝ 2 (volume.restrict (realFinCube 4))

def sphereSmoothChartPartial (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : Yau.Jets.Coord → ℝ :=
  fun x ↦ Yau.coordPartial ((SphereEnergySmooth.toSmooth d u) ∘ sphereChartCoordMap p) x i

theorem sphereSmoothChartPartial_continuous (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : Continuous (sphereSmoothChartPartial d p i u) :=
  (Yau.real_coordPartial_smooth _
    (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) i).continuous

theorem sphereSmoothChartPartial_memLp (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : MemLp (sphereSmoothChartPartial d p i u) 2
      (volume.restrict (realFinCube 4)) :=
  Yau.real_continuous_memLp_compact (realFinCube_isCompact 4) _ (sphereSmoothChartPartial_continuous d p i u)

def sphereChartDerivativeLinear (d : SphereEnergyData) (p : Base) (i : Fin 4) :
    SphereEnergySmooth d →ₗ[ℝ] SphereChartCubeL2 where
  toFun u := (sphereSmoothChartPartial_memLp d p i u).toLp (sphereSmoothChartPartial d p i u)
  map_add' u v := by
    have he : sphereSmoothChartPartial d p i (u+v) =
        sphereSmoothChartPartial d p i u+sphereSmoothChartPartial d p i v := by
      funext x
      exact Yau.real_coordPartial_add _ _
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p)
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d v).property p) x i
    exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_add (sphereSmoothChartPartial_memLp d p i u) (sphereSmoothChartPartial_memLp d p i v))
  map_smul' a u := by
    have he : sphereSmoothChartPartial d p i (a • u) = a • sphereSmoothChartPartial d p i u := by
      funext x
      exact Yau.real_coordPartial_const_mul _
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) a x i
    exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_const_smul a (sphereSmoothChartPartial_memLp d p i u))

theorem sphereChartDerivativeLinear_norm_sq (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) :
    ‖sphereChartDerivativeLinear d p i u‖^2 = ∫ x in realFinCube 4, (sphereSmoothChartPartial d p i u x)^2 :=
  Yau.real_toLp_norm_sq _ (sphereSmoothChartPartial_memLp d p i u)

theorem sphereChartDerivativeLinear_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ i (u : SphereEnergySmooth d), ‖sphereChartDerivativeLinear d p i u‖ ≤ C*‖u‖ := by
  obtain ⟨K,hK,hb⟩ := sphere_chart_cube_energy_bound d.tensor d.smooth d.symm d.pos
    d.density d.continuous d.positive p
  refine ⟨Real.sqrt K,Real.sqrt_pos.mpr hK,?_⟩
  intro i u
  have h := hb (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property
  rw [← SphereEnergySmooth.norm_sq] at h
  have hle : (∫ x in realFinCube 4, (sphereSmoothChartPartial d p i u x)^2) ≤
      ∫ x in realFinCube 4, ∑ j, (sphereSmoothChartPartial d p j u x)^2 := by
    apply integral_mono (sphereSmoothChartPartial_memLp d p i u).integrable_sq
      (integrable_finsetSum _ (fun j _ ↦ (sphereSmoothChartPartial_memLp d p j u).integrable_sq))
    intro x
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (sphereSmoothChartPartial d p j u x)) (Finset.mem_univ i)
  have hsq : ‖sphereChartDerivativeLinear d p i u‖^2 ≤ K*‖u‖^2 := by
    rw [sphereChartDerivativeLinear_norm_sq]
    have hm : 0 ≤ ∫ x in realFinCube 4, ((SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x))^2 :=
      integral_nonneg (fun _ ↦ sq_nonneg _)
    exact hle.trans (by unfold sphereSmoothChartPartial; linarith)
  have hroot : (Real.sqrt K*‖u‖)^2 = K*‖u‖^2 := by rw [mul_pow,Real.sq_sqrt hK.le]
  nlinarith [mul_nonneg (Real.sqrt_nonneg K) (norm_nonneg u),norm_nonneg (sphereChartDerivativeLinear d p i u)]

def sphereChartDerivativeMap (d : SphereEnergyData) (p : Base) (i : Fin 4) :
    SphereEnergyHilbert d →L[ℝ] SphereChartCubeL2 :=
  (sphereChartDerivativeLinear d p i).extendOfNorm (sphereEnergyToCompletion d).toLinearMap

theorem sphereChartDerivativeMap_coe (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : sphereChartDerivativeMap d p i (sphereEnergyToCompletion d u) =
      sphereChartDerivativeLinear d p i u := by
  apply LinearMap.extendOfNorm_eq (sphereEnergyToCompletion_dense d)
  obtain ⟨C,_,hC⟩ := sphereChartDerivativeLinear_bound d p
  exact ⟨C,fun v ↦ by simpa using hC i v⟩

theorem sphereChartDerivativeMap_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ i (z : SphereEnergyHilbert d), ‖sphereChartDerivativeMap d p i z‖ ≤ C*‖z‖ := by
  obtain ⟨C,hC,hb⟩ := sphereChartDerivativeLinear_bound d p
  refine ⟨C,hC,fun i z ↦ ?_⟩
  have hn : ‖sphereChartDerivativeMap d p i‖ ≤ C :=
    LinearMap.opNorm_extendOfNorm_le (sphereEnergyToCompletion_dense d) hC.le
      (fun u ↦ by simpa using hb i u)
  exact ((sphereChartDerivativeMap d p i).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg z))

end
end Yau.Target

end OAI
