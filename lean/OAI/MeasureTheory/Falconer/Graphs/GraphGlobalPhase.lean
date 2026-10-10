import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalDomain
import OAI.MeasureTheory.Falconer.Estimates.DistanceForm

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphPlaneEquiv_polar (p : ℝ × ℝ) :
    graphPlaneEquiv (polarCoord.symm p) = p.1 • sourceDirection p.2 := by
  ext i
  fin_cases i <;> simp [graphPlaneEquiv, sourceDirection, Complex.orthonormalBasisOneI_repr_apply,
    polarCoord, MeasurableEquiv.finTwoArrow, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem graph_plane_axis {η : Plane} (hη : η ∈ graphPlaneSlit) :
    ‖η‖ • sourceDirection (graphPlaneAngle η) = η := by
  have he := graphPlaneEquiv_polar (polarCoord (graphPlaneEquiv.symm η))
  rw [polarCoord.left_inv hη, MeasurableEquiv.apply_symm_apply,
    graphPlaneEquiv_symm_radius] at he
  exact he.symm

theorem graph_global_endpoint_frequencies {η : Plane} (hη : η ∈ graphPlaneSlit) (z : ℝ) :
    (‖η‖*Real.sqrt (1+z^2)/2) • sourceDirection (graphPlaneAngle η+Real.arctan z) = graphB z η ∧
    (‖η‖*Real.sqrt (1+z^2)/2) • sourceDirection (graphPlaneAngle η-Real.arctan z) = graphA z η := by
  have he := graphLiftMap_endpoint_frequencies ![‖η‖,graphPlaneAngle η,z]
  simp only [graphCartesianFrequency_polar, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, graph_plane_axis hη] at he
  exact he

theorem graphB_inner (z : ℝ) (η x : Plane) :
    inner ℝ (graphB z η) x = inner ℝ η (graphA z x) := by
  have hq : inner ℝ (quarterTurn η) x = -inner ℝ η (quarterTurn x) := by
    simp [quarterTurn, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [graphA, graphB, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_sub_right, hq]
  ring

theorem graphA_inner (z : ℝ) (η x : Plane) :
    inner ℝ (graphA z η) x = inner ℝ η (graphB z x) := by
  simpa only [graphA, graphB, neg_smul, sub_neg_eq_add, ← sub_eq_add_neg] using graphB_inner (-z) η x

theorem graph_global_plane_wave_phase {η : Plane} (hη : η ∈ graphPlaneSlit)
    (z R : ℝ) (x y : Plane) :
    sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z)) x *
      sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) y =
      Complex.exp (Complex.I*(R:ℂ)*(inner ℝ η (graphA z x+graphB z y) : ℂ)) := by
  have he := graph_global_endpoint_frequencies hη z
  have hx := congrArg (fun w : Plane => inner ℝ w x) he.1
  have hy := congrArg (fun w : Plane => inner ℝ w y) he.2
  simp only [real_inner_smul_left, graphB_inner, graphA_inner] at hx hy
  simp only [sourcePlaneWave, ← Complex.exp_add, Complex.ofReal_mul]
  change Complex.exp (Complex.I*(↑R*↑(‖η‖*Real.sqrt (1+z^2)/2))*↑(inner ℝ
      (sourceDirection (graphPlaneAngle η+Real.arctan z)) x) +
    Complex.I*(↑R*↑(‖η‖*Real.sqrt (1+z^2)/2))*↑(inner ℝ
      (sourceDirection (graphPlaneAngle η-Real.arctan z)) y)) = _
  have hx' := congrArg (fun r : ℝ => (r:ℂ)) hx
  have hy' := congrArg (fun r : ℝ => (r:ℂ)) hy
  simp only [Complex.ofReal_mul] at hx' hy'
  rw [inner_add_right, Complex.ofReal_add]
  congr 1
  linear_combination Complex.I*(R:ℂ)*hx' + Complex.I*(R:ℂ)*hy'

theorem sourcePlaneWave_add_pi (r θ : ℝ) (x : Plane) :
    sourcePlaneWave r (sourceUnitDirection (θ+Real.pi)) x =
      sourcePlaneWave r (sourceUnitDirection θ) (-x) := by
  change Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection (θ+Real.pi)) x : ℂ)) =
    Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection θ) (-x) : ℂ))
  rw [sourceDirection_add_pi, inner_neg_left, inner_neg_right]

theorem graph_global_plane_wave_phase_minus {η : Plane} (hη : η ∈ graphPlaneSlit)
    (z R : ℝ) (x y : Plane) :
    sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η+Real.arctan z)) x *
      sourcePlaneWave (R*(‖η‖*Real.sqrt (1+z^2)/2))
        (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+Real.pi)) y =
      Complex.exp (Complex.I*(R:ℂ)*(inner ℝ η (graphA z x-graphB z y) : ℂ)) := by
  rw [sourcePlaneWave_add_pi, graph_global_plane_wave_phase hη]
  have hn : graphB z (-y) = -graphB z y := by
    ext i
    fin_cases i <;> simp [graphB, quarterTurn] <;> ring
  rw [hn, ← sub_eq_add_neg]

theorem graph_phase_affine (z s : ℝ) (x y : Plane) :
    graphA z x+s • graphB z y = (1/2:ℝ) • (x+s • y) + z • graphDerivative s x y := by
  ext i
  fin_cases i <;> simp [graphA,graphB,graphDerivative,quarterTurn] <;> ring

end PlanarFalconer

end OAI
