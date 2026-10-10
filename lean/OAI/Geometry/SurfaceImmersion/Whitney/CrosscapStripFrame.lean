import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCoordinateStrip
import OAI.Geometry.SurfaceImmersion.Geometry.CurveNormalFrame

namespace OAI

/-! A smooth invertible target frame on a neighborhood of the actual strip axis. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

def CrosscapCoordinateStrip.transverseVector (S : CrosscapCoordinateStrip A) (t : ℝ) : Fin 3 → ℝ :=
  EuclideanSpace.equiv (Fin 3) ℝ (fderiv ℝ S.model (crosscapAxis t) (![1,0] : Base))

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
lemma CrosscapCoordinateStrip.transverseVector_smooth (S : CrosscapCoordinateStrip A) :
    ContDiff ℝ ∞ S.transverseVector := by
  have hD := S.model_smooth.fderiv_right (m := ∞) (by simp)
  exact (EuclideanSpace.equiv (Fin 3) ℝ).contDiff.comp
    ((hD.comp crosscapAxis.contDiff).clm_apply contDiff_const)

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
lemma CrosscapCoordinateStrip.transverseVector_ne_zero (S : CrosscapCoordinateStrip A)
    {t : ℝ} (ht : t ∈ Icc A.arc.start A.arc.finish) : S.transverseVector t ≠ 0 := by
  intro hz
  apply S.transverse t ht
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simpa only [CrosscapCoordinateStrip.transverseVector,map_zero,crosscapAxis_apply] using hz

lemma curveNormalLinear_smooth {v : ℝ → Fin 3 → ℝ} (hv : ContDiff ℝ ∞ v) (a : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (fun t => curveNormalLinear (v t) a) := by
  have hcross : ContDiff ℝ ∞ (fun t => v t ⨯₃ a) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  exact ((contDiff_const.smulRight hv).add contDiff_const).add (contDiff_const.smulRight hcross)

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem CrosscapCoordinateStrip.exists_frame (S : CrosscapCoordinateStrip A) :
    ∃ (a : Fin 3 → ℝ) (J : Set ℝ), IsOpen J ∧ Icc A.arc.start A.arc.finish ⊆ J ∧
      ContDiff ℝ ∞ (fun t => curveNormalLinear (S.transverseVector t) a) ∧
      ∀ t ∈ J, Function.Bijective (curveNormalLinear (S.transverseVector t) a) := by
  obtain ⟨a,ha⟩ := exists_curve_transverse_vector S.transverseVector S.transverseVector_smooth
  let J := {t | S.transverseVector t ≠ 0}
  have hJ : IsOpen J := isOpen_ne.preimage S.transverseVector_smooth.continuous
  refine ⟨a,J,hJ,fun t ht => S.transverseVector_ne_zero ht,
    curveNormalLinear_smooth S.transverseVector_smooth a,?_⟩
  intro t ht
  exact curveNormalLinear_bijective ht (ha t)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
