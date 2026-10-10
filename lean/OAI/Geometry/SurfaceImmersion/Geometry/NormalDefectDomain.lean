import OAI.Geometry.SurfaceImmersion.Atlas.NormalDefectCoordinates

namespace OAI

/-! The normal-defect coordinates exist on a genuine open neighborhood
of the entire compact crosscap strip axis. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def normalFrameDomain (φ : Base → ProjectionTarget 3) (a : Fin 3 → ℝ) : Set Base :=
  {x | transverseDerivative φ x ⨯₃ a ≠ 0}

lemma normalFrameDomain_open {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    (a : Fin 3 → ℝ) : IsOpen (normalFrameDomain φ a) := by
  have hu : Continuous (transverseDerivative φ) := (transverseDerivative_smooth hφ).continuous
  have hcross : Continuous (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  exact isOpen_ne.preimage hcross

lemma normalFrameDomain_nonzero {φ : Base → ProjectionTarget 3} {a : Fin 3 → ℝ}
    {x : Base} (hx : x ∈ normalFrameDomain φ a) : transverseDerivative φ x ≠ 0 := by
  intro hz
  apply hx
  rw [hz]
  simp

lemma normalFrameDomain_transverse {φ : Base → ProjectionTarget 3} {a : Fin 3 → ℝ}
    {x : Base} (hx : x ∈ normalFrameDomain φ a) :
    ∀ r : ℝ, r • transverseDerivative φ x ≠ a := by
  exact (LinearIndependent.pair_iff' (normalFrameDomain_nonzero hx)).mp
    (crossProduct_ne_zero_iff_linearIndependent.mp hx)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
lemma CrosscapCoordinateStrip.transverseDerivative_axis (S : CrosscapCoordinateStrip A) (t : ℝ) :
    transverseDerivative S.model (![0,t] : Base) = S.transverseVector t := by
  simp only [transverseDerivative,coordinateDifferential,
    CrosscapCoordinateStrip.transverseVector,crosscapAxis_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem CrosscapCoordinateStrip.normal_defect_rectangle (S : CrosscapCoordinateStrip A) :
    ∃ (a : Fin 3 → ℝ) (δ : ℝ) (U : Set Base), 0 < δ ∧ IsOpen U ∧ U ⊆ S.domain ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (A.arc.start-δ) (A.arc.finish+δ), (![x,t] : Base) ∈ U) ∧
      ContDiffOn ℝ ∞ (normalDefect S.model a) U ∧
      ∀ x ∈ U, Function.Injective (fderiv ℝ S.model x) ↔ normalDefect S.model a x ≠ 0 := by
  obtain ⟨a,ha⟩ := exists_curve_transverse_vector S.transverseVector S.transverseVector_smooth
  let U := S.domain ∩ normalFrameDomain S.model a
  have hU : IsOpen U := S.domain_open.inter (normalFrameDomain_open S.model_smooth a)
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U := by
    intro t ht
    constructor
    · apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
      constructor <;> linarith [S.width_pos,ht.1,ht.2]
    · change transverseDerivative S.model (![0,t] : Base) ⨯₃ a ≠ 0
      rw [S.transverseDerivative_axis]
      exact curve_transverse_cross_ne_zero (S.transverseVector_ne_zero ht) (ha t)
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_rectangle A.arc.start_lt_finish.le hU haxis
  refine ⟨a,δ,U,hδ,hU,inter_subset_left,hrect,?_,?_⟩
  · exact normalDefect_smooth S.model_smooth (fun _ hx => normalFrameDomain_nonzero hx.2)
      (fun _ hx => normalFrameDomain_transverse hx.2)
  · intro x hx
    exact normalDefect_immersion_iff S.model a x (normalFrameDomain_nonzero hx.2)
      (normalFrameDomain_transverse hx.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
