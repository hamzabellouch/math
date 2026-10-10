import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodJointSupport

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set Filter ConvexSkorokhod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem joint_causal_reflected_map (B : Body E) (c : E) (r R : ℝ)
    (hr : 0<r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀z∈B.carrier,‖z-c‖≤R) :
    ∃Φ : B.carrier × VectorPath E → VectorPath E,Continuous Φ ∧
      (∀x : B.carrier,IsReflectedMap B x (fun f => Φ (x,f))) ∧
      (∀(x y : B.carrier) (f : VectorPath E),‖Φ (x,f)-Φ (y,f)‖≤‖(x:E)-y‖) ∧
      ∀(x : B.carrier) (f g : VectorPath E) (t : Set.Icc (0:ℝ) 1),
        (∀s : Set.Icc (0:ℝ) 1,s≤t → f s=g s) → Φ (x,f) t=Φ (x,g) t := by
  classical
  have hex (x : B.carrier) := measurable_reflected_path_map B x c r R x.2 hr hball hR
  choose φ hφcont hφmeas hφ using hex
  have hnormal (x : B.carrier) : IsReflectedMap B x (φ x) := hφ x
  let Φ : B.carrier × VectorPath E → VectorPath E := fun p => φ p.1 p.2
  have hc : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (hφcont p.1).continuousAt (ε/2) (half_pos hε)
    refine ⟨min (ε/2) δ,lt_min (half_pos hε) hδ,?_⟩
    intro q hq
    have hds : dist q.1 p.1 < min (ε/2) δ ∧ dist q.2 p.2 < min (ε/2) δ := by
      simpa only [Prod.dist_eq,max_lt_iff] using hq
    have hfirst : dist (φ q.1 q.2) (φ p.1 q.2)≤dist q.1 p.1 := by
      simpa only [dist_eq_norm,Subtype.dist_eq] using map_initial_contraction B q.1 p.1
        (φ q.1) (φ p.1) (hnormal q.1) (hnormal p.1) q.2
    have hsecond : dist (φ p.1 q.2) (φ p.1 p.2)<ε/2 := hd (hds.2.trans_le (min_le_right _ _))
    calc
      dist (Φ q) (Φ p) ≤ dist (φ q.1 q.2) (φ p.1 q.2)+dist (φ p.1 q.2) (φ p.1 p.2) := dist_triangle _ _ _
      _ ≤ dist q.1 p.1+dist (φ p.1 q.2) (φ p.1 p.2) := add_le_add hfirst le_rfl
      _ < ε/2+ε/2 := add_lt_add (hds.1.trans_le (min_le_left _ _)) hsecond
      _ = ε := by ring
  exact ⟨Φ,hc,hnormal,fun x y f => map_initial_contraction B x y (φ x) (φ y) (hnormal x) (hnormal y) f,
    fun x f g t hfg => map_causal B x (φ x) (hnormal x) f g t hfg⟩

end BrownianForcing

end OAI
