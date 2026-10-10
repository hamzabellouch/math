import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodJoint

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set ConvexSkorokhod

abbrev FreeHeightSpace (m : ℕ) := EuclideanSpace ℝ (Fin m)

noncomputable def weightedBodyMeasure {m : ℕ} (B : Body (FreeHeightSpace m))
    (b : FreeHeightSpace m) : Measure (FreeHeightSpace m) :=
  (volume.restrict B.carrier).withDensity (fun x => ENNReal.ofReal (Real.exp (inner ℝ b x)))

noncomputable def weightedBodyLaw {m : ℕ} (B : Body (FreeHeightSpace m))
    (b : FreeHeightSpace m) : Measure (FreeHeightSpace m) :=
  (weightedBodyMeasure B b Set.univ)⁻¹ • weightedBodyMeasure B b

noncomputable def linearVectorPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E) : VectorPath E := ⟨fun t => (t:ℝ) • b,by fun_prop⟩

noncomputable def reverseVectorPath {E : Type*} [TopologicalSpace E]
    (f : VectorPath E) : VectorPath E :=
  ⟨fun t => f ⟨1-(t:ℝ),by constructor <;> linarith [t.2.1,t.2.2]⟩,by fun_prop⟩

noncomputable def fullReflectedMap {m : ℕ} (B : Body (FreeHeightSpace m))
    (c : FreeHeightSpace m) (r R : ℝ) (hr : 0<r)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R) :
    FreeHeightSpace m × VectorPath (FreeHeightSpace m) → VectorPath (FreeHeightSpace m) :=
  fun p => (Classical.choose (joint_causal_reflected_map B c r R hr hball hR))
    (⟨project B p.1,project_mem B p.1⟩,p.2)

noncomputable def reflectedBathLaw {m : ℕ} (B : Body (FreeHeightSpace m))
    (c : FreeHeightSpace m) (r R : ℝ) (hr : 0<r)
    (hball : Metric.closedBall c r⊆B.carrier) (hR : ∀z∈B.carrier,‖z-c‖≤R)
    (μ : Measure (VectorPath (FreeHeightSpace m))) (b : FreeHeightSpace m) :
    Measure (VectorPath (FreeHeightSpace m)) :=
  ((weightedBodyLaw B b).prod μ).map (fun p =>
    fullReflectedMap B c r R hr hball hR (p.1,p.2+linearVectorPath b))

end BrownianForcing

end OAI
