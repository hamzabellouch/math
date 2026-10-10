import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothLieExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothIntegralCurve

namespace OAI

/-! # Smoothness of invariant fields and exponential lines at C-infinity regularity -/

noncomputable section
namespace PolycyclicRecognition.SmoothLie
open Bundle Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ∞ G]

local instance : LieGroup (𝓘(ℝ,E)) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞) (by simp)

omit [FiniteDimensional ℝ E] in
theorem isMIntegralCurve_of_exponential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t : ℝ => Exp (t • v))
      (mulInvariantVectorField v) := by
  intro t
  let γ : ℝ → G := fun s => Exp (s • v)
  let D : ℝ →L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  have hzero : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (t - t) D := by
    rw [sub_self]
    exact hExp.hasMFDerivAt_zero v
  have hshift : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => s - t) t
      (ContinuousLinearMap.id ℝ ℝ) := by
    have hD : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
        ContinuousLinearMap.id ℝ ℝ := by ext; simp
    simpa only [id_eq, hD] using
      ((hasDerivAt_id t).sub_const t).hasFDerivAt.hasMFDerivAt
  have hbase := HasMFDerivAt.comp t (f := fun s : ℝ => s - t) hzero hshift
  have hleft : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g)
      (γ (t - t)) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) := by
    rw [show γ (t - t) = 1 from by simp [γ, hExp.map_zero]]
    have h : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1 :=
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := γ t) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun g : G => γ t * g)).mdifferentiableAt
        (by simp)
    exact h.hasMFDerivAt
  have hder := hleft.comp t hbase
  have heq : (fun s : ℝ => γ t * γ (s - t)) = γ := by
    funext s
    dsimp [γ]
    rw [← hExp.map_add_smul]
    congr 2
    ring
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t _
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E))
    (fun s : ℝ => γ t * γ (s - t)) t _ at hder
  rw [heq] at hder
  apply hder.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) (s • v) =
    s • (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) v
  exact map_smul _ s v


omit [FiniteDimensional ℝ E] in
theorem contMDiff_invariantVectorField_infty (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun g => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) := by
  let z : G → TangentBundle (𝓘(ℝ, E)) G := fun g => TotalSpace.mk' E g 0
  let c : G → TangentBundle (𝓘(ℝ, E)) G := fun _ => TotalSpace.mk' E 1 v
  have hz : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ z :=
    contMDiff_zeroSection _ _
  have hc : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ c :=
    contMDiff_const
  have hj := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (n := ∞) (M := G) (M' := G))
  have hm := (contMDiff_mul (G := G) (𝓘(ℝ, E)) ∞).contMDiff_tangentMap (m := ∞) (by simp)
  have h := (hm.comp hj).comp (hz.prodMk hc)
  convert! h with g
  · simp [z, c, equivTangentBundleProd, tangentMap]
  · change mulInvariantVectorField v g =
      mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
        (fun p : G × G => p.1 * p.2) (g, 1) (0, v)
    have hp := mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) (p := (g, 1)) (v := (0, v))
      ((contMDiff_mul (𝓘(ℝ, E)) ∞).mdifferentiableAt (by simp))
    have hzero : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z : G => z * 1) g)
        (0 : TangentSpace (𝓘(ℝ, E)) g) = 0 := map_zero _
    dsimp only at hp
    let w : E := mulInvariantVectorField v g
    exact (zero_add w).symm.trans
      ((congrArg (fun z : E => z + w) hzero).symm.trans hp.symm)

omit [FiniteDimensional ℝ E] in
theorem contMDiff_exponential_curve
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun t : ℝ => Exp (t • v)) :=
  PolycyclicRecognition.IsMIntegralCurve.contMDiff (isMIntegralCurve_of_exponential hExp v)
    (contMDiff_invariantVectorField_infty v)


end PolycyclicRecognition.SmoothLie

end

end OAI
