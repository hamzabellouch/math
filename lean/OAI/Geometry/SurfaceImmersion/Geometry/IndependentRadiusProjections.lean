import OAI.Geometry.SurfaceImmersion.Geometry.GenericRadiusParameters

namespace OAI

/-! The pair and triple projections used for independently perturbed disk
radii are actual surjective bounded linear maps. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PublishedInputs
variable {ι : Type*} [DecidableEq ι]

def radiusPairProjection (i j : ι) : (ι → ℝ) →L[ℝ] Plane :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun a : Fin 2 => ContinuousLinearMap.proj (if a = 0 then i else j)))

omit [DecidableEq ι] in
@[simp] lemma radiusPairProjection_apply_zero (i j : ι) (t : ι → ℝ) :
    radiusPairProjection i j t 0 = t i := by
  simp [radiusPairProjection]

omit [DecidableEq ι] in
@[simp] lemma radiusPairProjection_apply_one (i j : ι) (t : ι → ℝ) :
    radiusPairProjection i j t 1 = t j := by
  simp [radiusPairProjection]

lemma radiusPairProjection_surjective {i j : ι} (hij : i ≠ j) :
    Function.Surjective (radiusPairProjection i j) := by
  intro y
  refine ⟨Function.update (Function.update (fun _ => 0) i (y 0)) j (y 1),?_⟩
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).injective
  funext a
  fin_cases a
  · simp [hij]
  · simp

def radiusTripleProjection (i j k : ι) : (ι → ℝ) →L[ℝ] (Plane × ℝ) :=
  (radiusPairProjection i j).prod (ContinuousLinearMap.proj k)

lemma radiusTripleProjection_surjective {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Surjective (radiusTripleProjection i j k) := by
  intro y
  refine ⟨Function.update
    (Function.update (Function.update (fun _ => 0) i (y.1 0)) j (y.1 1)) k y.2,?_⟩
  apply Prod.ext
  · change radiusPairProjection i j _ = y.1
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).injective
    funext a
    fin_cases a
    · simp [hij,hik]
    · simp [hjk]
  · simp [radiusTripleProjection]

end ClosedSurfaceR4.PublishedInputs

end

end OAI
