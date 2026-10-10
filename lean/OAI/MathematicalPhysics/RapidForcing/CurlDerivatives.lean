import OAI.MathematicalPhysics.RapidForcing.Collars

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma curl_smooth {v : Space → Space} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (curl v) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ v) := hv.fderiv_right (by simp)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [curl, vec] <;> fun_prop

lemma movingPotential_spatial_smooth (c : ℝ → Space) (δ σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y =>
      ζ (δ⁻¹ • (y - c σ)) • ((1 / 2 : ℝ) • cross (deriv c σ) (y - c σ))) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [cross, vec] <;> unfold ζ <;> fun_prop

lemma movingCurl_spatial_smooth (c : ℝ → Space) (δ σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (movingCurl c δ σ) :=
  curl_smooth (movingPotential_spatial_smooth c δ σ)

lemma addressedVelocity_spatial_smooth (M : Machine) (w : M.Input) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (addressedVelocity M w t) := by
  unfold addressedVelocity
  split_ifs
  · exact movingCurl_spatial_smooth _ _ _
  · apply ContDiff.sum
    intro m _
    exact movingCurl_spatial_smooth _ _ _


lemma fderiv_coordinate {v : Space → Space} {x : Space}
    (hv : DifferentiableAt ℝ v x) (i : Fin 3) (b : Space) :
    fderiv ℝ (fun y => v y i) x b = (fderiv ℝ v x b) i := by
  have h := (EuclideanSpace.proj i).hasFDerivAt.comp x hv.hasFDerivAt
  have hf : HasFDerivAt (fun y => v y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ v x)) x := by
    simpa only [Function.comp_def, PiLp.proj_apply] using h
  rw [hf.fderiv]
  rfl

lemma hasFDerivAt_partial_coordinate {v : Space → Space} {x : Space}
    (hv : DifferentiableAt ℝ (fderiv ℝ v) x) (i j : Fin 3) :
    HasFDerivAt (fun y => (fderiv ℝ v y (basis i)) j)
      ((EuclideanSpace.proj j).comp
        ((ContinuousLinearMap.apply ℝ Space (basis i)).comp (fderiv ℝ (fderiv ℝ v) x))) x := by
  simpa only [Function.comp_def, PiLp.proj_apply, ContinuousLinearMap.apply_apply] using
    (EuclideanSpace.proj j).hasFDerivAt.comp x
      ((ContinuousLinearMap.apply ℝ Space (basis i)).hasFDerivAt.comp x hv.hasFDerivAt)

lemma divergence_curl_eq_zero {v : Space → Space}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Space) :
    (∑ i, (fderiv ℝ (curl v) x (basis i)) i) = 0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x
  have hC : DifferentiableAt ℝ (curl v) x := (curl_smooth hv).differentiable (by simp) x
  let g := fun i j : Fin 3 => fun y : Space => (fderiv ℝ v y (basis i)) j
  have hg (i j : Fin 3) : DifferentiableAt ℝ (g i j) x :=
    (hasFDerivAt_partial_coordinate hD i j).differentiableAt
  have hgf (i j : Fin 3) (a : Space) :
      fderiv ℝ (g i j) x a = (fderiv ℝ (fderiv ℝ v) x a (basis i)) j := by
    rw [(hasFDerivAt_partial_coordinate hD i j).fderiv]
    rfl
  simp only [Fin.sum_univ_three]
  rw [← fderiv_coordinate hC 0, ← fderiv_coordinate hC 1, ← fderiv_coordinate hC 2]
  change fderiv ℝ (g 1 2 - g 2 1) x (basis 0) +
    fderiv ℝ (g 2 0 - g 0 2) x (basis 1) +
    fderiv ℝ (g 0 1 - g 1 0) x (basis 2) = 0
  rw [fderiv_sub (hg 1 2) (hg 2 1), fderiv_sub (hg 2 0) (hg 0 2),
    fderiv_sub (hg 0 1) (hg 1 0)]
  simp only [sub_apply, hgf]
  have hS := (hv.of_le (m := 2) (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (x := x) |>.isSymmSndFDerivAt (by simp)
  rw [hS (basis 0) (basis 1), hS (basis 0) (basis 2), hS (basis 1) (basis 2)]
  ring

lemma movingCurl_divergence (c : ℝ → Space) (δ σ : ℝ) (x : Space) :
    divergence (movingCurl c δ) σ x = 0 :=
  divergence_curl_eq_zero (movingPotential_spatial_smooth c δ σ) x

lemma divergence_sum {ι : Type} (s : Finset ι) (v : ι → Space → Space) (x : Space)
    (hv : ∀ j ∈ s, DifferentiableAt ℝ (v j) x) :
    (∑ i, (fderiv ℝ (fun y => ∑ j ∈ s, v j y) x (basis i)) i) =
      ∑ j ∈ s, ∑ i, (fderiv ℝ (v j) x (basis i)) i := by
  have he : (fun y => ∑ j ∈ s, v j y) = ∑ j ∈ s, v j := by
    funext y
    simp
  rw [he, fderiv_sum hv]
  simp only [sum_apply]
  change (∑ i, (∑ j ∈ s, fderiv ℝ (v j) x (basis i)).ofLp i) = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_comm

theorem addressedVelocity_divergence (M : Machine) (w : M.Input) (t : ℝ) (x : Space) :
    divergence (addressedVelocity M w) t x = 0 := by
  unfold divergence spatialD addressedVelocity
  split_ifs
  · exact movingCurl_divergence _ _ _ _
  · rw [divergence_sum]
    · apply Finset.sum_eq_zero
      intro m _
      exact movingCurl_divergence _ _ _ _
    · intro m _
      exact (movingCurl_spatial_smooth _ _ _).differentiable (by simp) x

lemma gradient_zero (t : ℝ) (x : Space) : gradient (fun _ _ => 0) t x = 0 := by
  simp [gradient, spatialD]

theorem addressed_pointwise_equations (ν : ℝ) (M : Machine) (w : M.Input) :
    NavierStokes ν (addressedForce ν M w) (addressedVelocity M w) (fun _ _ => 0) := by
  refine ⟨?_, ?_, addressedVelocity_initial M w⟩
  · intro t _ x
    rw [gradient_zero]
    unfold addressedForce residual
    abel
  · intro t _ x
    exact addressedVelocity_divergence M w t x

end RapidForcing

end OAI
