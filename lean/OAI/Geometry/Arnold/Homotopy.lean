import OAI.Geometry.Arnold.Exterior

namespace OAI

universe uE uD uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial inclusion in the cylinder. -/
def spatial : E →L[ℝ] ℝ × E := (0 : E →L[ℝ] ℝ).prod (.id ℝ E)

@[simp] lemma spatial_apply (v : E) : spatial v = (0, v) := rfl

/-- Fixed-direction contraction and slice restriction, bundled in norm topology. -/
def cylinderContraction (n : ℕ) :
    ((ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℝ) :=
  let P : ((ℝ × E) [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℝ) :=
    (compContinuousLinearMapₗ (ι := Fin n) (N := ℝ) spatial).mkContinuous
      (‖(spatial : E →L[ℝ] ℝ × E)‖ ^ n) (by
        intro θ
        simpa only [compContinuousLinearMapₗ, LinearMap.coe_mk, AddHom.coe_mk,
          Fintype.card_fin, mul_comm] using θ.norm_compContinuousLinearMap_le spatial)
  P.comp ((ContinuousLinearMap.apply ℝ
    ((ℝ × E) [⋀^Fin n]→L[ℝ] ℝ) (1, 0)).comp (curryLeftLI.toContinuousLinearMap))

@[simp] lemma cylinderContraction_apply (n : ℕ)
    (θ : (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ) (v : Fin n → E) :
    cylinderContraction n θ v = θ (Matrix.vecCons (1, 0) (fun i ↦ (0, v i))) := rfl

def sliceContraction {n : ℕ}
    (Θ : ℝ × E → (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ) (t : ℝ) :
    E → E [⋀^Fin n]→L[ℝ] ℝ := fun z ↦ cylinderContraction n (Θ (t, z))

lemma sliceContraction_contDiff {n : ℕ}
    (Θ : ℝ × E → (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (hΘ : ContDiff ℝ ∞ Θ) (t : ℝ) : ContDiff ℝ ∞ (sliceContraction Θ t) := by
  exact (cylinderContraction n).contDiff.comp (hΘ.comp (contDiff_const.prodMk contDiff_id))

/-- The time derivative of a closed form restricted to slices is the spatial
exterior derivative of its contraction with the time direction. -/
theorem cylinder_homotopy_identity {n : ℕ}
    (Θ : ℝ × E → (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (hΘ : Differentiable ℝ Θ) (t : ℝ) (z : E)
    (hclosed : extDeriv Θ (t, z) = 0) (v : Fin (n + 1) → E) :
    extDeriv (sliceContraction Θ t) z v =
      (fderiv ℝ Θ (t, z) (1, 0)) (fun i ↦ (0, v i)) := by
  have hr {k : ℕ} (i : Fin (k + 1)) (w : Fin (k + 1) → ℝ × E) :
      i.succ.removeNth (Matrix.vecCons (1, 0) w) =
        Matrix.vecCons (1, 0) (i.removeNth w) :=
    Fin.cons_comp_succ_succAbove (1, 0) w i
  have hd : fderiv ℝ (sliceContraction Θ t) z =
      (cylinderContraction n).comp ((fderiv ℝ Θ (t, z)).comp spatial) := by
    exact ((cylinderContraction n).hasFDerivAt.comp z
      ((hΘ (t, z)).hasFDerivAt.comp z
        ((hasFDerivAt_const (c := t) z).prodMk (hasFDerivAt_id z)))).fderiv
  have hc : extDeriv Θ (t, z) (Matrix.vecCons (1, 0) (fun i ↦ (0, v i))) = 0 := by
    rw [hclosed]; rfl
  simp only [extDeriv, alternatizeUncurryFin_apply] at hc ⊢
  rw [Fin.sum_univ_succ] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.removeNth_zero,
    Fin.val_zero, pow_zero, one_smul, hr, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Finset.sum_neg_distrib] at hc
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, spatial_apply, cylinderContraction_apply]
  have heq : (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (fderiv ℝ Θ (t, z) (0, v i))
        (Matrix.vecCons (1, 0) (fun j ↦ (0, (i.removeNth v) j)))) =
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (fderiv ℝ Θ (t, z) (0, v i))
        (Matrix.vecCons (1, 0) (i.removeNth (fun j ↦ (0, v j))))) := rfl
  rw [heq]
  change (fderiv ℝ Θ (t, z) (1, 0)) (fun i ↦ (0, v i)) -
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (fderiv ℝ Θ (t, z) (0, v i))
        (Matrix.vecCons (1, 0) (i.removeNth (fun j ↦ (0, v j))))) = 0 at hc
  linarith

instance finiteDimensional_multilinear_fin [FiniteDimensional ℝ E] (n : ℕ) :
    FiniteDimensional ℝ (E [×n]→L[ℝ] ℝ) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toLinearEquiv.finiteDimensional
  | succ n ih =>
    let := ih
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ).symm.toLinearEquiv.finiteDimensional

/-- Smoothness into finite-dimensional alternating forms can be checked after
forgetting alternation. This uses an honest linear retraction, not an axiom. -/
lemma contDiff_of_toMultilinear {D : Type uD} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ E] {n : ℕ} {k : ℕ∞ω}
    {f : D → E [⋀^Fin n]→L[ℝ] ℝ}
    (hf : ContDiff ℝ k (fun x ↦ (f x).toContinuousMultilinearMap)) : ContDiff ℝ k f := by
  let L := (toContinuousMultilinearMapCLM (𝕜 := ℝ) (E := E) (F := ℝ) (ι := Fin n) ℝ).toLinearMap
  have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr toContinuousMultilinearMap_injective
  obtain ⟨R, hR⟩ := L.exists_leftInverse_of_injective hL
  have heq : f = fun x ↦ R.toContinuousLinearMap ((f x).toContinuousMultilinearMap) := by
    funext x
    exact (LinearMap.congr_fun hR (f x)).symm
  rw [heq]
  exact R.toContinuousLinearMap.contDiff.comp hf

lemma contDiff_pullback_form {D : Type uD} {F : Type uF}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] {n : ℕ} {k : ℕ∞ω}
    {θ : D → F [⋀^Fin n]→L[ℝ] ℝ} {L : D → E →L[ℝ] F}
    (hθ : ContDiff ℝ k θ) (hL : ContDiff ℝ k L) :
    ContDiff ℝ k (fun x ↦ (θ x).compContinuousLinearMap (L x)) := by
  apply contDiff_of_toMultilinear
  let : TopologicalSpace (E →L[ℝ] F) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] F)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : TopologicalSpace ((F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
    (inferInstance : NormedAddCommGroup ((F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ))).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let P : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E →L[ℝ] F)
      ((F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapMultilinear
      ℝ (fun _ : Fin n ↦ E) (fun _ ↦ F) ℝ).mkContinuous 1 (by
        intro g
        rw [one_mul]
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℝ g)
  have hPc : ContDiff ℝ k (fun g : Fin n → E →L[ℝ] F ↦ P g) := by
    exact ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (E := fun _ : Fin n ↦ E →L[ℝ] F)
      (F := (F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ)) P
  have hP := hPc.comp (contDiff_pi.mpr (fun _ ↦ hL))
  exact hP.clm_apply ((toContinuousMultilinearMapCLM (𝕜 := ℝ) (E := F) (F := ℝ) (ι := Fin n) ℝ).contDiff.comp hθ)

/-- Pullback of a constant form is closed. -/
lemma pullback_constant_closed {D : Type uD} {F : Type uF}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (θ : F [⋀^Fin n]→L[ℝ] ℝ) (H : D → F)
    (hH : ContDiff ℝ ∞ H) (x : D) :
    extDeriv (fun y ↦ θ.compContinuousLinearMap (fderiv ℝ H y)) x = 0 := by
  have hθ : DifferentiableAt ℝ (fun _ : F ↦ θ) (H x) := differentiableAt_const _
  have hH2 : ContDiffAt ℝ 2 H x := hH.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hp := extDeriv_pullback hθ hH2 (by simp)
  convert hp using 1
  ext v
  simp [extDeriv, alternatizeUncurryFin_apply]

end ArnoldCounterexample.Forms

end

end OAI
