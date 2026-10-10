import Mathlib
import OAI.Analysis.AffineBernstein.SphereAlgebra

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_rotationPair {W : E → E} {e : E} (hW : DifferentiableAt ℝ W e)
    (u v z : E) :
    fderiv ℝ (fun q => inner ℝ u q * inner ℝ v (W q)) e z =
      inner ℝ u z * inner ℝ v (W e) + inner ℝ u e * inner ℝ v (fderiv ℝ W e z) := by
  have h1 := (InnerProductSpace.toDual ℝ E u).hasFDerivAt (x := e)
  have h2 := (InnerProductSpace.toDual ℝ E v).hasFDerivAt.comp e hW.hasFDerivAt
  have hd := (h1.mul h2).fderiv
  simp only [Pi.mul_def, Function.comp_def, InnerProductSpace.toDual_apply_apply] at hd
  rw [hd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem rotationPair_smooth {U : Set E} {W : E → E} (hW : ContDiffOn ℝ ∞ W U)
    (u v : E) : ContDiffOn ℝ ∞ (fun q => inner ℝ u q * inner ℝ v (W q)) U :=
  (contDiffOn_const.inner ℝ contDiffOn_id).mul (contDiffOn_const.inner ℝ hW)

theorem sphere_directional_integrable {U : Set E} (hU : IsOpen U)
    (hSU : sphere (0 : E) 1 ⊆ U) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (M : E →L[ℝ] E) :
    Integrable (fun e : sphere (0 : E) 1 => fderiv ℝ f e (M e)) volume.toSphere := by
  have hd : ContinuousOn (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  have hc : Continuous (fun e : sphere (0 : E) 1 => fderiv ℝ f e) :=
    hd.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  exact (hc.clm_apply (M.continuous.comp continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_sphere_rotation_basis (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (i j : ι) :
    (∫ e : sphere (0 : E) 1, fderiv ℝ f e (rotationGenerator (b i) (b j) e)
      ∂volume.toSphere) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [rotationGenerator]
  · exact integral_sphere_rotation_deriv
      (by simp)
      (by simp)
      (b.inner_eq_zero hij) hU hSU hf

/- No angular boundary term: the round divergence of an actual smooth tangent
vector field integrates to zero, including the two-point and empty spheres. -/
theorem integral_roundDivergence (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {W : E → E} (hW : ContDiffOn ℝ ∞ W U)
    (ht : ∀ e ∈ sphere (0 : E) 1, inner ℝ e (W e) = 0) :
    (∫ e : sphere (0 : E) 1, roundDivergence b W e ∂volume.toSphere) = 0 := by
  let Q : ι → ι → E → ℝ := fun i j q => inner ℝ (b i) q * inner ℝ (b j) (W q)
  have hsmooth (i j : ι) : ContDiffOn ℝ ∞ (Q i j) U := rotationPair_smooth hW _ _
  have hpoint (e : sphere (0 : E) 1) :
      (∑ i, ∑ j, fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e)) =
        roundDivergence b W e := by
    have hd : DifferentiableAt ℝ W (e : E) :=
      (hW.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp)
    simp only [Q, fderiv_rotationPair hd]
    rw [sum_rotation_pair b (e : E)]
    · rw [ht e e.property, mul_zero, add_zero, roundDivergence_trace]
    · rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp e.property]
      norm_num
  have hi (i j : ι) : Integrable (fun e : sphere (0 : E) 1 =>
      fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e)) volume.toSphere :=
    sphere_directional_integrable hU hSU (hsmooth i j) _
  calc
    (∫ e : sphere (0 : E) 1, roundDivergence b W e ∂volume.toSphere) =
        ∫ e : sphere (0 : E) 1, ∑ i, ∑ j,
          fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e) ∂volume.toSphere := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun e => (hpoint e).symm)
    _ = ∑ i, ∑ j, ∫ e : sphere (0 : E) 1,
          fderiv ℝ (Q i j) e (rotationGenerator (b i) (b j) e) ∂volume.toSphere := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hi i j)
    _ = 0 := by
      simp only [integral_sphere_rotation_basis b hU hSU (hsmooth _ _), Finset.sum_const_zero]

/- Product rule for the actual round divergence, with no coordinate frame
extension assumed. The only cancellation is actual tangency on the sphere. -/
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
theorem roundDivergence_smul (b : OrthonormalBasis ι ℝ E)
    {f : E → ℝ} {W : E → E} {e : E}
    (hf : DifferentiableAt ℝ f e) (hW : DifferentiableAt ℝ W e)
    (ht : inner ℝ e (W e) = 0) :
    roundDivergence b (fun q => f q • W q) e =
      fderiv ℝ f e (W e) + f e * roundDivergence b W e := by
  have hd := (hf.hasFDerivAt.smul hW.hasFDerivAt).fderiv
  simp only [Pi.smul_def'] at hd
  rw [roundDivergence_trace, hd, roundDivergence_trace]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, real_inner_smul_right,
    ht, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hw : (∑ i, fderiv ℝ f e (b i) * inner ℝ (b i) (W e)) = fderiv ℝ f e (W e) := by
    conv_rhs => rw [← b.sum_repr' (W e)]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hw]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphere_fderiv_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    Continuous (fun e : sphere (0 : E) 1 => fderiv ℝ f e) :=
  (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn.comp_continuous
    continuous_subtype_val (fun e => hSU e.property)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
theorem sphere_roundDivergence_continuous (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {W : E → E} (hW : ContDiffOn ℝ ∞ W U) :
    Continuous (fun e : sphere (0 : E) 1 => roundDivergence b W e) := by
  have hd := sphere_fderiv_continuous hU hSU hW
  unfold roundDivergence
  apply continuous_finsetSum
  intro i _
  exact continuous_const.inner (hd.clm_apply
    (continuous_const.sub ((continuous_subtype_val.inner continuous_const).smul continuous_subtype_val)))

/- One genuine spherical integration by parts; all integrability follows from
smoothness near the compact sphere. -/
theorem integral_sphere_by_parts (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {f : E → ℝ} {W : E → E} (hf : ContDiffOn ℝ ∞ f U) (hW : ContDiffOn ℝ ∞ W U)
    (ht : ∀ e ∈ sphere (0 : E) 1, inner ℝ e (W e) = 0) :
    (∫ e : sphere (0 : E) 1, f e * roundDivergence b W e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, fderiv ℝ f e (W e) ∂volume.toSphere) := by
  have hfc : Continuous (fun e : sphere (0 : E) 1 => f e) :=
    hf.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hWc : Continuous (fun e : sphere (0 : E) 1 => W e) :=
    hW.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hi1 : Integrable (fun e : sphere (0 : E) 1 => fderiv ℝ f e (W e)) volume.toSphere :=
    ((sphere_fderiv_continuous hU hSU hf).clm_apply hWc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun e : sphere (0 : E) 1 => f e * roundDivergence b W e) volume.toSphere :=
    (hfc.mul (sphere_roundDivergence_continuous b hU hSU hW)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz := integral_roundDivergence b hU hSU (hf.smul hW) (fun e he => by
    simp only [Pi.smul_apply', real_inner_smul_right, ht e he, mul_zero])
  simp only [Pi.smul_def'] at hz
  have hh : (∫ e : sphere (0 : E) 1, roundDivergence b (fun q => f q • W q) e ∂volume.toSphere) =
      (∫ e : sphere (0 : E) 1, fderiv ℝ f e (W e) ∂volume.toSphere) +
      (∫ e : sphere (0 : E) 1, f e * roundDivergence b W e ∂volume.toSphere) := by
    rw [← integral_add hi1 hi2]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro e
    exact roundDivergence_smul b
      ((hf.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
      ((hW.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp)) (ht e e.property)
  linarith

end AffineBernstein

end

end OAI
