import OAI.Probability.InvariantIsing.Haar.PlaneRotation
import OAI.Probability.InvariantIsing.Core.Ward

namespace OAI

/-! Genuine coordinate-plane rotations and infinitesimal Haar invariance on
`SO(N)`, the rotation group used by the actual enriched model. -/

noncomputable section

open MeasureTheory Filter IsingPerceptron
open scoped Topology Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

/-- Forget only the determinant-one condition. -/
def specialToOrthogonal {N : ℕ} : SpecialOrthogonal N →* Orthogonal N where
  toFun U := ⟨U.val, (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma matrixRotation_specialToOrthogonal {N : ℕ} (U : SpecialOrthogonal N) :
    matrixRotation (specialToOrthogonal U) = specialRotation U := rfl

lemma measurable_specialToOrthogonal {N : ℕ} :
    Measurable (specialToOrthogonal : SpecialOrthogonal N → Orthogonal N) :=
  measurable_subtype_coe.subtype_mk

/-- Orthogonal determinants have only two possible real values. -/
lemma orthogonal_det_eq_one_or_neg_one {N : ℕ} (U : Orthogonal N) :
    (U : Matrix (Fin N) (Fin N) ℝ).det = 1 ∨
      (U : Matrix (Fin N) (Fin N) ℝ).det = -1 := by
  apply mul_self_eq_one_iff.mp
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp U.property)
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using h

/-- A continuous plane-rotation path starts at determinant one and cannot
switch between the two orthogonal determinant values. -/
lemma planeRotation_det {N : ℕ} (i j : Fin N) (t : ℝ) :
    (planeRotation i j t : Matrix (Fin N) (Fin N) ℝ).det = 1 := by
  let f : ℝ → ℝ := fun s => (planeRotation i j s : Matrix (Fin N) (Fin N) ℝ).det
  have hc : Continuous f := by
    apply Continuous.matrix_det
    exact continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_exp_smul_const' (planeGenerator i j) s).continuousAt
  have hm : Set.MapsTo f Set.univ ({1, -1} : Set ℝ) := by
    intro s _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, f] using
      orthogonal_det_eq_one_or_neg_one (planeRotation i j s)
  have he : f t = f 0 := isPreconnected_univ.constant_of_mapsTo
    (Set.toFinite ({1, -1} : Set ℝ)).isDiscrete hc.continuousOn hm (Set.mem_univ t)
      (Set.mem_univ 0)
  simpa only [f, planeRotation_zero, OneMemClass.coe_one, Matrix.det_one] using he

/-- The same matrix exponential, now as an element of the special orthogonal group. -/
def specialPlaneRotation {N : ℕ} (i j : Fin N) (t : ℝ) : SpecialOrthogonal N :=
  ⟨(planeRotation i j t).val,
    Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨(planeRotation i j t).property, planeRotation_det i j t⟩⟩

@[simp] lemma specialPlaneRotation_zero {N : ℕ} (i j : Fin N) :
    specialPlaneRotation i j 0 = 1 := by
  apply Subtype.ext
  change (planeRotation i j 0 : Matrix (Fin N) (Fin N) ℝ) = 1
  simp only [planeRotation_zero, OneMemClass.coe_one]

@[simp] lemma specialToOrthogonal_planeRotation {N : ℕ} (i j : Fin N) (t : ℝ) :
    specialToOrthogonal (specialPlaneRotation i j t) = planeRotation i j t := rfl

/-- A dominated infinitesimal left rotation has Haar mean zero. -/
lemma integral_special_rotation_derivative_eq_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [μ.IsMulLeftInvariant] (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    (f : SpecialOrthogonal N → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (f' : ℝ → SpecialOrthogonal N → ℝ) (hf' : AEStronglyMeasurable (f' 0) μ)
    (B : SpecialOrthogonal N → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ B U)
    (hderiv : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t) :
    ∫ U, f' 0 U ∂μ = 0 := by
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun U => f (R t * U)) μ := by
    apply Filter.Eventually.of_forall
    intro t
    have hmul : Measurable (fun U : SpecialOrthogonal N => R t * U) := by
      apply Measurable.subtype_mk
      change Measurable (fun U : SpecialOrthogonal N =>
        (R t : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ))
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      simp only [Matrix.mul_apply]
      exact Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply j).comp
          ((measurable_pi_apply k).comp measurable_subtype_coe))
    exact (hf.comp hmul).aestronglyMeasurable
  have hi : Integrable (fun U => f (R 0 * U)) μ := by simpa only [hR, one_mul] using hfi
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hf'
    hbound hB hderiv
  have he : (fun t => ∫ U, f (R t * U) ∂μ) = fun _ : ℝ => ∫ U, f U ∂μ := by
    funext t
    exact integral_mul_left_eq_self f (R t)
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (∫ U, f U ∂μ))


variable {S : Type*} [Fintype S]

/-- Exact finite-volume Haar Ward identity. All regularity assumptions concern
finite-dimensional derivatives; none assumes a limiting overlap identity. -/
theorem integral_special_gibbs_rotation_identity {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    {w : S → ℝ} (hw : GibbsReference w)
    (H A : SpecialOrthogonal N → S → ℝ)
    (hHm : ∀ σ, Measurable (fun U => H U σ))
    (hAm : ∀ σ, Measurable (fun U => A U σ))
    (dH dA : ℝ → SpecialOrthogonal N → S → ℝ)
    (hdHm : ∀ σ, Measurable (fun U => dH 0 U σ))
    (hdAm : ∀ σ, Measurable (fun U => dA 0 U σ))
    (hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => H (R s * U) σ) (dH t U σ) t)
    (hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => A (R s * U) σ) (dA t U σ) t)
    (K L M : ℝ) (hK : 0 ≤ K)
    (hAb : ∀ U σ, |A U σ| ≤ K)
    (hdHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dH t U σ| ≤ L)
    (hdAb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dA t U σ| ≤ M) :
    (∫ U, gibbsAverage w (H U) (dA 0 U) +
      gibbsAverage w (H U) (fun σ => A U σ * dH 0 U σ) -
      gibbsAverage w (H U) (A U) * gibbsAverage w (H U) (dH 0 U) ∂μ) = 0 := by
  let f : SpecialOrthogonal N → ℝ := fun U => gibbsAverage w (H U) (A U)
  let f' : ℝ → SpecialOrthogonal N → ℝ := fun t U =>
    gibbsAverage w (H (R t * U)) (dA t U) +
      gibbsAverage w (H (R t * U)) (fun σ => A (R t * U) σ * dH t U σ) -
      gibbsAverage w (H (R t * U)) (A (R t * U)) *
        gibbsAverage w (H (R t * U)) (dH t U)
  have hm : Measurable f := measurable_gibbsAverage w H A hHm hAm
  have hi : Integrable f μ := (integrable_const K).mono' hm.aestronglyMeasurable
    (ae_of_all μ fun U => by
      simpa only [Real.norm_eq_abs] using
        (abs_gibbsAverage_le hw (H U) (A U) (hAb U)))
  have hm' : Measurable (f' 0) := by
    simp only [f', hR, one_mul]
    exact ((measurable_gibbsAverage w H (dA 0) hHm hdAm).add
      (measurable_gibbsAverage w H (fun U σ => A U σ * dH 0 U σ) hHm
        (fun σ => (hAm σ).mul (hdHm σ)))).sub
      ((measurable_gibbsAverage w H A hHm hAm).mul
        (measurable_gibbsAverage w H (dH 0) hHm hdHm))
  have hb : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ M + 2 * K * L := by
    exact ae_of_all _ fun U t ht => by
      simpa only [f', Real.norm_eq_abs] using
        abs_gibbsVariation_le hw (H (R t * U)) (A (R t * U)) (dH t U) (dA t U)
          hK (hAb _) (hdHb U t ht) (hdAb U t ht)
  have hd : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t :=
    ae_of_all _ fun U t ht => hasDerivAt_gibbsAverage hw (hHd U t ht) (hAd U t ht)
  have he := integral_special_rotation_derivative_eq_zero μ R hR f hm hi f'
    hm'.aestronglyMeasurable (fun _ => M + 2 * K * L) (integrable_const _) hb hd
  simpa only [f', hR, one_mul] using he


end InvariantIsing

end

end OAI
