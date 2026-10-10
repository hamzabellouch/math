import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.FlowLinearization
open scoped ContDiff Topology
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem derivative_spatial_derivative_at_zero (V : E → E) (Φ : ℝ × E → E)
    (hΦ : ContDiff ℝ ∞ Φ) (hzero : ∀ x, Φ (0, x) = x)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (V (Φ (t, x))) t) (p : E) :
    HasDerivAt (fun t => fderiv ℝ (fun x => Φ (t, x)) p) (fderiv ℝ V p) 0 := by
  let D := fderiv ℝ Φ
  let A := fderiv ℝ D (0, p)
  let L : ((ℝ × E) →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip (ContinuousLinearMap.inr ℝ ℝ E)
  let T : ((ℝ × E) →L[ℝ] E) →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ E (1, 0)
  have hD : ContDiff ℝ ∞ D := (contDiff_infty_iff_fderiv.mp hΦ).2
  have ht : ∀ t, fderiv ℝ (fun x => Φ (t, x)) p = L (D (t, p)) := by
    intro t
    exact ((hΦ.differentiable (by simp) (t, p)).hasFDerivAt.comp p
      (hasFDerivAt_prodMk_right t p)).fderiv
  have hB : ∀ x, T (D (0, x)) = V x := by
    intro x
    have h1 := ((hΦ.differentiable (by simp) (0, x)).hasFDerivAt.comp (0 : ℝ)
      (hasFDerivAt_prodMk_left (0 : ℝ) x)).hasDerivAt
    have h2 := hODE 0 x
    rw [hzero x] at h2
    exact h1.unique h2
  have hV : fderiv ℝ V p = (T.comp A).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hb := (T.hasFDerivAt.comp (0, p)
      ((hD.differentiable (by simp) (0, p)).hasFDerivAt)).comp p
      (hasFDerivAt_prodMk_right (0 : ℝ) p)
    have he : V = T ∘ D ∘ (fun x : E => ((0 : ℝ), x)) := funext (fun x => (hB x).symm)
    rw [he]
    exact hb.fderiv
  have hJ := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (((hD.differentiable (by simp) (0, p)).hasFDerivAt.comp (0 : ℝ)
      (hasFDerivAt_prodMk_left (0 : ℝ) p)).hasDerivAt)
  have hsym := (hΦ.contDiffAt (x := (0, p))).isSymmSndFDerivAt (show minSmoothness ℝ 2 ≤ ∞ by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have heq : L (A (1, 0)) = fderiv ℝ V p := by
    rw [hV]
    ext v
    exact hsym (1, 0) (0, v)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at hJ
  change HasDerivAt (fun t => L (D (t, p))) (L (A (1, 0))) 0 at hJ
  rw [heq] at hJ
  exact hJ.congr_of_eventuallyEq (Filter.Eventually.of_forall ht)

omit [CompleteSpace E] in
theorem derivative_spatial_derivative_at_zero_local (V : E → E) (Φ : ℝ × E → E)
    (p : E) (hΦ : ContDiffAt ℝ ∞ Φ (0, p))
    (hzero : ∀ᶠ x in 𝓝 p, Φ (0, x) = x)
    (hODE : ∀ᶠ x in 𝓝 p, HasDerivAt (fun s => Φ (s, x)) (V (Φ (0, x))) 0) :
    HasDerivAt (fun t => fderiv ℝ (fun x => Φ (t, x)) p) (fderiv ℝ V p) 0 := by
  let D := fderiv ℝ Φ
  let A := fderiv ℝ D (0, p)
  let L : ((ℝ × E) →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip (ContinuousLinearMap.inr ℝ ℝ E)
  let T : ((ℝ × E) →L[ℝ] E) →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ E (1, 0)
  have hD : ContDiffAt ℝ 1 D (0, p) := hΦ.fderiv_right (by
    change (2 : ℕ∞ω) ≤ ∞
    exact WithTop.coe_le_coe.mpr le_top)
  have hdiff : ∀ᶠ q in 𝓝 ((0 : ℝ), p), DifferentiableAt ℝ Φ q := by
    filter_upwards [(hΦ.of_le (show (1 : ℕ∞ω) ≤ ∞ by norm_num)).eventually (by simp)] with q hq
    exact hq.differentiableAt one_ne_zero
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), fderiv ℝ (fun x => Φ (t, x)) p = L (D (t, p)) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hdiff] with t ht
    exact (ht.hasFDerivAt.comp p (hasFDerivAt_prodMk_right t p)).fderiv
  have hB : (fun x => T (D (0, x))) =ᶠ[𝓝 p] V := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hdiff, hODE, hzero] with x hx hODE hx0
    have h1 := (hx.hasFDerivAt.comp (0 : ℝ)
      (hasFDerivAt_prodMk_left (0 : ℝ) x)).hasDerivAt
    rw [hx0] at hODE
    exact h1.unique hODE
  have hV : fderiv ℝ V p = (T.comp A).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hb := (T.hasFDerivAt.comp (0, p)
      ((hD.differentiableAt one_ne_zero).hasFDerivAt)).comp p
      (hasFDerivAt_prodMk_right (0 : ℝ) p)
    exact (hb.congr_of_eventuallyEq hB.symm).fderiv
  have hJ := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (((hD.differentiableAt one_ne_zero).hasFDerivAt.comp (0 : ℝ)
      (hasFDerivAt_prodMk_left (0 : ℝ) p)).hasDerivAt)
  have hsym := hΦ.isSymmSndFDerivAt (show minSmoothness ℝ 2 ≤ ∞ by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have heq : L (A (1, 0)) = fderiv ℝ V p := by
    rw [hV]
    ext v
    exact hsym (1, 0) (0, v)
  change HasDerivAt (fun t => L (D (t, p))) (L (A (1, 0))) 0 at hJ
  rw [heq] at hJ
  exact hJ.congr_of_eventuallyEq ht

theorem sub_one_isUnit_small {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] (f : ℝ → R) (A : R) (hf : HasDerivAt f A 0)
    (h0 : f 0 = 1) (hA : IsUnit A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → IsUnit (f t - 1) := by
  have ht : Tendsto (fun t : ℝ => t⁻¹ • (f t - 1)) (𝓝[≠] 0) (𝓝 A) := by
    have h := hf.tendsto_slope
    change Tendsto (fun t => slope f 0 t) _ _ at h
    simpa only [slope_def_module, sub_zero, h0] using h
  have he : ∀ᶠ t : ℝ in 𝓝[≠] 0, IsUnit (t⁻¹ • (f t - 1)) :=
    ht (Units.isOpen.mem_nhds hA)
  obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ
  have hscaled : IsUnit (t⁻¹ • (f t - 1)) := by
    apply hsub
    refine ⟨hball ?_, ?_⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0] using htδ
    · simpa using ht0.ne'
  have htu : IsUnit (algebraMap ℝ R t) :=
    (isUnit_iff_ne_zero.mpr ht0.ne').map (algebraMap ℝ R)
  have h := htu.mul hscaled
  rw [← Algebra.smul_def, smul_inv_smul₀ ht0.ne'] at h
  exact h

theorem small_time_nondegenerate (V : E → E) (Φ : ℝ × E → E)
    (hΦ : ContDiff ℝ ∞ Φ) (hzero : ∀ x, Φ (0, x) = x)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (V (Φ (t, x))) t)
    (p : E) (hA : IsUnit (fderiv ℝ V p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      IsUnit (fderiv ℝ (fun x => Φ (t, x)) p - ContinuousLinearMap.id ℝ E) := by
  apply sub_one_isUnit_small (fun t => fderiv ℝ (fun x => Φ (t, x)) p) (fderiv ℝ V p)
    (derivative_spatial_derivative_at_zero V Φ hΦ hzero hODE p) _ hA
  have he : (fun x => Φ ((0 : ℝ), x)) = id := funext hzero
  rw [he, fderiv_id]
  rfl

theorem small_time_nondegenerate_local (V : E → E) (Φ : ℝ × E → E)
    (p : E) (hΦ : ContDiffAt ℝ ∞ Φ (0, p))
    (hzero : ∀ᶠ x in 𝓝 p, Φ (0, x) = x)
    (hODE : ∀ᶠ x in 𝓝 p, HasDerivAt (fun s => Φ (s, x)) (V (Φ (0, x))) 0)
    (hA : IsUnit (fderiv ℝ V p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      IsUnit (fderiv ℝ (fun x => Φ (t, x)) p - ContinuousLinearMap.id ℝ E) := by
  apply sub_one_isUnit_small (fun t => fderiv ℝ (fun x => Φ (t, x)) p) (fderiv ℝ V p)
    (derivative_spatial_derivative_at_zero_local V Φ p hΦ hzero hODE) _ hA
  have he : (fun x => Φ ((0 : ℝ), x)) =ᶠ[𝓝 p] id := hzero
  rw [he.fderiv_eq, fderiv_id]
  rfl

theorem hamiltonian_field_derivative_isUnit [FiniteDimensional ℝ E]
    (F : E → ℝ) (V : E → E) (omega : E → E →L[ℝ] E →L[ℝ] ℝ)
    (p : E) (hV : DifferentiableAt ℝ V p) (hω : DifferentiableAt ℝ omega p)
    (hωn : Function.Injective (omega p))
    (hHam : ∀ x, omega x (V x) = fderiv ℝ F x)
    (hp : fderiv ℝ F p = 0)
    (hH : Function.Injective (fderiv ℝ (fderiv ℝ F) p)) :
    IsUnit (fderiv ℝ V p) := by
  have hVp : V p = 0 := hωn (by rw [hHam, hp, map_zero])
  have hder := hω.hasFDerivAt.clm_apply hV.hasFDerivAt
  simp only [hVp, map_zero, add_zero] at hder
  have he : (fun x => omega x (V x)) = fderiv ℝ F := funext hHam
  rw [he] at hder
  have hessian := hder.fderiv
  have hinj : Function.Injective (fderiv ℝ V p) := by
    intro u v huv
    apply hH
    rw [hessian]
    simp only [ContinuousLinearMap.comp_apply, huv]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (fderiv ℝ V p).toLinearMap)).mp hinj⟩

theorem small_time_nondegenerate_hamiltonian [FiniteDimensional ℝ E]
    (F : E → ℝ) (V : E → E) (omega : E → E →L[ℝ] E →L[ℝ] ℝ)
    (Φ : ℝ × E → E) (hΦ : ContDiff ℝ ∞ Φ)
    (hzero : ∀ x, Φ (0, x) = x)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (V (Φ (t, x))) t)
    (p : E) (hV : DifferentiableAt ℝ V p) (hω : DifferentiableAt ℝ omega p)
    (hωn : Function.Injective (omega p))
    (hHam : ∀ x, omega x (V x) = fderiv ℝ F x)
    (hp : fderiv ℝ F p = 0)
    (hH : Function.Injective (fderiv ℝ (fderiv ℝ F) p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      IsUnit (fderiv ℝ (fun x => Φ (t, x)) p - ContinuousLinearMap.id ℝ E) :=
  small_time_nondegenerate V Φ hΦ hzero hODE p
    (hamiltonian_field_derivative_isUnit F V omega p hV hω hωn hHam hp hH)

end MorseArnold.FlowLinearization

end

end OAI
