import OAI.GroupTheory.Kervaire.SpectralMeasures

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open KervaireStrong

theorem exists_phaseOperator (U : Operator H) (hU : U ∈ unitary (Operator H)) :
    letI := isStarNormal_of_mem_unitary hU
    ∃ B : Operator H, 0 ≤ B ∧ B ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      NormedSpace.exp ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) • B) = U ∧
      (∀ ξ, (inner ℂ ξ (B ξ)).re = vectorPhase U ξ) ∧
      ∀ R, Commute U R → Commute (star U) R → Commute B R := by
  let hN := isStarNormal_of_mem_unitary hU
  let := hN
  let f (n : ℕ) : C(spectrum ℂ U, ℂ) := complexify (phaseApprox U hU n)
  have hb : ∀ n z, ‖f n z‖ ≤ 1 := by
    intro n z
    simp only [f, complexify_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (phaseApprox_nonneg U hU n z)]
    exact phaseApprox_le_one U hU n z
  have ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (phase z : ℂ)) := by
    intro z
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_phaseApprox U hU z)
  obtain ⟨B, hB, hnormB⟩ := exists_strongLimit U f (fun z => (phase z : ℂ)) 1 zero_le_one hb ht
  have hbs : StrongTendsto (fun n => cfcHom hN (f n)) atTop B := hB
  have hnorm : ∀ n, ‖cfcHom hN (f n)‖ ≤ 1 := by
    intro n
    rw [norm_cfcHom U (f n) hN]
    exact ((f n).norm_le zero_le_one).mpr (hb n)
  have hpos : 0 ≤ B := hbs.nonneg fun n =>
    (cfcHom_nonneg_iff hN).mpr fun z =>
      (Complex.zero_le_real).mpr (phaseApprox_nonneg U hU n z)
  have hle : B ≤ 1 := by
    apply sub_nonneg.mp
    apply KervaireStrong.StrongTendsto.nonneg (T := fun n => 1 - cfcHom hN (f n))
      (l := atTop)
    · intro ξ
      simpa only [sub_apply] using (tendsto_const_nhds (x := (1 : Operator H) ξ)).sub (hB ξ)
    · intro n
      have hn : 0 ≤ cfcHom hN (1 - f n) := by
        apply (cfcHom_nonneg_iff hN).mpr
        intro z
        change 0 ≤ 1 - (phaseApprox U hU n z : ℂ)
        exact sub_nonneg.mpr (by exact_mod_cast phaseApprox_le_one U hU n z)
      simpa only [map_sub, map_one] using hn
  refine ⟨B, hpos, hle, hnormB, ?_, ?_, ?_⟩
  · let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
    have hcbs : StrongTendsto (fun n => c • cfcHom hN (f n)) atTop (c • B) := by
      intro ξ
      exact (hB ξ).const_smul c
    have hcb : ∀ n, ‖c • cfcHom hN (f n)‖ ≤ ‖c‖ := by
      intro n
      rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg c)
    have hexp := hcbs.exp (norm_nonneg c) hcb
    have heq (n : ℕ) : NormedSpace.exp (c • cfcHom hN (f n)) =
        cfcHom hN (expMap (c • f n)) := by
      rw [← map_smul]
      exact (calculus_expMap U (c • f n)).symm
    let g : C(spectrum ℂ U, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
    have hgb : ∀ n z, ‖expMap (c • f n) z‖ ≤ 1 := by
      intro n z
      simp [expMap, f, complexify, c, Complex.norm_exp, Complex.mul_re]
    have hgt : ∀ z, Tendsto (fun n => expMap (c • f n) z) atTop (𝓝 (g z)) := by
      intro z
      have hz := Complex.continuous_exp.continuousAt.tendsto.comp ((ht z).const_mul c)
      have he : Complex.exp (c * (phase z : ℂ)) = (z : ℂ) := by
        convert exp_phase (CStarRing.norm_of_mem_unitary
          (spectrum_subset_unitary_of_mem_unitary hU z.property)) using 1
        · congr 1
          simp only [c, Complex.ofReal_mul]
          ring
      simpa only [expMap, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
        smul_eq_mul, Function.comp_def, he, g, ContinuousMap.restrict_apply,
        ContinuousMap.id_apply] using hz
    have hexpU := tendsto_calculus U (fun n => expMap (c • f n)) g 1 zero_le_one hgb hgt
    apply ContinuousLinearMap.ext
    intro ξ
    apply tendsto_nhds_unique (hexp ξ)
    simpa only [heq, g, cfcHom_id] using hexpU ξ
  · intro ξ
    have ht1 := Complex.continuous_re.continuousAt.tendsto.comp
      (Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := ξ)) (hB ξ))
    have ht2 := tendsto_integral_phaseApprox U hU ξ
    simp_rw [integral_vectorMeasure] at ht2
    exact tendsto_nhds_unique ht1 ht2
  · intro R hR hRstar
    exact hbs.commute fun n => hR.cfcHom hN hRstar (f n)

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The continuous vector functional on all bounded operators. -/
def vectorCLM (ξ : H) : Operator H →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

omit [CompleteSpace H] in
@[simp] theorem vectorCLM_apply (ξ : H) (T : Operator H) :
    vectorCLM ξ T = inner ℂ ξ (T ξ) := rfl

/-- The vector functional respects the star, without a trace assumption. -/
theorem vectorCLM_star (ξ : H) (T : Operator H) :
    vectorCLM ξ (star T) = star (vectorCLM ξ T) := by
  simp only [vectorCLM_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

/-- Real continuous spectral functions have real vector expectations. -/
theorem vectorCLM_complexify_real (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℝ)) :
    (((vectorCLM ξ (cfcHom hU (complexify f))).re : ℝ) : ℂ) =
      vectorCLM ξ (cfcHom hU (complexify f)) := by
  apply Complex.conj_eq_iff_re.mp
  change star (vectorCLM ξ (cfcHom hU (complexify f))) = _
  rw [← vectorCLM_star, ← map_star]
  congr 2
  ext z
  simp [complexify]

/-- Every continuous function on the compact spectral space is integrable. -/
theorem integrable_continuous_map {E : Type*} [NormedAddCommGroup E]
    (U : Operator H) [IsStarNormal U] (ξ : H) (f : C(spectrum ℂ U, E)) :
    Integrable f (vectorMeasure U ξ) := by
  apply Integrable.mono' (integrable_const ‖f‖) f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall f.norm_coe_le_norm

/-- The scalar spectral measure integrates complex functions as well as real ones. -/
theorem integral_vectorMeasure_complex (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, f z ∂vectorMeasure U ξ = vectorCLM ξ (cfcHom hU f) := by
  let fr : C(spectrum ℂ U, ℝ) := ⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(spectrum ℂ U, ℝ) := ⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩
  have hf : f = complexify fr + Complex.I • complexify fi := by
    ext z
    change f z = ((f z).re : ℂ) + Complex.I * ((f z).im : ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (f z)).symm
  have hr := integrable_continuous_map U ξ (complexify fr)
  have hi := integrable_continuous_map U ξ (complexify fi)
  change Integrable (fun z => (fr z : ℂ)) (vectorMeasure U ξ) at hr
  change Integrable (fun z => (fi z : ℂ)) (vectorMeasure U ξ) at hi
  rw [hf, map_add, map_smul, map_add, map_smul]
  change (∫ z, (fr z : ℂ) + Complex.I • (fi z : ℂ) ∂vectorMeasure U ξ) = _
  have hi' : Integrable (fun z => Complex.I • (fi z : ℂ)) (vectorMeasure U ξ) := by
    exact integrable_continuous_map U ξ (Complex.I • complexify fi)
  rw [integral_add hr hi', integral_smul]
  simp only [integral_complex_ofReal, integral_vectorMeasure,
    ← vectorCLM_apply, vectorCLM_complexify_real]

end KervaireSpectral

end

end OAI
