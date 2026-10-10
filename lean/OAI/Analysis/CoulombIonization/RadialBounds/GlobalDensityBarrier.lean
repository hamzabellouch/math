import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

namespace CoulombPauli

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma memLp_tensor {u : A → ℂ} {v : B → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 ν) :
    MemLp (fun z : A × B => u z.1 * v z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hu.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu).mul_prod
      ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv)

omit [SFinite μ] in
lemma l2_norm_sq (u : Lp ℂ 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K]
  change (∫ a, ((‖u a‖ : ℝ) : ℂ)^2 ∂μ).re = _
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rfl

def tensor (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (memLp_tensor (Lp.memLp u) (Lp.memLp v)).toLp _

omit [SFinite μ] in
lemma tensor_ae (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensor u v =ᵐ[μ.prod ν] (fun z => u z.1 * v z.2) := MemLp.coeFn_toLp _

lemma tensor_norm_sq (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    ‖tensor u v‖^2 = ‖u‖^2 * ‖v‖^2 := by
  rw [l2_norm_sq, l2_norm_sq u, l2_norm_sq v]
  calc
    _ = ∫ z : A × B, ‖u z.1 * v z.2‖^2 ∂μ.prod ν :=
      integral_congr_ae ((tensor_ae u v).fun_comp (fun c : ℂ => ‖c‖^2))
    _ = _ := by
      simp only [norm_mul, mul_pow]
      exact integral_prod_mul (fun x => ‖u x‖^2) (fun y => ‖v y‖^2)

lemma tensor_norm (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : ‖tensor u v‖ = ‖u‖*‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
  simpa only [mul_pow] using tensor_norm_sq u v

omit [SFinite μ] in
lemma tensor_add_right (u : Lp ℂ 2 μ) (v w : Lp ℂ 2 ν) :
    tensor u (v+w) = tensor u v + tensor u w := by
  apply Lp.ext
  filter_upwards [tensor_ae u (v+w), tensor_ae u v, tensor_ae u w,
    Lp.coeFn_add (tensor u v) (tensor u w),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add v w)] with z h1 h2 h3 h4 h5
  simp only [h1,h2,h3,h4,h5, Pi.add_apply, mul_add]

omit [SFinite μ] in
lemma tensor_smul_right (u : Lp ℂ 2 μ) (c : ℂ) (v : Lp ℂ 2 ν) :
    tensor u (c • v) = c • tensor u v := by
  apply Lp.ext
  filter_upwards [tensor_ae u (c • v), tensor_ae u v,
    Lp.coeFn_smul c (tensor u v),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c v)] with z h1 h2 h3 h4
  simp only [h1,h2,h3,h4, Pi.smul_apply, smul_eq_mul]
  ring

def tensorLeft (u : Lp ℂ 2 μ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    ({ toFun := fun v => tensor u v
       map_add' := tensor_add_right u
       map_smul' := tensor_smul_right u } : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν))
    ‖u‖ (fun v => (tensor_norm u v).le)

lemma tensorLeft_apply (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : tensorLeft u v = tensor u v := rfl

lemma tensor_inner (u u' : Lp ℂ 2 μ) (v v' : Lp ℂ 2 ν) :
    ⟪tensor u v, tensor u' v'⟫_ℂ = ⟪u,u'⟫_ℂ * ⟪v,v'⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ z : A × B, ⟪u z.1,u' z.1⟫_ℂ * ⟪v z.2,v' z.2⟫_ℂ ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [tensor_ae u v, tensor_ae u' v'] with z h1 h2
      simp only [h1,h2,inner,star_mul]
      ring
    _ = _ := integral_prod_mul (L := ℂ) (fun x => ⟪u x,u' x⟫_ℂ) (fun y => ⟪v y,v' y⟫_ℂ)

lemma tensorLeft_adjoint_tensor (u u' : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    (tensorLeft u).adjoint (tensor u' v) = ⟪u,u'⟫_ℂ • v := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply, tensor_inner, inner_smul_right]

omit [SFinite μ] [SFinite ν] in
lemma integrable_eq_zero_of_rectangles {f : A × B → ℂ} (hf : Integrable f (μ.prod ν))
    (h : ∀ (s : Set A) (t : Set B), MeasurableSet s → MeasurableSet t →
      ∫ z in s ×ˢ t, f z ∂μ.prod ν = 0) : f =ᵐ[μ.prod ν] 0 := by
  apply hf.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  rw [withDensityᵥ_zero]
  apply VectorMeasure.ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [withDensityᵥ_apply hf MeasurableSet.univ]
    simpa only [Set.univ_prod_univ, zero_apply] using h Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    rw [withDensityᵥ_apply hf (hs.prod ht)]
    exact h s t hs ht

omit [SFinite μ] in
lemma tensor_indicator (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ⊤) (hνt : ν t ≠ ⊤) :
    tensor (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ)) =
      indicatorConstLp 2 (hs.prod ht) (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt) (1 : ℂ) := by
  classical
  apply Lp.ext
  filter_upwards [tensor_ae (indicatorConstLp 2 hs hμs (1 : ℂ))
    (indicatorConstLp 2 ht hνt (1 : ℂ)),
    Measure.quasiMeasurePreserving_fst.ae (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ))),
    Measure.quasiMeasurePreserving_snd.ae (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hνt) (c := (1 : ℂ))),
    indicatorConstLp_coeFn (p := 2) (hs := hs.prod ht)
      (hμs := by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt) (c := (1 : ℂ))] with z h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  by_cases hz : z.1 ∈ s <;> by_cases hz' : z.2 ∈ t <;> simp [hz, hz']

omit [SFinite μ] in
lemma rectangle_integral_eq_zero_of_tensor_orthogonal (ψ : Lp ℂ 2 (μ.prod ν))
    (hψ : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), ⟪tensor u v, ψ⟫_ℂ = 0)
    (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ⊤) (hνt : ν t ≠ ⊤) : ∫ z in s ×ˢ t, ψ z ∂μ.prod ν = 0 := by
  have h := hψ (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ))
  rw [tensor_indicator, L2.inner_indicatorConstLp_one] at h
  exact h

omit [SFinite μ] in
lemma rectangle_indicator_eq_zero_of_tensor_orthogonal (ψ : Lp ℂ 2 (μ.prod ν))
    (hψ : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), ⟪tensor u v, ψ⟫_ℂ = 0)
    (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ⊤) (hνt : ν t ≠ ⊤) :
    (s ×ˢ t).indicator (fun z => ψ z) =ᵐ[μ.prod ν] 0 := by
  classical
  have hR : (μ.prod ν) (s ×ˢ t) ≠ ⊤ := by
    rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμs hνt
  apply integrable_eq_zero_of_rectangles
    ((integrableOn_Lp_of_measure_ne_top ψ (by norm_num) hR).integrable_indicator (hs.prod ht))
  intro s' t' hs' ht'
  rw [setIntegral_indicator (hs.prod ht), Set.prod_inter_prod]
  exact rectangle_integral_eq_zero_of_tensor_orthogonal ψ hψ (s' ∩ s) (t' ∩ t)
    (hs'.inter hs) (ht'.inter ht)
    ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.2 hμs)).ne
    ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.2 hνt)).ne

omit [SFinite μ] in
lemma eq_zero_of_tensor_orthogonal [SigmaFinite μ] [SigmaFinite ν]
    (ψ : Lp ℂ 2 (μ.prod ν))
    (hψ : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), ⟪tensor u v, ψ⟫_ℂ = 0) : ψ = 0 := by
  have hzero : ∀ᵐ z ∂μ.prod ν, ∀ n m : ℕ,
      (spanningSets μ n ×ˢ spanningSets ν m).indicator (fun z => ψ z) z = 0 := by
    apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro m
    exact rectangle_indicator_eq_zero_of_tensor_orthogonal ψ hψ _ _
      (measurableSet_spanningSets μ n) (measurableSet_spanningSets ν m)
      (measure_spanningSets_lt_top μ n).ne (measure_spanningSets_lt_top ν m).ne
  apply Lp.ext
  filter_upwards [hzero, Lp.coeFn_zero ℂ 2 (μ.prod ν)] with z hz h0
  have ha : z.1 ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; trivial
  have hb : z.2 ∈ ⋃ m, spanningSets ν m := by rw [iUnion_spanningSets]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ha
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hb
  have hz' := hz n m
  rw [Set.indicator_of_mem (show z ∈ spanningSets μ n ×ˢ spanningSets ν m from ⟨hn, hm⟩)] at hz'
  simpa only [h0, Pi.zero_apply] using hz'

omit [SFinite μ] in
lemma continuousLinearMap_ext_tensor [SigmaFinite μ] [SigmaFinite ν]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F G : Lp ℂ 2 (μ.prod ν) →L[ℂ] H)
    (h : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), F (tensor u v) = G (tensor u v)) : F = G := by
  have hz (w : H) : (F-G).adjoint w = 0 := by
    apply eq_zero_of_tensor_orthogonal
    intro u v
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [sub_apply, h u v, sub_self, inner_zero_left]
  ext x
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change ⟪(F-G) x, (F-G) x⟫_ℂ = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_right]

end CoulombPauli

end

end OAI
