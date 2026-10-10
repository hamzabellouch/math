import OAI.Dynamics.MultipleMixing.Joinings

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory
open scoped InnerProductSpace
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma memLp_tensor (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    MemLp (fun p : X × Y => g p.1 * h p.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((g.1.stronglyMeasurable.comp_measurable measurable_fst).mul
      (h.1.stronglyMeasurable.comp_measurable measurable_snd)).aestronglyMeasurable).mpr
  change Integrable (fun p : X × Y => ‖g p.1 * h p.2‖ ^ 2) (μ.prod ν)
  simp only [norm_mul, mul_pow]
  exact ((Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_prod
    ((Lp.memLp h).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

def tensorLp (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (memLp_tensor g h).toLp _

omit [SFinite μ] in
lemma coe_tensorLp (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    (tensorLp g h : X × Y → ℂ) =ᵐ[μ.prod ν] (fun p => g p.1 * h p.2) :=
  MemLp.coeFn_toLp _

lemma tensorLp_inner (g g' : Lp ℂ 2 μ) (h h' : Lp ℂ 2 ν) :
    inner ℂ (tensorLp g h) (tensorLp g' h') = inner ℂ g g' * inner ℂ h h' := by
  rw [L2.inner_def, L2.inner_def g g', L2.inner_def h h', ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [coe_tensorLp g h, coe_tensorLp g' h'] with p hp hp'
  rw [hp, hp']
  simp only [RCLike.inner_apply, map_mul]
  ring

lemma tensorLp_norm (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    ‖tensorLp g h‖ = ‖g‖ * ‖h‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), tensorLp_inner]
  simp only [inner_self_eq_norm_sq_to_K]
  change ((‖g‖ : ℂ) ^ 2 * (‖h‖ : ℂ) ^ 2).re = _
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_pow]

omit [SFinite μ] in
lemma tensorLp_add_left (g g' : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    tensorLp (g + g') h = tensorLp g h + tensorLp g' h := by
  apply Lp.ext
  have hf : Measure.QuasiMeasurePreserving Prod.fst (μ.prod ν) μ :=
    Measure.quasiMeasurePreserving_fst
  filter_upwards [coe_tensorLp (g + g') h, coe_tensorLp g h, coe_tensorLp g' h,
    Lp.coeFn_add (tensorLp g h) (tensorLp g' h), hf.ae (Lp.coeFn_add g g')]
      with p ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, hb, hc, he, add_mul]

omit [SFinite μ] in
lemma tensorLp_smul_left (c : ℂ) (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    tensorLp (c • g) h = c • tensorLp g h := by
  apply Lp.ext
  have hf : Measure.QuasiMeasurePreserving Prod.fst (μ.prod ν) μ :=
    Measure.quasiMeasurePreserving_fst
  filter_upwards [coe_tensorLp (c • g) h, coe_tensorLp g h,
    Lp.coeFn_smul c (tensorLp g h), hf.ae (Lp.coeFn_smul c g)] with p ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hc, hb, hd]
  simp only [smul_eq_mul, mul_assoc]

omit [SFinite μ] in
lemma tensorLp_add_right (g : Lp ℂ 2 μ) (h h' : Lp ℂ 2 ν) :
    tensorLp g (h + h') = tensorLp g h + tensorLp g h' := by
  apply Lp.ext
  have hf : Measure.QuasiMeasurePreserving Prod.snd (μ.prod ν) ν :=
    Measure.quasiMeasurePreserving_snd
  filter_upwards [coe_tensorLp g (h + h'), coe_tensorLp g h, coe_tensorLp g h',
    Lp.coeFn_add (tensorLp g h) (tensorLp g h'), hf.ae (Lp.coeFn_add h h')]
      with p ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, hb, hc, he, mul_add]

omit [SFinite μ] in
lemma tensorLp_smul_right (c : ℂ) (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    tensorLp g (c • h) = c • tensorLp g h := by
  apply Lp.ext
  have hf : Measure.QuasiMeasurePreserving Prod.snd (μ.prod ν) ν :=
    Measure.quasiMeasurePreserving_snd
  filter_upwards [coe_tensorLp g (c • h), coe_tensorLp g h,
    Lp.coeFn_smul c (tensorLp g h), hf.ae (Lp.coeFn_smul c h)] with p ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hc, hb, hd]
  simp only [smul_eq_mul]
  ring

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω}
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  [SFinite η] [SFinite ρ]

def contraction (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) : Lp ℂ 2 ν :=
  operator hx huy (tensorLp g h)

lemma contraction_norm_le (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) : ‖contraction hx huy g h‖ ≤ ‖g‖ * ‖h‖ := by
  calc
    _ ≤ ‖operator hx huy‖ * ‖tensorLp g h‖ := (operator hx huy).le_opNorm _
    _ ≤ ‖tensorLp g h‖ := by grw [operator_norm_le]; simp
    _ = _ := tensorLp_norm g h

omit [SFinite η] in
lemma contraction_inner (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (f : Lp ℂ 2 ν) (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    inner ℂ f (contraction hx huy g h) =
      ∫ ω, g (u ω) * inner ℂ (f (x ω)) (h (y ω)) ∂μ := by
  rw [contraction, inner_operator]
  apply integral_congr_ae
  filter_upwards [huy.quasiMeasurePreserving.ae (coe_tensorLp g h)] with ω hω
  rw [hω]
  simp only [RCLike.inner_apply]
  ring

omit [SFinite η] in
lemma contraction_integrand (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (f : Lp ℂ 2 ν) (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    Integrable (fun ω => g (u ω) * inner ℂ (f (x ω)) (h (y ω))) μ := by
  apply (integrable_inner_comp hx huy f (tensorLp g h)).congr
  filter_upwards [huy.quasiMeasurePreserving.ae (coe_tensorLp g h)] with ω hω
  rw [hω]
  simp only [RCLike.inner_apply]
  ring

variable [IsFiniteMeasure η] [SecondCountableTopology (Lp ℂ 2 ν)]
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]

omit [SFinite η] [SFinite ρ] [IsMarkovKernel κ] in
lemma family_weight_integrable
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    Integrable (fun a => g a • family κ ν ρ a h) η := by
  apply ((Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).smul_bdd ‖h‖
    (family_aestronglyMeasurable hm h)
  filter_upwards with a
  calc
    _ ≤ ‖family κ ν ρ a‖ * ‖h‖ := (family κ ν ρ a).le_opNorm h
    _ ≤ _ := by grw [family_norm_le]; simp

omit [SFinite η] in
lemma contraction_integral (hu : MeasurePreserving u μ η)
    (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    contraction hx huy g h = ∫ a, g a • family κ ν ρ a h ∂η := by
  have : IsFiniteMeasure (μ.map u) := hu.map_eq.symm ▸ inferInstance
  apply ext_inner_left ℂ
  intro f
  rw [contraction_inner, ← integral_inner (family_weight_integrable hm g h)]
  let F : U × (X × Y) → ℂ := fun p => g p.1 * inner ℂ (f p.2.1) (h p.2.2)
  have hFm : StronglyMeasurable F :=
    (g.1.stronglyMeasurable.comp_measurable (by fun_prop)).mul
      ((f.1.stronglyMeasurable.comp_measurable (by fun_prop)).inner
        (h.1.stronglyMeasurable.comp_measurable (by fun_prop)))
  have hFi : Integrable F (μ.map u ⊗ₘ κ) := by
    rw [← hκ.map_eq]
    apply (integrable_map_measure hFm.aestronglyMeasurable hκ.aemeasurable).mpr
    exact contraction_integrand hx huy f g h
  calc
    _ = ∫ p, F p ∂μ.map u ⊗ₘ κ := hκ.integral_comp hFm.aestronglyMeasurable
    _ = ∫ a, ∫ p, F (a,p) ∂κ a ∂μ.map u := Measure.integral_compProd hFi
    _ = ∫ a, g a * (∫ p, inner ℂ (f p.1) (h p.2) ∂κ a) ∂η := by
      rw [hu.map_eq]
      simp only [F, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [family_inner hm f h] with a ha
      rw [inner_smul_right, ha]

omit [SFinite η] in
lemma contraction_projection (hu : MeasurePreserving u μ η)
    (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω, y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hPQ : ∀ᵐ a ∂η, P ∘L family κ ν ρ a = family κ ν ρ a ∘L Q)
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    P (contraction hx huy g h) = contraction hx huy g (Q h) := by
  rw [contraction_integral hu hx huy hκ hm,
    contraction_integral hu hx huy hκ hm,
    ← P.integral_comp_comm (family_weight_integrable hm g h)]
  apply integral_congr_ae
  filter_upwards [hPQ] with a ha
  rw [map_smul]
  exact congrArg (g a • ·) (congrArg (fun L : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ν => L h) ha)
end JoiningOperator

section
open MeasureTheory
open scoped InnerProductSpace ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma tensorLp_indicator (A : Set X) (hA : MeasurableSet A) (B : Set Y) (hB : MeasurableSet B) :
    tensorLp (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℂ))
      (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : ℂ)) =
        indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) (1 : ℂ) := by
  apply Lp.ext
  have hf : Measure.QuasiMeasurePreserving Prod.fst (μ.prod ν) μ :=
    Measure.quasiMeasurePreserving_fst
  have hs : Measure.QuasiMeasurePreserving Prod.snd (μ.prod ν) ν :=
    Measure.quasiMeasurePreserving_snd
  filter_upwards [coe_tensorLp (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℂ))
    (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : ℂ)),
    hf.ae (indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℂ))),
    hs.ae (indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top ν B) (c := (1 : ℂ))),
    indicatorConstLp_coeFn (p := 2) (hs := hA.prod hB) (hμs := measure_ne_top (μ.prod ν) _) (c := (1 : ℂ))]
    with p ht hp hq hr
  rw [ht, hp, hq, hr]
  by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;> simp [ha, hb]

lemma dense_tensorLp :
    (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => tensorLp p.1 p.2))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => tensorLp p.1 p.2))
  have hS : Sᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    apply Lp.ext
    apply (JoiningOperator.ae_eq_zero_of_rectangles
      ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) ?_).trans
      (Lp.coeFn_zero _ _ _).symm
    intro A B hA hB
    rw [← L2.inner_indicatorConstLp_one (hA.prod hB) (measure_ne_top _ _), ← tensorLp_indicator A hA B hB]
    exact S.inner_right_of_mem_orthogonal
      (Submodule.subset_span ⟨(_, _), rfl⟩) hf
  rw [← Submodule.orthogonal_orthogonal_eq_closure, hS, Submodule.bot_orthogonal_eq_top]

end

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma closure_tensor_image (A : Lp ℂ 2 (μ.prod ν) →L[ℂ] H) :
    (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp p.1 p.2)))).topologicalClosure =
      (LinearMap.range A.toLinearMap).topologicalClosure := by
  let S := (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp p.1 p.2)))).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨⟨g,h⟩, rfl⟩
      exact (Submodule.le_topologicalClosure _) ⟨tensorLp g h, rfl⟩
    · exact Submodule.isClosed_topologicalClosure _
  · apply Submodule.topologicalClosure_minimal
    · rintro z ⟨v,rfl⟩
      have hclosed : IsClosed (S.comap A.toLinearMap : Set (Lp ℂ 2 (μ.prod ν))) :=
        (Submodule.isClosed_topologicalClosure _).preimage A.continuous
      have ht : (⊤ : Submodule ℂ (Lp ℂ 2 (μ.prod ν))) ≤ S.comap A.toLinearMap := by
        rw [← dense_tensorLp]
        apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hclosed
        rintro z ⟨⟨g,h⟩,rfl⟩
        exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨(g,h),rfl⟩)
      exact ht (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ (Lp ℂ 2 (μ.prod ν))))
    · exact Submodule.isClosed_topologicalClosure _

omit [CompleteSpace H] in

lemma restricted_contractions_span (A : Lp ℂ 2 (μ.prod ν) →L[ℂ] H)
    (D : Submodule ℂ H) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hA : D ≤ (LinearMap.range A.toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (A (tensorLp g h)) = A (tensorLp (P g) (Q h))) :
    (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp (P p.1) (Q p.2))))).topologicalClosure = D := by
  let S := (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => A (tensorLp (P p.1) (Q p.2))))).topologicalClosure
  have hDS : ∀ v ∈ (LinearMap.range A.toLinearMap).topologicalClosure,
      D.starProjection v ∈ S := by
    intro v hv
    have hclosed : IsClosed (S.comap D.starProjection.toLinearMap : Set H) :=
      (Submodule.isClosed_topologicalClosure _).preimage D.starProjection.continuous
    have hh : (LinearMap.range A.toLinearMap).topologicalClosure ≤ S.comap D.starProjection.toLinearMap := by
      rw [← closure_tensor_image A]
      apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hclosed
      rintro z ⟨⟨g,h⟩,rfl⟩
      change D.starProjection (A (tensorLp g h)) ∈ S
      rw [hPQ]
      exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨(g,h),rfl⟩)
    exact hh hv
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨⟨g,h⟩,rfl⟩
      change A (tensorLp (P g) (Q h)) ∈ D
      rw [← hPQ]
      exact D.starProjection_apply_mem _
    · exact D.isTopCompl_orthogonal.isClosed
  · intro v hv
    have hh := hDS v (hA hv)
    rwa [D.starProjection_eq_self_iff.mpr hv] at hh

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω}
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}

lemma contraction_swap [SFinite η] [SFinite ρ] (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω,y ω)) μ (η.prod ρ))
    (hyu : MeasurePreserving (fun ω => (y ω,u ω)) μ (ρ.prod η))
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    contraction hx huy g h = contraction hx hyu h g := by
  apply ext_inner_left ℂ
  intro f
  rw [contraction_inner,contraction_inner]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [RCLike.inner_apply]
  ring

lemma contraction_projection_both
    [IsFiniteMeasure η] [IsFiniteMeasure ρ]
    (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω,y ω)) μ (η.prod ρ))
    (hyu : MeasurePreserving (fun ω => (y ω,u ω)) μ (ρ.prod η))
    (D : Submodule ℂ (Lp ℂ 2 ν)) [D.HasOrthogonalProjection]
    (P : Submodule ℂ (Lp ℂ 2 η)) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ (Lp ℂ 2 ρ)) [Q.HasOrthogonalProjection]
    (hr : ∀ g h, D.starProjection (contraction hx huy g h) = contraction hx huy g (Q.starProjection h))
    (hl : ∀ h g, D.starProjection (contraction hx hyu h g) = contraction hx hyu h (P.starProjection g))
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) :
    D.starProjection (contraction hx huy g h) =
      contraction hx huy (P.starProjection g) (Q.starProjection h) := by
  calc
    _ = D.starProjection (D.starProjection (contraction hx huy g h)) := by
      rw [D.starProjection_eq_self_iff.mpr (D.starProjection_apply_mem _)]
    _ = D.starProjection (contraction hx huy g (Q.starProjection h)) := by rw [hr]
    _ = D.starProjection (contraction hx hyu (Q.starProjection h) g) := by rw [contraction_swap hx huy hyu]
    _ = contraction hx hyu (Q.starProjection h) (P.starProjection g) := hl _ _
    _ = _ := contraction_swap hx hyu huy _ _

lemma active_eq_essentialRange_product [IsProbabilityMeasure μ]
    [SecondCountableTopology (Lp ℂ 2 ρ)]
    {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
    (hu : MeasurePreserving u μ η) (hx : MeasurePreserving x μ ν)
    (hy : MeasurePreserving y μ ρ)
    (huy : MeasurePreserving (fun ω => (u ω,y ω)) μ (η.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ) :
    (LinearMap.range (operator hx huy).toLinearMap).topologicalClosure =
      essentialRange η (family κ ν ρ) := by
  have h := active_eq_essentialRange hu.measurable hx hy hκ (by simpa only [hu.map_eq] using hm)
  calc
    _ = (LinearMap.range (operator hx ⟨hu.measurable.prodMk hy.measurable,rfl⟩).toLinearMap).topologicalClosure :=
      active_observation_eq hx huy ⟨hu.measurable.prodMk hy.measurable,rfl⟩ rfl
    _ = _ := by simpa only [hu.map_eq] using h
end JoiningOperator

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal

section
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma commonActive_swapColumns (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e =
        commonActive M rows.P rows.A rows.B cols.P cols.B cols.A n e := by
  filter_upwards [rowActive_swap M hM rows.P rows.properP cols n] with e he
  simp only [commonActive,he]

lemma commonActive_swapRows (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e =
        commonActive M rows.P rows.B rows.A cols.P cols.A cols.B n e := by
  filter_upwards [columnActive_swap M hM rows cols.P cols.properP n] with e he
  simp only [commonActive,he]

lemma grouped_first_row_edge (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ s ∂cellLaw M rows.P cols.A n e,
        (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection ∘L
          fibreRowEdge M rows.P cols.A cols.P cols.B n e s =
        fibreRowEdge M rows.P cols.A cols.P cols.B n e s ∘L
          (commonActive M rows.P rows.A rows.B cols.B cols.P cols.A n e).starProjection := by
  filter_upwards [grouped_active_intersections M hM rows.swapPA cols.swapPA n,
    commonActive_swapColumns M hM rows cols.swapPB n] with e he hs
  dsimp only [TriplePartition.swapPA,TriplePartition.swapPB] at he hs
  have hp : (commonActive M rows.P rows.A rows.B cols.B cols.A cols.P n e).starProjection =
      (commonActive M rows.P rows.A rows.B cols.B cols.P cols.A n e).starProjection := by congr 1
  filter_upwards [he.1] with s h
  rw [hp] at h
  exact h

lemma grouped_second_row_edge (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ t ∂cellLaw M rows.P cols.B n e,
        (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection ∘L
          fibreRowEdge M rows.P cols.B cols.P cols.A n e t =
        fibreRowEdge M rows.P cols.B cols.P cols.A n e t ∘L
          (commonActive M rows.P rows.A rows.B cols.A cols.P cols.B n e).starProjection := by
  filter_upwards [grouped_first_row_edge M hM rows cols.swapAB n,
    commonActive_swapColumns M hM rows cols n] with e he hs
  have hp : (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection =
      (commonActive M rows.P rows.A rows.B cols.P cols.B cols.A n e).starProjection := by congr 1
  filter_upwards [he] with t h
  rw [hp]
  exact h

theorem grouped_row_contraction_projection (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P cols.P n) (M.ownKernel (n+2) e) (cellLaw M rows.P cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M rows.P cols.A n y,cells M rows.P cols.B n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.P cols.A n e).prod (cellLaw M rows.P cols.B n e)))
      (g : Lp ℂ 2 (cellLaw M rows.P cols.A n e)) (h : Lp ℂ 2 (cellLaw M rows.P cols.B n e)),
      (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection
        (JoiningOperator.contraction hr hst g h) =
      JoiningOperator.contraction hr hst
        ((commonActive M rows.P rows.A rows.B cols.A cols.P cols.B n e).starProjection g)
        ((commonActive M rows.P rows.A rows.B cols.B cols.P cols.A n e).starProjection h) := by
  filter_upwards [grouped_first_row_edge M hM rows cols n,grouped_second_row_edge M hM rows cols n,
    cells_fibre_marginal M hM rows.P cols.A rows.properP n,
    cells_fibre_marginal M hM rows.P cols.B rows.properP n,
    rowPair_fixed_conditional M rows.P cols.A cols.P cols.B n,
    rowPair_fixed_conditional M rows.P cols.B cols.P cols.A n,
    rowPair_fixed_marginals M hM rows.P cols.A cols.P cols.B rows.properP
      cols.disjointPA.symm cols.disjointAB (by simpa [Finset.union_comm] using cols.properPA) cols.properAB n,
    rowPair_fixed_marginals M hM rows.P cols.B cols.P cols.A rows.properP
      cols.disjointPB.symm cols.disjointAB.symm (by simpa [Finset.union_comm] using cols.properPB)
      (by simpa [Finset.union_comm] using cols.properAB) n] with e hq hp hs ht hκ hξ hmκ hmξ
  intro hr hst g h
  rw [hs.map_eq] at hmκ
  rw [ht.map_eq] at hmξ
  simp only [fibreRowEdge_eq] at hq hp
  let hts : MeasurePreserving (fun y => (cells M rows.P cols.B n y,cells M rows.P cols.A n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.P cols.B n e).prod (cellLaw M rows.P cols.A n e)) :=
    Measure.measurePreserving_swap.comp hst
  apply JoiningOperator.contraction_projection_both hr hst hts _ _ _
  · intro g h
    exact JoiningOperator.contraction_projection hs hr hst hκ hmκ _ _ hq g h
  · intro h g
    exact JoiningOperator.contraction_projection ht hr hts hξ hmξ _ _ hp h g

lemma grouped_first_column_edge (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ s ∂cellLaw M rows.A cols.P n e,
        (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection ∘L
          fibreColumnEdge M rows.A rows.P rows.B cols.P n e s =
        fibreColumnEdge M rows.A rows.P rows.B cols.P n e s ∘L
          (commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection := by
  filter_upwards [grouped_active_intersections M hM rows.swapPA cols.swapPA n,
    commonActive_swapRows M hM rows.swapPB cols n] with e he hs
  dsimp only [TriplePartition.swapPA,TriplePartition.swapPB] at he hs
  have hp : (commonActive M rows.B rows.A rows.P cols.P cols.A cols.B n e).starProjection =
      (commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection := by congr 1
  filter_upwards [he.2.2.1] with s h
  rw [hp] at h
  exact h

lemma grouped_second_column_edge (hM : M.IsSaturated) (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ᵐ t ∂cellLaw M rows.B cols.P n e,
        (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection ∘L
          fibreColumnEdge M rows.B rows.P rows.A cols.P n e t =
        fibreColumnEdge M rows.B rows.P rows.A cols.P n e t ∘L
          (commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e).starProjection := by
  filter_upwards [grouped_first_column_edge M hM rows.swapAB cols n,
    commonActive_swapRows M hM rows cols n] with e he hs
  have hp : (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection =
      (commonActive M rows.P rows.B rows.A cols.P cols.A cols.B n e).starProjection := by congr 1
  filter_upwards [he] with t h
  rw [hp]
  exact h

theorem grouped_column_contraction_projection (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P cols.P n) (M.ownKernel (n+2) e) (cellLaw M rows.P cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M rows.A cols.P n y,cells M rows.B cols.P n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.A cols.P n e).prod (cellLaw M rows.B cols.P n e)))
      (g : Lp ℂ 2 (cellLaw M rows.A cols.P n e)) (h : Lp ℂ 2 (cellLaw M rows.B cols.P n e)),
      (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection
        (JoiningOperator.contraction hr hst g h) =
      JoiningOperator.contraction hr hst
        ((commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e).starProjection g)
        ((commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection h) := by
  let rr := rows.swapPA
  let rt := rows.swapPB
  filter_upwards [grouped_first_column_edge M hM rows cols n,grouped_second_column_edge M hM rows cols n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    columnPair_fixed_conditional M hM rows.A rows.P rows.B cols.P rr.cardP cols.properP n,
    columnPair_fixed_conditional M hM rows.B rows.P rows.A cols.P rt.cardP cols.properP n,
    columnPair_fixed_marginals M hM rows.A rows.P rows.B cols.P rr.cardP cols.properP
      rows.properP rows.properB rows.disjointPA.symm rows.disjointAB
      (by simpa [Finset.union_comm] using rows.properPA) rows.properAB n,
    columnPair_fixed_marginals M hM rows.B rows.P rows.A cols.P rt.cardP cols.properP
      rows.properP rows.properA rows.disjointPB.symm rows.disjointAB.symm
      (by simpa [Finset.union_comm] using rows.properPB)
      (by simpa [Finset.union_comm] using rows.properAB) n] with e hq hp hs ht hκ hξ hmκ hmξ
  intro hr hst g h
  rw [hs.map_eq] at hmκ
  rw [ht.map_eq] at hmξ
  simp only [fibreColumnEdge_eq] at hq hp
  let hts : MeasurePreserving (fun y => (cells M rows.B cols.P n y,cells M rows.A cols.P n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.B cols.P n e).prod (cellLaw M rows.A cols.P n e)) :=
    Measure.measurePreserving_swap.comp hst
  apply JoiningOperator.contraction_projection_both hr hst hts _ _ _
  · intro g h
    exact JoiningOperator.contraction_projection hs hr hst hκ hmκ _ _ hq g h
  · intro h g
    exact JoiningOperator.contraction_projection ht hr hts hξ hmξ _ _ hp h g

end

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rowActive_eq_range (hM : M.IsSaturated) (A : Finset I) (hA : A ≠ Finset.univ)
    (cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M A cols.P n) (M.ownKernel (n+2) e) (cellLaw M A cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M A cols.A n y,cells M A cols.B n y))
        (M.ownKernel (n+2) e) ((cellLaw M A cols.A n e).prod (cellLaw M A cols.B n e))),
      rowActive M A cols.P cols.A cols.B n e =
        (LinearMap.range (JoiningOperator.operator hr hst).toLinearMap).topologicalClosure := by
  filter_upwards [cells_fibre_marginal M hM A cols.A hA n,
    cells_fibre_marginal M hM A cols.B hA n,
    rowPair_fixed_conditional M A cols.A cols.P cols.B n,
    rowPair_fixed_marginals M hM A cols.A cols.P cols.B hA
      cols.disjointPA.symm cols.disjointAB (by simpa [Finset.union_comm] using cols.properPA)
      cols.properAB n] with e hs ht hκ hm
  intro hr hst
  rw [hs.map_eq] at hm
  unfold rowActive
  rw [fibreRowEdge_eq]
  exact (JoiningOperator.active_eq_essentialRange_product hs hr ht hst hκ hm).symm

lemma columnActive_eq_range (hM : M.IsSaturated) (rows : TriplePartition I)
    (R : Finset I) (hR : R ≠ Finset.univ) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P R n) (M.ownKernel (n+2) e) (cellLaw M rows.P R n e))
      (hst : MeasurePreserving (fun y => (cells M rows.A R n y,cells M rows.B R n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.A R n e).prod (cellLaw M rows.B R n e))),
      columnActive M rows.P rows.A rows.B R n e =
        (LinearMap.range (JoiningOperator.operator hr hst).toLinearMap).topologicalClosure := by
  filter_upwards [cells_fibre_marginal M hM rows.A R rows.properA n,
    cells_fibre_marginal M hM rows.B R rows.properB n,
    columnPair_fixed_conditional M hM rows.A rows.P rows.B R rows.swapPA.cardP hR n,
    columnPair_fixed_marginals M hM rows.A rows.P rows.B R rows.swapPA.cardP hR
      rows.properP rows.properB rows.disjointPA.symm rows.disjointAB
      (by simpa [Finset.union_comm] using rows.properPA) rows.properAB n] with e hs ht hκ hm
  intro hr hst
  rw [hs.map_eq] at hm
  unfold columnActive
  rw [fibreColumnEdge_eq]
  exact (JoiningOperator.active_eq_essentialRange_product hs hr ht hst hκ hm).symm

theorem grouped_row_contractions_span (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P cols.P n) (M.ownKernel (n+2) e) (cellLaw M rows.P cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M rows.P cols.A n y,cells M rows.P cols.B n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.P cols.A n e).prod (cellLaw M rows.P cols.B n e))),
      (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 (cellLaw M rows.P cols.A n e) ×
          Lp ℂ 2 (cellLaw M rows.P cols.B n e) => JoiningOperator.contraction hr hst
          ((commonActive M rows.P rows.A rows.B cols.A cols.P cols.B n e).starProjection p.1)
          ((commonActive M rows.P rows.A rows.B cols.B cols.P cols.A n e).starProjection p.2)))).topologicalClosure =
        commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e := by
  filter_upwards [rowActive_eq_range M hM rows.P rows.properP cols n,
    grouped_row_contraction_projection M hM rows cols n] with e he hp
  intro hr hst
  apply restricted_contractions_span (JoiningOperator.operator hr hst)
  · rw [←he hr hst]
    exact inf_le_left
  · exact hp hr hst

theorem grouped_column_contractions_span (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P cols.P n) (M.ownKernel (n+2) e) (cellLaw M rows.P cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M rows.A cols.P n y,cells M rows.B cols.P n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.A cols.P n e).prod (cellLaw M rows.B cols.P n e))),
      (Submodule.span ℂ (Set.range (fun p : Lp ℂ 2 (cellLaw M rows.A cols.P n e) ×
          Lp ℂ 2 (cellLaw M rows.B cols.P n e) => JoiningOperator.contraction hr hst
          ((commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e).starProjection p.1)
          ((commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e).starProjection p.2)))).topologicalClosure =
        commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e := by
  filter_upwards [columnActive_eq_range M hM rows cols.P cols.properP n,
    grouped_column_contraction_projection M hM rows cols n] with e he hp
  intro hr hst
  apply restricted_contractions_span (JoiningOperator.operator hr hst)
  · rw [←he hr hst]
    exact inf_le_right
  · exact hp hr hst

end ArrayObjects.Object.Rolled

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section ContractionCoefficients
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
  [Nonempty X] [Nonempty Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  [IsProbabilityMeasure η] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]

omit [IsProbabilityMeasure η] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] in
lemma contraction_coefficient [SFinite ρ] (hu : MeasurePreserving u μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    contraction hu hxy g h =ᵐ[η] (fun a => inner ℂ (star g) (family κ ν ρ a h)) := by
  let F : X × Y → ℂ := fun p => g p.1 * h p.2
  have hFm : StronglyMeasurable F :=
    (g.1.stronglyMeasurable.comp_measurable measurable_fst).mul
      (h.1.stronglyMeasurable.comp_measurable measurable_snd)
  have hten : (fun ω => tensorLp g h (x ω,y ω)) =ᵐ[μ] (fun ω => F (x ω,y ω)) :=
    hxy.quasiMeasurePreserving.ae (coe_tensorLp g h)
  have hFi : Integrable (fun ω => F (x ω,y ω)) μ := by
    apply (((Lp.memLp (tensorLp g h)).comp_measurePreserving hxy).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).congr
    exact hten
  have hcond := (operator_ae_eq_condExp hu hxy (tensorLp g h)).trans
      ((condExp_congr_ae hten).trans (condExp_of_kernel hu.measurable hκ F hFm hFi))
  have hi : contraction hu hxy g h =ᵐ[η] (fun a => ∫ p, F p ∂κ a) := by
    have ht := (ae_map_iff hu.aemeasurable
      (measurableSet_eq_fun (Lp.stronglyMeasurable (contraction hu hxy g h)).measurable hFm.integral_kernel.measurable)).mpr hcond
    change ∀ᵐ a ∂η, contraction hu hxy g h a = ∫ p, F p ∂κ a
    simpa only [hu.map_eq] using ht
  apply hi.trans
  filter_upwards [hm, family_inner hm (star g) h] with a ha hai
  rw [hai]
  apply integral_congr_ae
  filter_upwards [ha.1.quasiMeasurePreserving.ae (Lp.coeFn_star g)] with p hp
  rw [hp]
  simp [F, RCLike.inner_apply, mul_comm]

end ContractionCoefficients


variable {Ω Z X Y A B C : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  {α : Measure A} {β : Measure B} {τ : Measure C}
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z} {a : X → A} {b : Y → B} {c : Z → C}
  [SFinite ν] [SFinite ρ]

lemma tensor_pull [SFinite β] (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (g : Lp ℂ 2 α) (h : Lp ℂ 2 β) :
    tensorLp (pull ha g) (pull hb h) = pull (ha.prod hb) (tensorLp g h) := by
  apply Lp.ext
  filter_upwards [coe_tensorLp (pull ha g) (pull hb h),
    (ha.prod hb).quasiMeasurePreserving.ae (coe_tensorLp g h),
    Lp.coeFn_compMeasurePreserving (tensorLp g h) (ha.prod hb),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_compMeasurePreserving g ha),
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_compMeasurePreserving h hb)] with p hp ht hpull hga hhb
  exact hp.trans ((congrArg₂ (· * ·) hga hhb).trans (ht.symm.trans hpull.symm))

lemma contraction_pull [SFinite β] (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (g : Lp ℂ 2 α) (h : Lp ℂ 2 β) :
    contraction hz hxy (pull ha g) (pull hb h) =
      operator hz ((ha.prod hb).comp hxy) (tensorLp g h) := by
  unfold contraction operator
  rw [tensor_pull ha hb, pull_comp hxy (ha.prod hb)]
  rfl

lemma contraction_mem_screen
    [IsProbabilityMeasure μ] [StandardBorelSpace A] [Nonempty A]
    [StandardBorelSpace B] [Nonempty B]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (hc : MeasurePreserving c η τ)
    {κ : Kernel C (A × B)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z (κ.comap c hc.measurable) μ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ)
    (hg : g ∈ lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν)
    (hh : h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 ρ) :
    contraction hz hxy g h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  have : SFinite β := hb.map_eq ▸ inferInstanceAs (SFinite (ρ.map b))
  rw [←pull_range ha] at hg
  rw [←pull_range hb] at hh
  obtain ⟨g,rfl⟩ := hg
  obtain ⟨h,rfl⟩ := hh
  change contraction hz hxy (pull ha g) (pull hb h) ∈ _
  rw [contraction_pull hz hxy ha hb g h, screened_operator hz ((ha.prod hb).comp hxy) hc hκ]
  rw [←pull_range hc]
  exact ⟨operator (hc.comp hz) ((ha.prod hb).comp hxy) (tensorLp g h),rfl⟩

end JoiningOperator

section
open MeasureTheory ProbabilityTheory
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

lemma measure_eq_graph_of_ratio (μ : Measure (G × G)) (ρ : Measure G) (a : G)
    (hρ : μ.map Prod.snd = ρ) (hr : ∀ᵐ p ∂μ, p.1 * p.2⁻¹ = a) :
    μ = ρ.map (fun b => (a*b,b)) := by
  have hg : Measurable (fun b : G => (a*b,b)) :=
    (measurable_const.mul measurable_id).prodMk measurable_id
  rw [←hρ, Measure.map_map hg measurable_snd]
  calc
    μ = μ.map id := (Measure.map_id).symm
    _ = μ.map ((fun b => (a*b,b)) ∘ Prod.snd) := by
      apply Measure.map_congr
      filter_upwards [hr] with p hp
      apply Prod.ext
      · change p.1 = a*p.2
        rw [←hp, mul_assoc, inv_mul_cancel, mul_one]
      · rfl

def ratioKernel (ρ : Measure G) : Kernel G (G × G) :=
  (Kernel.id.prod (Kernel.const G ρ)).map (fun p : G × G => (p.1*p.2,p.2))

lemma ratioKernel_apply (ρ : Measure G) [SFinite ρ] (a : G) :
    ratioKernel ρ a = ρ.map (fun b => (a*b,b)) := by
  have hm : Measurable (fun p : G × G => (p.1*p.2,p.2)) :=
    (measurable_fst.mul measurable_snd).prodMk measurable_snd
  rw [ratioKernel, Kernel.map_apply _ hm]
  simp only [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod]
  rw [Measure.map_map hm (measurable_prodMk_left (x := a))]
  rfl

instance ratioKernel_markov (ρ : Measure G) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (ratioKernel ρ) := by
  unfold ratioKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.mul measurable_snd |>.prodMk measurable_snd)

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {μ : Measure Ω} {z : Ω → Z} {v : Ω → G × G}

lemma hasCondDistrib_ratio {κ : Kernel Z (G × G)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib v z κ μ) (ρ : Measure G) [IsProbabilityMeasure ρ]
    (c : Z → G) (hc : Measurable c)
    (hm : ∀ᵐ t ∂μ.map z, (κ t).map Prod.snd = ρ)
    (hr : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂κ t, p.1*p.2⁻¹ = c t) :
    HasCondDistrib v z ((ratioKernel ρ).comap c hc) μ := by
  refine ⟨hκ.aemeasurable, hκ.map_eq.trans (Measure.compProd_congr ?_)⟩
  filter_upwards [hm,hr] with t ht htr
  change κ t = ratioKernel ρ (c t)
  rw [ratioKernel_apply]
  exact measure_eq_graph_of_ratio (κ t) ρ (c t) ht htr

end

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section FactorFields
variable {Ω Z X Y A B C : Type*}
  [MeasurableSpace Ω] [mZ : MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {η : Measure Z}
  {α : Measure A} {β : Measure B} {τ : Measure C}
  {x : Ω → X} {y : Ω → Y} {z : Ω → Z} {a : X → A} {b : Y → B} {c : Z → C}

lemma mem_field_of_eq_comp (hc : Measurable c) (f : Lp ℂ 2 η)
    (F : C → ℂ) (hF : Measurable F) (he : f =ᵐ[η] (fun v => F (c v))) :
    f ∈ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  let : Fact (MeasurableSpace.comap c inferInstance ≤ mZ) := ⟨hc.comap_le⟩
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hm : @StronglyMeasurable Z ℂ _ (MeasurableSpace.comap c inferInstance)
      (fun v => F (c v)) :=
    (hF.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  exact hm.aestronglyMeasurable.congr he.symm

lemma common_space_le_screen
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    [StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B]
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : MeasurePreserving a ν α) (hb : MeasurePreserving b ρ β)
    (hc : MeasurePreserving c η τ)
    {κ : Kernel C (A × B)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z (κ.comap c hc.measurable) μ)
    (D : Submodule ℂ (Lp ℂ 2 η)) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hD : D ≤ (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (contraction hz hxy g h) =
      contraction hz hxy (P g) (Q h))
    (hP : ∀ g, P g ∈ lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν)
    (hQ : ∀ h, Q h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 ρ) :
    D ≤ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  rw [←restricted_contractions_span (operator hz hxy) D P Q hD hPQ]
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,h⟩,rfl⟩
    exact contraction_mem_screen hz hxy ha hb hc hκ (P g) (Q h) (hP g) (hQ h)
  · exact isClosed_aestronglyMeasurable hc.measurable.comap_le

lemma common_space_le_ratio
    {G : Type*} [gG : Group G] [mG : MeasurableSpace G] [hG : MeasurableMul₂ G]
    [StandardBorelSpace G] [Nonempty G]
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    {a : X → G} {b : Y → G} {c : Z → G}
    (hz : MeasurePreserving z μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    {κ : Kernel Z (G × G)} [IsMarkovKernel κ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z κ μ)
    (σ : Measure G) [IsProbabilityMeasure σ]
    (hm : ∀ᵐ t ∂η, (κ t).map Prod.snd = σ)
    (hr : ∀ᵐ t ∂η, ∀ᵐ p ∂κ t, p.1*p.2⁻¹ = c t)
    (D : Submodule ℂ (Lp ℂ 2 η)) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hD : D ≤ (LinearMap.range (operator hz hxy).toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (contraction hz hxy g h) =
      contraction hz hxy (P g) (Q h))
    (hP : ∀ g, P g ∈ lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν)
    (hQ : ∀ h, Q h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 ρ) :
    D ≤ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  have hscreen := hasCondDistrib_ratio hκ σ c hc (by simpa only [hz.map_eq] using hm)
    (by simpa only [hz.map_eq] using hr)
  exact common_space_le_screen hz hxy ⟨ha,rfl⟩ ⟨hb,rfl⟩ ⟨hc,rfl⟩
    hscreen D P Q hD hPQ hP hQ

end FactorFields


variable {Ω U X Y C : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
local instance : MeasurableSpace (Lp ℂ 2 ν) := borel _
local instance : BorelSpace (Lp ℂ 2 ν) := ⟨rfl⟩

lemma contraction_mem_operatorField [SFinite ρ]
    (hu : MeasurePreserving u μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (V : Submodule ℂ (Lp ℂ 2 ρ)) (W : Submodule ℂ (Lp ℂ 2 ν))
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : ∀ᵐ a ∂η, W.starProjection ∘L family κ ν ρ a = family κ ν ρ a ∘L V.starProjection)
    (c : U → C) (hc : Measurable c)
    (F : C → V → W) (hF : ∀ v, Measurable (fun q => (F q v : Lp ℂ 2 ν)))
    (hf : ∀ᵐ a ∂η, ∀ v, compress (family κ ν ρ a) V W v = F (c a) v)
    (g : Lp ℂ 2 ν) (h : V) :
    contraction hu hxy g h ∈ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  apply mem_field_of_eq_comp hc _ (fun q => inner ℂ (star g) (F q h : Lp ℂ 2 ν))
    ((continuous_const.inner (𝕜 := ℂ) continuous_id).measurable.comp (hF h))
  apply (contraction_coefficient hu hxy hκ hm g h).trans
  filter_upwards [hA,hf] with a ha hf
  rw [←compress_apply _ V W ha h, hf]

lemma common_space_le_operatorField
    [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hu : MeasurePreserving u μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (V : Submodule ℂ (Lp ℂ 2 ρ)) (W : Submodule ℂ (Lp ℂ 2 ν))
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hA : ∀ᵐ a ∂η, W.starProjection ∘L family κ ν ρ a = family κ ν ρ a ∘L V.starProjection)
    (c : U → C) (hc : Measurable c)
    (F : C → V → W) (hF : ∀ v, Measurable (fun q => (F q v : Lp ℂ 2 ν)))
    (hf : ∀ᵐ a ∂η, ∀ v, compress (family κ ν ρ a) V W v = F (c a) v)
    (D : Submodule ℂ (Lp ℂ 2 η)) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hD : D ≤ (LinearMap.range (operator hu hxy).toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (contraction hu hxy g h) = contraction hu hxy (P g) (Q h))
    (hQ : ∀ h, Q h ∈ V) :
    D ≤ lpMeas ℂ ℂ (MeasurableSpace.comap c inferInstance) 2 η := by
  rw [←restricted_contractions_span (operator hu hxy) D P Q hD hPQ]
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,h⟩,rfl⟩
    exact contraction_mem_operatorField hu hxy hκ hm V W hA c hc F hF hf (P g) ⟨Q h,hQ h⟩
  · exact isClosed_aestronglyMeasurable hc.comap_le
end JoiningOperator

section
open MeasureTheory ContinuousLinearMap
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]
  {μ : Measure X} [IsProbabilityMeasure μ] {F : X → E →L[ℂ] H}

omit [SecondCountableTopology H] in

lemma MeasurablePolar.fixed_factor (R : MeasurablePolar μ F)
    (hs : HasFixedInjectiveSquares μ F) :
    ∃ B : E →L[ℂ] E, ∀ᵐ x ∂μ, ∀ v, F x v = R.unitary x (B v) := by
  obtain ⟨P,Q,_,_,hP,_⟩ := hs
  obtain ⟨x₀,hx₀⟩ := hP.exists
  refine ⟨operatorAbs (F x₀),?_⟩
  filter_upwards [hP,R.formula] with x hx hf
  intro v
  have he : operatorAbs (F x) = operatorAbs (F x₀) := by
    unfold operatorAbs
    rw [hx,hx₀]
  rw [←hf.2.2]
  change R.unitary x (operatorAbs (F x) v) = _
  rw [he]
end

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
namespace JoiningOperator
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {η : Measure U} [IsProbabilityMeasure η]
  {ν : Measure X} {ρ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]

local instance : MeasurableSpace (Lp ℂ 2 ν) := borel _
local instance : BorelSpace (Lp ℂ 2 ν) := ⟨rfl⟩

lemma common_space_le_polarField
    (hu : MeasurePreserving u μ η)
    (hxy : MeasurePreserving (fun ω => (x ω,y ω)) μ (ν.prod ρ))
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) u κ μ)
    (hm : ∀ᵐ a ∂η, MeasurePreserving Prod.fst (κ a) ν ∧ MeasurePreserving Prod.snd (κ a) ρ)
    (V : Submodule ℂ (Lp ℂ 2 ρ)) (W : Submodule ℂ (Lp ℂ 2 ν))
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] [CompleteSpace V] [CompleteSpace W]
    (hA : ∀ᵐ a ∂η, W.starProjection ∘L family κ ν ρ a = family κ ν ρ a ∘L V.starProjection)
    (R : MeasurablePolar η (fun a => compress (family κ ν ρ a) V W))
    (hs : HasFixedInjectiveSquares η (fun a => compress (family κ ν ρ a) V W))
    (D : Submodule ℂ (Lp ℂ 2 η)) [D.HasOrthogonalProjection]
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ)
    (hD : D ≤ (LinearMap.range (operator hu hxy).toLinearMap).topologicalClosure)
    (hPQ : ∀ g h, D.starProjection (contraction hu hxy g h) = contraction hu hxy (P g) (Q h))
    (hQ : ∀ h, Q h ∈ V) :
    D ≤ lpMeas ℂ ℂ (MeasurableSpace.comap R.unitary inferInstance) 2 η := by
  obtain ⟨B,hB⟩ := R.fixed_factor hs
  apply common_space_le_operatorField hu hxy hκ hm V W hA R.unitary R.measurable
    (fun q v => q (B v)) _ hB D P Q hD hPQ hQ
  intro v
  exact (continuous_subtype_val.comp (StrongUnitary.continuous_apply (B v))).measurable
end JoiningOperator

namespace ArrayObjects.Object.Rolled
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_polar_a_field (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ R : GroupedPolarData M rows cols n e,
        commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e ≤
          lpMeas ℂ ℂ (MeasurableSpace.comap R.a.unitary inferInstance) 2
            (cellLaw M rows.A cols.P n e) := by
  filter_upwards [grouped_rectangle_spaces M hM rows cols n,
    grouped_restricted_fixed_squares M hM rows cols n,
    grouped_active_intersections M hM rows cols n,
    grouped_row_contraction_projection M hM rows.swapPA cols n,
    rowActive_eq_range M hM rows.A rows.properA cols n,
    cells_fibre_marginal M hM rows.A cols.P rows.properA n,
    cells_fibre_marginal M hM rows.A cols.A rows.properA n,
    cells_fibre_marginal M hM rows.A cols.B rows.properA n,
    cells_indep_columns_fibre M rows.A rows.A cols.A cols.B cols.disjointAB cols.properAB n,
    rowPair_fixed_conditional M rows.A cols.P cols.A cols.B n,
    rowPair_fixed_marginals M hM rows.A cols.P cols.A cols.B rows.properA
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n]
      with e hspaces hs hA hproj hrange hx hc hd hcd hκ hm
  intro R
  rw [hx.map_eq] at hm
  let hpair : MeasurePreserving (fun y => (cells M rows.A cols.A n y,cells M rows.A cols.B n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.A cols.A n e).prod (cellLaw M rows.A cols.B n e)) :=
    ⟨hc.measurable.prodMk hd.measurable, by
      rw [←hc.map_eq,←hd.map_eq]
      exact hcd.map_prod_eq_prod_map_map hc.measurable.aemeasurable hd.measurable.aemeasurable⟩
  let V := rectangleSpace₂ (cellLaw M rows.A cols.P n e) (cellLaw M rows.P cols.B n e)
    (fibreRowEdge M rows.A cols.P cols.A cols.B n e) (fibreColumnEdge M rows.P rows.A rows.B cols.B n e)
  let W := rectangleSpace₁ (cellLaw M rows.A cols.P n e) (cellLaw M rows.P cols.A n e)
    (fibreRowEdge M rows.A cols.P cols.A cols.B n e) (fibreColumnEdge M rows.P rows.A rows.B cols.A n e)
  have hv : V = commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e := hspaces.2.1
  have hw : W = commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e := hspaces.1
  have ha : ∀ᵐ a ∂cellLaw M rows.A cols.P n e,
      W.starProjection ∘L JoiningOperator.family ((rowPairKernel M rows.A cols.P cols.A cols.B n).sectR e)
        (cellLaw M rows.A cols.A n e) (cellLaw M rows.A cols.B n e) a =
      JoiningOperator.family ((rowPairKernel M rows.A cols.P cols.A cols.B n).sectR e)
        (cellLaw M rows.A cols.A n e) (cellLaw M rows.A cols.B n e) a ∘L V.starProjection := by
    simpa only [hv,hw,fibreRowEdge_eq] using hA.1
  apply JoiningOperator.common_space_le_polarField hx hpair hκ hm V W ha R.a hs.1 _
    (commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e).starProjection
    (commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e).starProjection
  · rw [←hrange hx hpair]
    exact inf_le_left
  · exact hproj hx hpair
  · intro h
    rw [hv]
    exact Submodule.starProjection_apply_mem _ h

theorem grouped_polar_b_field (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ R : GroupedPolarData M rows cols n e,
        commonActive M rows.B rows.P rows.A cols.P cols.A cols.B n e ≤
          lpMeas ℂ ℂ (MeasurableSpace.comap R.b.unitary inferInstance) 2
            (cellLaw M rows.B cols.P n e) := by
  filter_upwards [grouped_rectangle_spaces M hM rows cols n,
    grouped_restricted_fixed_squares M hM rows cols n,
    grouped_active_intersections M hM rows cols n,
    grouped_row_contraction_projection M hM rows.swapAB.swapPA cols n,
    rowActive_eq_range M hM rows.B rows.properB cols n,
    cells_fibre_marginal M hM rows.B cols.P rows.properB n,
    cells_fibre_marginal M hM rows.B cols.A rows.properB n,
    cells_fibre_marginal M hM rows.B cols.B rows.properB n,
    cells_indep_columns_fibre M rows.B rows.B cols.A cols.B cols.disjointAB cols.properAB n,
    rowPair_fixed_conditional M rows.B cols.P cols.A cols.B n,
    rowPair_fixed_marginals M hM rows.B cols.P cols.A cols.B rows.properB
      cols.disjointPA cols.disjointPB cols.properPA cols.properPB n]
      with e hspaces hs hA hproj hrange hx hc hd hcd hκ hm
  intro R
  rw [hx.map_eq] at hm
  let hpair : MeasurePreserving (fun y => (cells M rows.B cols.A n y,cells M rows.B cols.B n y))
      (M.ownKernel (n+2) e) ((cellLaw M rows.B cols.A n e).prod (cellLaw M rows.B cols.B n e)) :=
    ⟨hc.measurable.prodMk hd.measurable, by
      rw [←hc.map_eq,←hd.map_eq]
      exact hcd.map_prod_eq_prod_map_map hc.measurable.aemeasurable hd.measurable.aemeasurable⟩
  let V := rectangleSpace₄ (cellLaw M rows.B cols.P n e) (cellLaw M rows.P cols.B n e)
    (fibreRowEdge M rows.B cols.P cols.A cols.B n e) (fibreColumnEdge M rows.P rows.A rows.B cols.B n e)
  let W := rectangleSpace₃ (cellLaw M rows.B cols.P n e) (cellLaw M rows.P cols.A n e)
    (fibreRowEdge M rows.B cols.P cols.A cols.B n e) (fibreColumnEdge M rows.P rows.A rows.B cols.A n e)
  have hv : V = commonActive M rows.B rows.P rows.A cols.B cols.P cols.A n e := hspaces.2.2.2
  have hw : W = commonActive M rows.B rows.P rows.A cols.A cols.P cols.B n e := hspaces.2.2.1
  have ha : ∀ᵐ a ∂cellLaw M rows.B cols.P n e,
      W.starProjection ∘L JoiningOperator.family ((rowPairKernel M rows.B cols.P cols.A cols.B n).sectR e)
        (cellLaw M rows.B cols.A n e) (cellLaw M rows.B cols.B n e) a =
      JoiningOperator.family ((rowPairKernel M rows.B cols.P cols.A cols.B n).sectR e)
        (cellLaw M rows.B cols.A n e) (cellLaw M rows.B cols.B n e) a ∘L V.starProjection := by
    simpa only [hv,hw,fibreRowEdge_eq] using hA.2.1
  apply JoiningOperator.common_space_le_polarField hx hpair hκ hm V W ha R.b hs.2.1 _
    (commonActive M rows.B rows.P rows.A cols.A cols.P cols.B n e).starProjection
    (commonActive M rows.B rows.P rows.A cols.B cols.P cols.A n e).starProjection
  · rw [←hrange hx hpair]
    exact inf_le_left
  · exact hproj hx hpair
  · intro h
    rw [hv]
    exact Submodule.starProjection_apply_mem _ h
end ArrayObjects.Object.Rolled
end

section
open MeasureTheory
open scoped ENNReal
variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure Ω} {a a' : Ω → A} {b : Ω → B}

lemma lpMeas_comap_congr (he : a =ᵐ[μ] a') :
    lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 μ =
      lpMeas ℂ ℂ (MeasurableSpace.comap a' inferInstance) 2 μ := by
  suffices h : ∀ (a a' : Ω → A), a =ᵐ[μ] a' →
      lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 μ ≤
        lpMeas ℂ ℂ (MeasurableSpace.comap a' inferInstance) 2 μ from
    le_antisymm (h a a' he) (h a' a he.symm)
  intro a a' hae f hf
  have hm := mem_lpMeas_iff_aestronglyMeasurable.mp hf
  obtain ⟨g,hg,hgcomp⟩ := hm.stronglyMeasurable_mk.exists_eq_measurable_comp
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hstrong : StronglyMeasurable[MeasurableSpace.comap a' inferInstance] (g ∘ a') :=
    hg.comp_measurable (Measurable.of_comap_le le_rfl)
  apply hstrong.aestronglyMeasurable.congr
  filter_upwards [hm.ae_eq_mk,hae] with ω hfω haω
  exact (congrArg g haω).symm.trans ((congrFun hgcomp ω).symm.trans hfω.symm)

lemma lpMeas_comap_mono (hab : MeasurableSpace.comap a inferInstance ≤
    MeasurableSpace.comap b inferInstance) :
    lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 μ ≤
      lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 μ := by
  intro f hf
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact (mem_lpMeas_iff_aestronglyMeasurable.mp hf).mono hab

end

section
open MeasureTheory
lemma comap_eq_of_measurable_leftInverse {X Y Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (a : X → Y)
    (f : Y → Z) (g : Z → Y) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    MeasurableSpace.comap (f ∘ a) inferInstance = MeasurableSpace.comap a inferInstance := by
  apply le_antisymm
  · rw [←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hf.comap_le
  · have he : a = g ∘ (f ∘ a) := funext fun x => (hgf (a x)).symm
    conv_lhs => rw [he,←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hg.comap_le
namespace StrongUnitary
variable {X H₁ H₂ H₃ H₄ : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

omit [SecondCountableTopology H₁] in
lemma comap_normalizeA (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (a : X → H₂ ≃ₗᵢ[ℂ] H₁) :
    MeasurableSpace.comap (normalizeA a₀ d₀ ∘ a) inferInstance =
      MeasurableSpace.comap a inferInstance := by
  let g (u : H₄ ≃ₗᵢ[ℂ] H₄) := d₀.symm.trans (u.trans (d₀.trans a₀))
  have hg : Continuous g := by
    apply continuous_iff.mpr
    intro v
    exact (d₀.trans a₀).continuous.comp (continuous_apply (d₀.symm v))
  apply comap_eq_of_measurable_leftInverse a _ g (continuous_normalizeA a₀ d₀).measurable hg.measurable
  intro u
  ext v
  simp [g,normalizeA]

omit [SecondCountableTopology H₃] in
lemma comap_normalizeB (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (b : X → H₄ ≃ₗᵢ[ℂ] H₃) :
    MeasurableSpace.comap (normalizeB b₀ ∘ b) inferInstance =
      MeasurableSpace.comap b inferInstance := by
  let g (u : H₄ ≃ₗᵢ[ℂ] H₄) := u.trans b₀
  have hg : Continuous g := by
    apply continuous_iff.mpr
    intro v
    exact b₀.continuous.comp (continuous_apply v)
  apply comap_eq_of_measurable_leftInverse b _ g (continuous_normalizeB b₀).measurable hg.measurable
  intro u
  ext v
  simp [g,normalizeB]

end StrongUnitary
end

namespace StrongUnitary

open MeasureTheory

section MeasurableEigenvalues
variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace X]

lemma measurable_of_eigenvalues (b : HilbertBasis I ℂ H) (U : X → H ≃ₗᵢ[ℂ] H)
    (χ : I → X → ℂ) (hχ : ∀ i, Measurable (χ i))
    (he : ∀ i x, U x (b i) = χ i x • b i) : Measurable U := by
  borelize H
  let : Countable I := hilbertBasis_countable b
  apply measurable_iff.mpr
  intro v
  have hes (x : X) : (∑' i, (b.repr v i * χ i x) • b i) = U x v := by
    have hs := (U x : H →L[ℂ] H).hasSum (b.hasSum_repr v)
    change HasSum (fun i => U x (b.repr v i • b i)) (U x v) at hs
    simpa only [map_smul, he, smul_smul] using hs.tsum_eq
  have hm : Measurable (fun x => ∑' i, (b.repr v i * χ i x) • b i) :=
    Measurable.tsum (fun i => (measurable_const.mul (hχ i)).smul measurable_const)
  simpa only [hes] using hm.stronglyMeasurable

end MeasurableEigenvalues


section
variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

lemma measurable_iff_eigenCoords [MeasurableSpace X]
    (b : HilbertBasis I ℂ H) (U : X → H ≃ₗᵢ[ℂ] H) (γ : X → I → Circle)
    (he : ∀ i x, U x (b i) = (γ x i : ℂ) • b i) :
    Measurable U ↔ Measurable γ := by
  borelize H
  constructor
  · intro hU
    apply Measurable.of_eval
    intro i
    apply Measurable.subtype_mk
    have hm : Measurable (fun x => inner ℂ (b i) (U x (b i))) :=
      (measurable_const (a := b i)).inner (𝕜 := ℂ) ((continuous_apply (b i)).measurable.comp hU)
    have heq (x : X) : (γ x i : ℂ) = inner ℂ (b i) (U x (b i)) := by
      rw [he, inner_smul_right]
      simp [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    convert hm using 1
    ext x
    exact heq x
  · intro hγ
    apply measurable_of_eigenvalues b U (fun i x => (γ x i : ℂ)) _ he
    intro i
    exact measurable_subtype_coe.comp ((measurable_pi_apply i).comp hγ)

lemma comap_eigenCoords (b : HilbertBasis I ℂ H)
    (U : X → H ≃ₗᵢ[ℂ] H) (γ : X → I → Circle)
    (he : ∀ i x, U x (b i) = (γ x i : ℂ) • b i) :
    MeasurableSpace.comap U inferInstance = MeasurableSpace.comap γ inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace X := MeasurableSpace.comap γ inferInstance
    have hm : Measurable γ := Measurable.of_comap_le le_rfl
    exact ((measurable_iff_eigenCoords b U γ he).mpr hm).comap_le
  · let : MeasurableSpace X := MeasurableSpace.comap U inferInstance
    have hm : Measurable U := Measurable.of_comap_le le_rfl
    exact ((measurable_iff_eigenCoords b U γ he).mp hm).comap_le
end

variable {H J X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

def subgroupVersion (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (g : H ≃ₗᵢ[ℂ] H) : S := by
  classical
  exact if h : g ∈ S then ⟨g,h⟩ else 1

omit [CompleteSpace H] in
lemma measurable_subgroupVersion (S : Subgroup (H ≃ₗᵢ[ℂ] H))
    (hS : IsClosed (S : Set (H ≃ₗᵢ[ℂ] H))) : Measurable (subgroupVersion S) := by
  classical
  exact Measurable.dite measurable_id measurable_const hS.measurableSet

omit [CompleteSpace H] [SecondCountableTopology H] in
lemma subgroupVersion_coe (S : Subgroup (H ≃ₗᵢ[ℂ] H)) {g : H ≃ₗᵢ[ℂ] H} (hg : g ∈ S) :
    (subgroupVersion S g : H ≃ₗᵢ[ℂ] H) = g := by simp [subgroupVersion,hg]

def spectralCoords (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (γ : J → S →* Circle)
    (g : H ≃ₗᵢ[ℂ] H) : J → Circle := fun j => γ j (subgroupVersion S g)

omit [CompleteSpace H] in
lemma measurable_spectralCoords (S : Subgroup (H ≃ₗᵢ[ℂ] H))
    (hS : IsClosed (S : Set (H ≃ₗᵢ[ℂ] H))) (γ : J → S →* Circle)
    (hγ : ∀ j, Continuous (γ j)) : Measurable (spectralCoords S γ) :=
  Measurable.of_eval fun j => (hγ j).measurable.comp (measurable_subgroupVersion S hS)

omit [CompleteSpace H] [SecondCountableTopology H] in
lemma spectralCoords_mul_inv (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (γ : J → S →* Circle)
    {g h : H ≃ₗᵢ[ℂ] H} (hg : g ∈ S) (hh : h ∈ S) :
    spectralCoords S γ (g*h⁻¹) = spectralCoords S γ g * (spectralCoords S γ h)⁻¹ := by
  have hs : subgroupVersion S (g*h⁻¹) = subgroupVersion S g * (subgroupVersion S h)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul,Subgroup.coe_inv,subgroupVersion_coe S hg,
      subgroupVersion_coe S hh,subgroupVersion_coe S (S.mul_mem hg (S.inv_mem hh))]
  funext j
  simp only [spectralCoords,hs,map_mul,map_inv,Pi.mul_apply,Pi.inv_apply]

lemma lpMeas_spectralCoords [MeasurableSpace X] (μ : Measure X)
    (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (b : HilbertBasis J ℂ H) (γ : J → S →* Circle)
    (heig : ∀ j (g : S), (g : H ≃ₗᵢ[ℂ] H) (b j) = (γ j g : ℂ) • b j)
    (U : X → H ≃ₗᵢ[ℂ] H) (hU : ∀ᵐ x ∂μ, U x ∈ S) :
    lpMeas ℂ ℂ (MeasurableSpace.comap U inferInstance) 2 μ =
      lpMeas ℂ ℂ (MeasurableSpace.comap (spectralCoords S γ ∘ U) inferInstance) 2 μ := by
  let V (x : X) : H ≃ₗᵢ[ℂ] H := subgroupVersion S (U x)
  have huv : U =ᵐ[μ] V := hU.mono fun x hx => (subgroupVersion_coe S hx).symm
  rw [lpMeas_comap_congr huv]
  rw [comap_eigenCoords b V (spectralCoords S γ ∘ U) (fun j x => heig j (subgroupVersion S (U x)))]
  rfl


end StrongUnitary

section
open MeasureTheory ProbabilityTheory

lemma exists_const_of_ae_prod_eq {X Y V : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → V} {g : Y → V}
    (h : ∀ᵐ p ∂μ.prod ν, f p.1 = g p.2) :
    ∃ v, f =ᵐ[μ] (fun _ => v) ∧ g =ᵐ[ν] (fun _ => v) := by
  have hh : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f x = g y := Measure.ae_ae_of_ae_prod h
  obtain ⟨x₀,hx₀⟩ := hh.exists
  refine ⟨f x₀, ?_, hx₀.mono (fun _ hy => hy.symm)⟩
  filter_upwards [hh] with x hx
  obtain ⟨y,hy,h0y⟩ := (hx.and hx₀).exists
  exact hy.trans h0y.symm

lemma measurable_conull_subset {Z : Type*} [MeasurableSpace Z] {σ : Measure Z}
    {p : Z → Prop} (h : ∀ᵐ z ∂σ, p z) :
    ∃ s : Set Z, MeasurableSet s ∧ (∀ᵐ z ∂σ, z ∈ s) ∧ ∀ z ∈ s, p z := by
  obtain ⟨t,ht,htm,ht0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  refine ⟨tᶜ, htm.compl, ?_, ?_⟩
  · apply mem_ae_iff.mpr
    change σ (tᶜ)ᶜ = 0
    simpa only [compl_compl] using ht0
  · intro z hz
    by_contra hp
    exact hz (ht hp)

lemma exists_measurable_common_unitary {Z X Y H : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology H] [CompleteSpace H]
    {σ : Measure Z} (κ : Kernel Z X) (ξ : Kernel Z Y)
    [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (f : X → H ≃ₗᵢ[ℂ] H) (g : Y → H ≃ₗᵢ[ℂ] H)
    (hf : Measurable f)
    (heq : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), f p.1 = g p.2) :
    ∃ U : Z → H ≃ₗᵢ[ℂ] H, Measurable U ∧
      ∀ᵐ z ∂σ, f =ᵐ[κ z] (fun _ => U z) ∧ g =ᵐ[ξ z] (fun _ => U z) := by
  classical
  have he : ∀ᵐ z ∂σ, ∃ U, f =ᵐ[κ z] (fun _ => U) ∧ g =ᵐ[ξ z] (fun _ => U) :=
    heq.mono fun _ hz => exists_const_of_ae_prod_eq hz
  obtain ⟨s,hsm,hs,hsprop⟩ := measurable_conull_subset he
  choose U₀ hU₀ using fun z : s => hsprop z z.property
  let U : Z → H ≃ₗᵢ[ℂ] H := fun z => if hz : z ∈ s then U₀ ⟨z,hz⟩ else 1
  refine ⟨U, ?_, ?_⟩
  · apply StrongUnitary.measurable_iff.mpr
    intro v
    have hev : (fun z => U z v) = s.piecewise (fun z => ∫ x, f x v ∂κ z) (fun _ => v) := by
      funext z
      by_cases hz : z ∈ s
      · simp only [U, dite_eq_left hz, Set.piecewise_eq_of_mem s _ _ hz]
        calc
          U₀ ⟨z,hz⟩ v = ∫ _x, U₀ ⟨z,hz⟩ v ∂κ z := by simp
          _ = ∫ x, f x v ∂κ z := integral_congr_ae ((hU₀ ⟨z,hz⟩).1.fun_comp (fun A => A v)).symm
      · simp [U, hz]
    rw [hev]
    exact ((StrongUnitary.measurable_iff.mp hf v).integral_kernel).piecewise hsm stronglyMeasurable_const
  · filter_upwards [hs] with z hz
    simpa only [U,dite_eq_left hz] using hU₀ ⟨z,hz⟩

namespace StrongUnitary

lemma rectangle_ratio_eq {G : Type*} [Group G] {a b c d : G}
    (hbd : Commute b d) (h : a * d = c * b) : a * b⁻¹ = c * d⁻¹ := by
  apply mul_inv_eq_iff_eq_mul.mpr
  calc
    a = c * b * d⁻¹ := by rw [←h, mul_assoc, mul_inv_cancel, mul_one]
    _ = (c * d⁻¹) * b := by rw [mul_assoc, hbd.inv_right.eq, ←mul_assoc]

variable {Z H : Type*} [MeasurableSpace Z]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]

lemma measurable_corner_ratio (σ : Measure Z)
    (κ ξ : Kernel Z ((H ≃ₗᵢ[ℂ] H) × (H ≃ₗᵢ[ℂ] H)))
    [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (ρ τ : ProbabilityMeasure (H ≃ₗᵢ[ℂ] H)) (G : Subgroup (H ≃ₗᵢ[ℂ] H))
    (hρ : (ρ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H))) (hτ : (τ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hcomm : ∀ u ∈ G, ∀ v ∈ G, u * v = v * u)
    (hm : ∀ᵐ z ∂σ, (κ z).map Prod.fst = ρ ∧ (κ z).map Prod.snd = ρ ∧
      (ξ z).map Prod.fst = τ ∧ (ξ z).map Prod.snd = τ)
    (hr : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), p.1.1*p.2.2 = p.2.1*p.1.2) :
    ∃ U : Z → H ≃ₗᵢ[ℂ] H, Measurable U ∧ ∀ᵐ z ∂σ, U z ∈ G ∧
      (∀ᵐ p ∂κ z, p.1 * p.2⁻¹ = U z) ∧
      (∀ᵐ p ∂ξ z, p.1 * p.2⁻¹ = U z) := by
  have hρm : ∀ᵐ u ∂(ρ : Measure _), u ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (ρ : Measure _)
    rw [←hρ]
    exact Measure.support_mem_ae
  have hτm : ∀ᵐ u ∂(τ : Measure _), u ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (τ : Measure _)
    rw [←hτ]
    exact Measure.support_mem_ae
  have hpairs : ∀ᵐ z ∂σ, (∀ᵐ p ∂κ z, p.1 ∈ G ∧ p.2 ∈ G) ∧
      (∀ᵐ p ∂ξ z, p.1 ∈ G ∧ p.2 ∈ G) := by
    filter_upwards [hm] with z hz
    constructor
    · have ha := ae_of_ae_map measurable_fst.aemeasurable (hz.1 ▸ hρm)
      have hb := ae_of_ae_map measurable_snd.aemeasurable (hz.2.1 ▸ hρm)
      exact ha.and hb
    · have hc := ae_of_ae_map measurable_fst.aemeasurable (hz.2.2.1 ▸ hτm)
      have hd := ae_of_ae_map measurable_snd.aemeasurable (hz.2.2.2 ▸ hτm)
      exact hc.and hd
  have he : ∀ᵐ z ∂σ, ∀ᵐ p ∂(κ z).prod (ξ z), p.1.1 * p.1.2⁻¹ = p.2.1 * p.2.2⁻¹ := by
    filter_upwards [hpairs,hr] with z hz hzr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hz.1,
      Measure.quasiMeasurePreserving_snd.ae hz.2,hzr] with p hp hq hrect
    exact rectangle_ratio_eq (hcomm _ hp.2 _ hq.2) hrect
  obtain ⟨U,hU,heU⟩ := exists_measurable_common_unitary κ ξ
    (fun p => p.1 * p.2⁻¹) (fun p => p.1 * p.2⁻¹)
    (measurable_fst.mul measurable_snd.inv) he
  refine ⟨U,hU,?_⟩
  filter_upwards [hpairs,heU] with z hz hzu
  obtain ⟨p,hp,heq⟩ := (hz.1.and hzu.1).exists
  change p.1 * p.2⁻¹ = U z at heq
  exact ⟨heq ▸ G.mul_mem hp.1 (G.inv_mem hp.2), hzu⟩

end StrongUnitary

namespace ConditionalFibres
lemma ae_of_ae_kernel {Ω Z V : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace V] {μ : Measure Ω} {z : Ω → Z} {v : Ω → V}
    {κ : Kernel Z V} (h : HasCondDistrib v z κ μ) {p : Z × V → Prop}
    (hp : MeasurableSet {q | p q}) (hv : ∀ᵐ a ∂μ.map z, ∀ᵐ b ∂κ a, p (a,b)) :
    ∀ᵐ ω ∂μ, p (z ω,v ω) := by
  have hh := Measure.ae_compProd_of_ae_ae hp hv
  rw [←h.map_eq] at hh
  exact ae_of_ae_map h.aemeasurable hh
end ConditionalFibres
namespace StrongUnitary
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
universe u
variable {Ω Z X Y C D : Type*} {H : Type u}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]
  {μ : Measure Ω} {ν : Measure X} {η : Measure Y} {ξC : Measure C} {ξD : Measure D}
  {z : Ω → Z} {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}

lemma spectral_corner
    (G : Subgroup (H ≃ₗᵢ[ℂ] H)) (hG : IsClosed (G : Set (H ≃ₗᵢ[ℂ] H)))
    (ρ τ : ProbabilityMeasure (H ≃ₗᵢ[ℂ] H))
    (hρ : (ρ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hτ : (τ : Measure _).support = (G : Set (H ≃ₗᵢ[ℂ] H)))
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, g*h = h*g)
    (hinv : ∀ g ∈ G, (ρ : Measure _).map (g * ·) = ρ)
    (a : X → H ≃ₗᵢ[ℂ] H) (b : Y → H ≃ₗᵢ[ℂ] H)
    (f : C → H ≃ₗᵢ[ℂ] H) (g : D → H ≃ₗᵢ[ℂ] H)
    (ha : MeasurePreserving a ν ρ) (hb : MeasurePreserving b η ρ)
    (hf : MeasurePreserving f ξC τ) (hg : MeasurePreserving g ξD τ)
    (κ ξ : Kernel Z ((H ≃ₗᵢ[ℂ] H) × (H ≃ₗᵢ[ℂ] H)))
    [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hκ : HasCondDistrib (fun ω => (a (x ω),b (y ω))) z κ μ)
    (hξ : HasCondDistrib (fun ω => (f (c ω),g (d ω))) z ξ μ)
    (hm : ∀ᵐ t ∂μ.map z, (κ t).map Prod.fst = ρ ∧ (κ t).map Prod.snd = ρ ∧
      (ξ t).map Prod.fst = τ ∧ (ξ t).map Prod.snd = τ)
    (hr : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂(κ t).prod (ξ t), p.1.1*p.2.2 = p.2.1*p.1.2) :
    ∃ (J : Type u) (_ : Countable J)
      (A : X → J → Circle) (B : Y → J → Circle)
      (F : C → J → Circle) (Q : D → J → Circle) (K : Z → J → Circle),
      Measurable A ∧ Measurable B ∧ Measurable F ∧ Measurable Q ∧ Measurable K ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap a inferInstance) 2 ν =
        lpMeas ℂ ℂ (MeasurableSpace.comap A inferInstance) 2 ν ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap b inferInstance) 2 η =
        lpMeas ℂ ℂ (MeasurableSpace.comap B inferInstance) 2 η ∧
      (∀ᵐ ω ∂μ, K (z ω) = A (x ω) * (B (y ω))⁻¹) ∧
      (∀ᵐ ω ∂μ, K (z ω) = F (c ω) * (Q (d ω))⁻¹) := by
  obtain ⟨U,hU,hUr⟩ := measurable_corner_ratio (μ.map z) κ ξ ρ τ G hρ hτ hcomm hm hr
  obtain ⟨J,hJ,e,γ,hγ,he⟩ := polar_spectral G hG ρ hρ hcomm hinv
  let sc := spectralCoords G γ
  have hsc : Measurable sc := measurable_spectralCoords G hG γ hγ
  have hgρ : ∀ᵐ v ∂(ρ : Measure _), v ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (ρ : Measure _)
    rw [←hρ]
    exact Measure.support_mem_ae
  have hgτ : ∀ᵐ v ∂(τ : Measure _), v ∈ G := by
    change (G : Set (H ≃ₗᵢ[ℂ] H)) ∈ ae (τ : Measure _)
    rw [←hτ]
    exact Measure.support_mem_ae
  have hmκ : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂κ t, p.1 ∈ G ∧ p.2 ∈ G := by
    filter_upwards [hm] with t ht
    exact (ae_of_ae_map measurable_fst.aemeasurable (ht.1 ▸ hgρ)).and
      (ae_of_ae_map measurable_snd.aemeasurable (ht.2.1 ▸ hgρ))
  have hmξ : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂ξ t, p.1 ∈ G ∧ p.2 ∈ G := by
    filter_upwards [hm] with t ht
    exact (ae_of_ae_map measurable_fst.aemeasurable (ht.2.2.1 ▸ hgτ)).and
      (ae_of_ae_map measurable_snd.aemeasurable (ht.2.2.2 ▸ hgτ))
  refine ⟨J,hJ,sc ∘ a,sc ∘ b,sc ∘ f,sc ∘ g,sc ∘ U,
    hsc.comp ha.measurable,hsc.comp hb.measurable,hsc.comp hf.measurable,
    hsc.comp hg.measurable,hsc.comp hU,?_,?_,?_,?_⟩
  · exact lpMeas_spectralCoords ν G e γ he a (ha.quasiMeasurePreserving.ae hgρ)
  · exact lpMeas_spectralCoords η G e γ he b (hb.quasiMeasurePreserving.ae hgρ)
  · have hh : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂κ t, sc (U t) = sc p.1 * (sc p.2)⁻¹ := by
      filter_upwards [hUr,hmκ] with t ht hm
      filter_upwards [ht.2.1,hm] with p hp hmem
      rw [←hp]
      exact spectralCoords_mul_inv G γ hmem.1 hmem.2
    exact ConditionalFibres.ae_of_ae_kernel hκ
      (measurableSet_eq_fun ((hsc.comp hU).comp measurable_fst)
        ((hsc.comp measurable_snd.fst).mul (hsc.comp measurable_snd.snd).inv)) hh
  · have hh : ∀ᵐ t ∂μ.map z, ∀ᵐ p ∂ξ t, sc (U t) = sc p.1 * (sc p.2)⁻¹ := by
      filter_upwards [hUr,hmξ] with t ht hm
      filter_upwards [ht.2.2,hm] with p hp hmem
      rw [←hp]
      exact spectralCoords_mul_inv G γ hmem.1 hmem.2
    exact ConditionalFibres.ae_of_ae_kernel hξ
      (measurableSet_eq_fun ((hsc.comp hU).comp measurable_fst)
        ((hsc.comp measurable_snd.fst).mul (hsc.comp measurable_snd.snd).inv)) hh
end StrongUnitary
end

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
universe u
variable {Ω Z X Y C D H₁ H₂ H₃ : Type*} {H₄ : Type u}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

omit [SecondCountableTopology H₁] [IsProbabilityMeasure μY] [IsProbabilityMeasure μD] in

lemma MeasurablePolarRectangle.torus_coordinates
    (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d)
    (hR : R.HasHaarNormalization)
    {z : Ω → Z}
    (κ : Kernel Z (X × Y)) (ξ : Kernel Z (C × D)) [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) z κ μ)
    (hξ : HasCondDistrib (fun ω => (c ω,d ω)) z ξ μ)
    (hpair : HasCondDistrib (fun ω => ((x ω,y ω),(c ω,d ω))) z (κ ×ₖ ξ) μ)
    (hκm : ∀ᵐ v ∂μ.map z, (κ v).map Prod.fst = μX ∧ (κ v).map Prod.snd = μY)
    (hξm : ∀ᵐ v ∂μ.map z, (ξ v).map Prod.fst = μC ∧ (ξ v).map Prod.snd = μD) :
    ∃ (J : Type u) (_ : Countable J)
      (A : X → J → Circle) (B : Y → J → Circle)
      (P : C → J → Circle) (Q : D → J → Circle) (H : Z → J → Circle),
      Measurable A ∧ Measurable B ∧ Measurable P ∧ Measurable Q ∧ Measurable H ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap R.a.unitary inferInstance) 2 μX =
        lpMeas ℂ ℂ (MeasurableSpace.comap A inferInstance) 2 μX ∧
      lpMeas ℂ ℂ (MeasurableSpace.comap R.b.unitary inferInstance) 2 μY =
        lpMeas ℂ ℂ (MeasurableSpace.comap B inferInstance) 2 μY ∧
      (∀ᵐ ω ∂μ, H (z ω) = A (x ω) * (B (y ω))⁻¹) ∧
      (∀ᵐ ω ∂μ, H (z ω) = P (c ω) * (Q (d ω))⁻¹) := by
  obtain ⟨a₀,b₀,d₀,S,hS,hAB,hCD,hρ,hτ,hcomm,hinv⟩ := hR
  let na := StrongUnitary.normalizeA a₀ d₀
  let nb := StrongUnitary.normalizeB b₀
  let nc := StrongUnitary.normalizeC a₀ b₀ d₀
  let nd := StrongUnitary.normalizeD d₀
  have hna : Measurable na := (StrongUnitary.continuous_normalizeA a₀ d₀).measurable
  have hnb : Measurable nb := (StrongUnitary.continuous_normalizeB b₀).measurable
  have hnc : Measurable nc := (StrongUnitary.continuous_normalizeC a₀ b₀ d₀).measurable
  have hnd : Measurable nd := (StrongUnitary.continuous_normalizeD d₀).measurable
  let aa := na ∘ R.a.unitary
  let bb := nb ∘ R.b.unitary
  let cc := nc ∘ R.p.unitary
  let dd := nd ∘ R.q.unitary
  have ha : Measurable aa := hna.comp R.a.measurable
  have hb : Measurable bb := hnb.comp R.b.measurable
  have hc : Measurable cc := hnc.comp R.p.measurable
  have hd : Measurable dd := hnd.comp R.q.measurable
  let ρ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) :=
    ⟨μX.map aa,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) ha.aemeasurable⟩
  let τ : ProbabilityMeasure (H₄ ≃ₗᵢ[ℂ] H₄) :=
    ⟨μC.map cc,(fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hc.aemeasurable⟩
  have hρeq : (μX.map R.a.unitary).map na = (ρ : Measure _) :=
    Measure.map_map hna R.a.measurable
  have hτeq : (μC.map R.p.unitary).map nc = (τ : Measure _) :=
    Measure.map_map hnc R.p.measurable
  change (μX.map R.a.unitary).map na = (μY.map R.b.unitary).map nb at hAB
  change (μC.map R.p.unitary).map nc = (μD.map R.q.unitary).map nd at hCD
  have hab : μY.map bb = (ρ : Measure _) :=
    (Measure.map_map hnb R.b.measurable).symm.trans (hAB.symm.trans hρeq)
  have hcd : μD.map dd = (τ : Measure _) :=
    (Measure.map_map hnd R.q.measurable).symm.trans (hCD.symm.trans hτeq)
  let α := κ.map (Prod.map aa bb)
  let β := ξ.map (Prod.map cc dd)
  let : IsMarkovKernel α := Kernel.IsMarkovKernel.map κ (ha.prodMap hb)
  let : IsMarkovKernel β := Kernel.IsMarkovKernel.map ξ (hc.prodMap hd)
  have hα : HasCondDistrib (fun ω => (aa (x ω),bb (y ω))) z α μ := hκ.comp_left (ha.prodMap hb)
  have hβ : HasCondDistrib (fun ω => (cc (c ω),dd (d ω))) z β μ := hξ.comp_left (hc.prodMap hd)
  have hm : ∀ᵐ v ∂μ.map z, (α v).map Prod.fst = ρ ∧ (α v).map Prod.snd = ρ ∧
      (β v).map Prod.fst = τ ∧ (β v).map Prod.snd = τ := by
    filter_upwards [hκm,hξm] with v hv hw
    dsimp only [α,β]
    rw [kernel_map_pair_fst _ _ ha hb,kernel_map_pair_snd _ _ ha hb,
      kernel_map_pair_fst _ _ hc hd,kernel_map_pair_snd _ _ hc hd,hv.1,hv.2,hw.1,hw.2,hab,hcd]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have hr : ∀ᵐ v ∂μ.map z, ∀ᵐ w ∂(α v).prod (β v), w.1.1*w.2.2 = w.2.1*w.1.2 := by
    have hh := hpair.comp_left ((ha.prodMap hb).prodMap (hc.prodMap hd))
    have he : (κ ×ₖ ξ).map (Prod.map (Prod.map aa bb) (Prod.map cc dd)) = α ×ₖ β :=
      (Kernel.map_prod_map κ ξ (ha.prodMap hb) (hc.prodMap hd)).symm
    rw [he] at hh
    have hr := ConditionalFibres.ae_kernel hh
      (isClosed_eq (continuous_fst.fst.mul continuous_snd.snd)
        (continuous_snd.fst.mul continuous_fst.snd)).measurableSet
      (R.rectangle.mono (fun ω hω => StrongUnitary.normalized_rectangle a₀
        (R.a.unitary (x ω)) b₀ (R.b.unitary (y ω)) (R.p.unitary (c ω)) d₀ (R.q.unitary (d ω)) hω))
    simpa only [Kernel.prod_apply, Pi.mul_apply] using hr
  have hρs : (ρ : Measure _).support = (S : Set (H₄ ≃ₗᵢ[ℂ] H₄)) := by rw [←hρeq]; exact hρ
  have hτs : (τ : Measure _).support = (S : Set (H₄ ≃ₗᵢ[ℂ] H₄)) := by rw [←hτeq]; exact hτ
  have hρi : ∀ g ∈ S, (ρ : Measure _).map (g*·) = ρ := by rw [←hρeq]; exact hinv
  obtain ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,hfa,hfb,hra,hrb⟩ :=
    StrongUnitary.spectral_corner S hS ρ τ hρs hτs hcomm hρi aa bb cc dd
      ⟨ha,rfl⟩ ⟨hb,hab⟩ ⟨hc,rfl⟩ ⟨hd,hcd⟩ α β hα hβ hm hr
  refine ⟨J,hJ,A,B,P,Q,H,hA,hB,hP,hQ,hH,?_,?_,hra,hrb⟩
  · rw [←StrongUnitary.comap_normalizeA a₀ d₀ R.a.unitary]
    exact hfa
  · rw [←StrongUnitary.comap_normalizeB b₀ R.b.unitary]
    exact hfb
end

section
open MeasureTheory
variable {X G : Type*} [TopologicalSpace X] [CompactSpace X] [Group G]

def characterAlgebra (χ : G →* C(X,ℂ)) (hs : ∀ g, star (χ g) = χ g⁻¹) :
    StarSubalgebra ℂ C(X,ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range χ)
  star_mem' := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨g,rfl⟩ := hf
      rw [hs]
      exact Algebra.subset_adjoin ⟨g⁻¹,rfl⟩
    | algebraMap c =>
      exact (Algebra.adjoin ℂ (Set.range χ)).algebraMap_mem (star c)
    | add f g hf hg hfs hgs =>
      rw [star_add]
      exact (Algebra.adjoin ℂ (Set.range χ)).add_mem hfs hgs
    | mul f g hf hg hfs hgs =>
      rw [star_mul]
      exact (Algebra.adjoin ℂ (Set.range χ)).mul_mem hgs hfs

lemma characterAlgebra_span (χ : G →* C(X,ℂ)) (hs : ∀ g, star (χ g) = χ g⁻¹) :
    (characterAlgebra χ hs).toSubmodule = Submodule.span ℂ (Set.range χ) := by
  change (Algebra.adjoin ℂ (Set.range χ)).toSubmodule = _
  rw [Algebra.adjoin_eq_span]
  rw [←MonoidHom.coe_mrange χ, (MonoidHom.mrange χ).closure_eq]

lemma dense_character_span (χ : G →* C(X,ℂ)) (hs : ∀ g, star (χ g) = χ g⁻¹)
    (hsep : ∀ x y : X, x ≠ y → ∃ g, χ g x ≠ χ g y) :
    (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤ := by
  have hA : (characterAlgebra χ hs).SeparatesPoints := by
    intro x y hxy
    obtain ⟨g,hg⟩ := hsep x y hxy
    refine ⟨(χ g : X → ℂ), ⟨χ g, Algebra.subset_adjoin ⟨g,rfl⟩, rfl⟩, hg⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (characterAlgebra χ hs) hA
  have hh := congrArg (fun A : StarSubalgebra ℂ C(X,ℂ) => A.toSubalgebra.toSubmodule) h
  change (characterAlgebra χ hs).toSubmodule.topologicalClosure = ⊤ at hh
  rwa [characterAlgebra_span] at hh

end

section
open MeasureTheory
open scoped ENNReal
variable {I : Type*}

def torusWordCircle : FreeGroup I →* C((I → Circle), Circle) :=
  FreeGroup.lift (fun i => ⟨fun x => x i, continuous_apply i⟩)

def circleMapComplex {X : Type*} [TopologicalSpace X] : C(X,Circle) →* C(X,ℂ) where
  toFun f := ⟨fun x => (f x : ℂ), continuous_subtype_val.comp f.continuous⟩
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

def torusWord : FreeGroup I →* C((I → Circle),ℂ) :=
  circleMapComplex.comp torusWordCircle

lemma torusWord_star (w : FreeGroup I) : star (torusWord w) = torusWord w⁻¹ := by
  ext x
  change star ((torusWordCircle w x : Circle) : ℂ) = (torusWordCircle w⁻¹ x : ℂ)
  rw [map_inv]
  exact (Circle.coe_inv_eq_conj (torusWordCircle w x)).symm

@[simp] lemma torusWord_of (i : I) (x : I → Circle) :
    torusWord (FreeGroup.of i) x = (x i : ℂ) := by
  change (torusWordCircle (FreeGroup.of i) x : ℂ) = _
  simp only [torusWordCircle, FreeGroup.lift_apply_of]
  rfl

lemma torusWord_dense :
    (Submodule.span ℂ (Set.range (torusWord (I := I)))).topologicalClosure = ⊤ := by
  apply dense_character_span _ torusWord_star
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨FreeGroup.of i, ?_⟩
  simpa only [torusWord_of] using (fun h => hi (Subtype.ext h))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
lemma dense_span_image (A : E →L[ℂ] F) (hA : DenseRange A) (s : Set E)
    (hs : (Submodule.span ℂ s).topologicalClosure = ⊤) :
    (Submodule.span ℂ (A '' s)).topologicalClosure = ⊤ := by
  let P := (Submodule.span ℂ (A '' s)).topologicalClosure
  have hspan : Submodule.span ℂ s ≤ P.comap A.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x,hx,rfl⟩)
  have htop : ⊤ ≤ P.comap A.toLinearMap := by
    rw [←hs]
    exact Submodule.topologicalClosure_minimal _ hspan
      ((Submodule.isClosed_topologicalClosure _).preimage A.continuous)
  apply top_unique
  intro x hx
  exact (Submodule.isClosed_topologicalClosure _).closure_subset_iff.mpr
    (Set.range_subset_iff.mpr (fun v => htop (show v ∈ (⊤ : Submodule ℂ E) from trivial)))
    (by rw [hA.closure_range]; trivial : x ∈ closure (Set.range A))

lemma dense_span_continuous_toLp {X J : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (f : J → C(X,ℂ)) (hf : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun j => ContinuousMap.toLp 2 μ ℂ (f j)))).topologicalClosure = ⊤ := by
  have hD : DenseRange (ContinuousMap.toLp 2 μ ℂ : C(X,ℂ) →L[ℂ] Lp ℂ 2 μ) :=
    ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ENNReal) ≠ ∞)
  have h := dense_span_image (ContinuousMap.toLp 2 μ ℂ : C(X,ℂ) →L[ℂ] Lp ℂ 2 μ) hD
    (Set.range f) hf
  simpa only [←Set.range_comp, Function.comp_def] using h

local instance : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

lemma torusWord_L2_dense [Countable I] (μ : Measure (I → Circle)) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (fun w => ContinuousMap.toLp 2 μ ℂ (torusWord (I := I) w)))).topologicalClosure = ⊤ := by
  exact dense_span_continuous_toLp μ (torusWord (I := I)) torusWord_dense

end

variable {I : Type*}

lemma torusWordCircle_of (i : I) (x : I → Circle) :
    torusWordCircle (FreeGroup.of i) x = x i := by
  simp only [torusWordCircle, FreeGroup.lift_apply_of]
  rfl

lemma torusWordCircle_mul (w : FreeGroup I) (x y : I → Circle) :
    torusWordCircle w (x*y) = torusWordCircle w x * torusWordCircle w y := by
  induction w using FreeGroup.induction_on with
  | one => simp only [map_one, ContinuousMap.one_apply, one_mul]
  | of i => simp only [torusWordCircle_of, Pi.mul_apply]
  | inv_of i hi =>
    simp only [map_inv, ContinuousMap.inv_apply, hi, mul_inv_rev]
    exact mul_comm _ _
  | mul a b ha hb =>
    simp only [map_mul, ContinuousMap.mul_apply, ha, hb]
    ac_rfl

lemma torusWordCircle_one (w : FreeGroup I) : torusWordCircle w (1 : I → Circle) = 1 := by
  have h := torusWordCircle_mul w (1 : I → Circle) 1
  simp only [one_mul] at h
  exact mul_left_cancel (by simpa only [mul_one] using h.symm :
    torusWordCircle w 1 * torusWordCircle w 1 = torusWordCircle w 1 * 1)

lemma torusWordCircle_inv (w : FreeGroup I) (x : I → Circle) :
    torusWordCircle w x⁻¹ = (torusWordCircle w x)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [←torusWordCircle_mul, inv_mul_cancel, torusWordCircle_one]

def torusCharacter (w : FreeGroup I) : (I → Circle) →* Circle where
  toFun := torusWordCircle w
  map_one' := torusWordCircle_one w
  map_mul' := torusWordCircle_mul w

lemma torusWord_ratio (w : FreeGroup I) (x y : I → Circle) :
    torusWord w (x*y⁻¹) = torusWord w x * star (torusWord w y) := by
  change (torusCharacter w (x*y⁻¹) : ℂ) =
    (torusCharacter w x : ℂ) * star (torusCharacter w y : ℂ)
  rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
  rfl

lemma torusWord_norm (w : FreeGroup I) (x : I → Circle) : ‖torusWord w x‖ = 1 := by
  change ‖(torusWordCircle w x : ℂ)‖ = 1
  exact Circle.norm_coe _


end Rokhlin

end

end OAI
