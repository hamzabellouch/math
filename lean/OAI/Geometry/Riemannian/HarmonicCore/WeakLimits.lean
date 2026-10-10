import OAI.Geometry.Riemannian.HarmonicCore.CoefficientDifference
import OAI.Geometry.Riemannian.HarmonicCore.WeakDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
theorem bounded_family_test_limit {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : Filter ι} [NeBot f]
    (u : ι → H) (K : ℝ) (hK : ∀ᶠ i in f, ‖u i‖ ≤ K) :
    ∃ w : H, ‖w‖ ≤ K ∧ ∀ (v : H) (l : ℝ),
      Tendsto (fun i ↦ ⟪u i,v⟫_ℝ) f (𝓝 l) → ⟪w,v⟫_ℝ = l := by
  let U : ι → WeakDual ℝ H := fun i ↦ StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u i))
  have hb : Filter.map U f ≤ 𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) K) := by
    rw [Filter.le_principal_iff,Filter.mem_map]
    filter_upwards [hK] with i hi
    simpa [U,Metric.mem_closedBall,dist_zero_right] using hi
  obtain ⟨L,hL,hLc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) K).exists_mapClusterPt hb
  let w : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual L)
  refine ⟨w,?_,?_⟩
  · simpa [w,Metric.mem_closedBall,dist_zero_right] using hL
  · intro v l ht
    have hcl := hLc.continuousAt_comp (WeakDual.eval_continuous v).continuousAt
    have hcl' : MapClusterPt (L v) f (fun i ↦ ⟪u i,v⟫_ℝ) := hcl
    have he : L v = l := eq_of_nhds_neBot (hcl'.clusterPt.mono ht)
    simpa only [w,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply] using he

def HasWeakDirectionalDerivative (u v : ValueL2) (a : E3) : Prop :=
  ∀ R : ℝ, ∀ φ : DirichletTest R,
    ⟪v,testValueLinear R φ⟫_ℝ = -⟪u,testDirection φ a⟫_ℝ

lemma test_finiteDifference_tendsto (R : ℝ) (φ : DirichletTest R) (a : E3) :
    Tendsto (fun h : ℝ ↦ finiteDifferenceL2 a h (testValueLinear R φ))
      (𝓝[≠] 0) (𝓝 (testDirection φ a)) := by
  simpa only [zero_add,zero_smul,translateL2_zero,finiteDifferenceL2_apply] using
    (test_translation_hasDerivAt_zero R φ a).tendsto_slope_zero

theorem bounded_finiteDifference_has_weakDerivative (u : ValueL2) (a : E3) (K : ℝ)
    (hK : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖finiteDifferenceL2 a h u‖ ≤ K) :
    ∃ v : ValueL2, ‖v‖ ≤ K ∧ HasWeakDirectionalDerivative u v a := by
  obtain ⟨v,hv,hvt⟩ := bounded_family_test_limit (fun h : ℝ ↦ finiteDifferenceL2 a h u) K hK
  refine ⟨v,hv,fun R φ ↦ hvt (testValueLinear R φ) (-⟪u,testDirection φ a⟫_ℝ) ?_⟩
  have hn : Tendsto (fun h : ℝ ↦ -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_,?_⟩
    · simpa only [neg_zero] using (continuous_neg.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simpa only [mem_compl_iff,mem_singleton_iff,neg_eq_zero] using hh
  have ht := (test_finiteDifference_tendsto R φ a).comp hn
  have hi : Tendsto (fun h : ℝ ↦ -⟪u,finiteDifferenceL2 a (-h) (testValueLinear R φ)⟫_ℝ)
      (𝓝[≠] 0) (𝓝 (-⟪u,testDirection φ a⟫_ℝ)) :=
    (tendsto_const_nhds.inner (𝕜:=ℝ) ht).neg
  simpa only [finiteDifferenceL2_inner] using hi

lemma smooth_scalar_lipschitz (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (x y : E3) :
    ‖χ y-χ x‖ ≤ D*‖y-x‖ := by
  exact (convex_univ : Convex ℝ (Set.univ : Set E3)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hχ.differentiable (by simp) z)
    (fun z _ ↦ by simpa only [gradient_norm_fderiv] using hD z) (mem_univ x) (mem_univ y)

noncomputable def differenceScalar (χ : E3 → ℝ) (a : E3) (h : ℝ) : E3 → ℝ :=
  fun x ↦ h⁻¹*(χ (x+h • a)-χ x)

lemma differenceScalar_continuous (χ : E3 → ℝ) (hχ : Continuous χ) (a : E3) (h : ℝ) :
    Continuous (differenceScalar χ a h) := by
  have ht : Continuous (fun x : E3 ↦ x+h • a) := continuous_id.add continuous_const
  exact ((hχ.comp ht).sub hχ).const_mul h⁻¹

lemma differenceScalar_bound (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (a : E3) (h : ℝ) :
    ∀ x, ‖differenceScalar χ a h x‖ ≤ D*‖a‖ := by
  intro x
  have hD0 : 0 ≤ D := (norm_nonneg (gradient χ 0)).trans (hD 0)
  by_cases hh : h = 0
  · simp [differenceScalar,hh,mul_nonneg hD0 (norm_nonneg a)]
  · calc
      _ = ‖h‖⁻¹*‖χ (x+h • a)-χ x‖ := by simp only [differenceScalar,norm_mul,norm_inv]
      _ ≤ ‖h‖⁻¹*(D*‖h • a‖) := mul_le_mul_of_nonneg_left
        (by simpa only [add_sub_cancel_left] using smooth_scalar_lipschitz χ hχ D hD x (x+h • a))
        (inv_nonneg.mpr (norm_nonneg _))
      _ = D*‖a‖ := by rw [norm_smul]; field_simp [norm_ne_zero_iff.mpr hh]

noncomputable def differenceScalarCLM {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (h : ℝ) : Lp V 2 (volume : Measure E3) →L[ℝ] Lp V 2 (volume : Measure E3) :=
  scalarFieldCLM (differenceScalar χ a h) (differenceScalar_continuous χ hχ.continuous a h)
    (D*‖a‖) (differenceScalar_bound χ hχ D hD a h)

lemma differenceScalarCLM_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (h : ℝ) (u : Lp V 2 (volume : Measure E3)) :
    (differenceScalarCLM χ hχ D hD a h u : E3 → V) =ᵐ[volume]
      fun x ↦ differenceScalar χ a h x • u x :=
  scalarFieldCLM_coe _ _ _ _ u

lemma differenceScalarCLM_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (h : ℝ) (u : Lp V 2 (volume : Measure E3)) :
    ‖differenceScalarCLM χ hχ D hD a h u‖ ≤ D*‖a‖*‖u‖ :=
  scalarFieldCLM_norm (differenceScalar χ a h) (differenceScalar_continuous χ hχ.continuous a h)
    (D*‖a‖) (differenceScalar_bound χ hχ D hD a h) u

lemma finiteDifference_scalar_product {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (K D : ℝ)
    (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (h : ℝ) (u : Lp V 2 (volume : Measure E3)) :
    finiteDifferenceL2 a h (scalarFieldCLM χ hχ.continuous K hK u) =
      translateL2 (h • a) (scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a (-h) u)) +
        differenceScalarCLM χ hχ D hD a h u := by
  apply Lp.ext
  let Q : Lp V 2 (volume : Measure E3) →L[ℝ] Lp V 2 (volume : Measure E3) := scalarFieldCLM χ hχ.continuous K hK
  let Dχ : Lp V 2 (volume : Measure E3) →L[ℝ] Lp V 2 (volume : Measure E3) := differenceScalarCLM χ hχ D hD a h
  have ht := (measurePreserving_add_right (volume : Measure E3) (h • a)).quasiMeasurePreserving
  filter_upwards [finiteDifferenceL2_coe a h (Q u),scalarFieldCLM_coe χ hχ.continuous K hK u,
    ht.ae (scalarFieldCLM_coe χ hχ.continuous K hK u),
    ht.ae (scalarFieldCLM_coe χ hχ.continuous K hK (finiteDifferenceL2 a (-h) u)),
    ht.ae (finiteDifferenceL2_coe a (-h) u),
    translateL2_coe (h • a) (Q (finiteDifferenceL2 a (-h) u)),
    differenceScalarCLM_coe χ hχ D hD a h u,
    Lp.coeFn_add (translateL2 (h • a) (Q (finiteDifferenceL2 a (-h) u))) (Dχ u)]
    with x h1 h2 h3 h4 h5 h6 h7 h8
  change (finiteDifferenceL2 a h (Q u)) x =
    (translateL2 (h • a) (Q (finiteDifferenceL2 a (-h) u))+Dχ u) x
  rw [h1,h2,h3,h8,Pi.add_apply,h6,h4,h5,h7]
  simp only [neg_smul,add_neg_cancel_right,inv_neg,differenceScalar,smul_sub,mul_smul]
  module

lemma finiteDifference_cutoff_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (K D : ℝ)
    (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (h : ℝ) (u : Lp V 2 (volume : Measure E3)) :
    ‖finiteDifferenceL2 a h (scalarFieldCLM χ hχ.continuous K hK u)‖ ≤
      ‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a (-h) u)‖+D*‖a‖*‖u‖ := by
  rw [finiteDifference_scalar_product χ hχ K D hK hD a h u]
  exact (norm_add_le _ _).trans (add_le_add (by rw [translateL2_norm])
    (differenceScalarCLM_norm χ hχ D hD a h u))

noncomputable def componentL2 (b : E3) : DerivativeL2 →L[ℝ] ValueL2 :=
  (innerSL ℝ b).compLpL 2 volume

lemma componentL2_coe (b : E3) (u : DerivativeL2) :
    (componentL2 b u : E3 → ℝ) =ᵐ[volume] fun x ↦ ⟪b,u x⟫_ℝ :=
  (innerSL ℝ b).coeFn_compLpL u

lemma componentL2_norm (b : E3) (u : DerivativeL2) :
    ‖componentL2 b u‖ ≤ ‖b‖*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [componentL2_coe b u] with x hx
  rw [hx]
  exact norm_inner_le_norm b (u x)

lemma componentL2_translate (b a : E3) (u : DerivativeL2) :
    componentL2 b (translateL2 a u) = translateL2 a (componentL2 b u) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right (volume : Measure E3) a).quasiMeasurePreserving
  filter_upwards [componentL2_coe b (translateL2 a u),translateL2_coe a u,
    translateL2_coe a (componentL2 b u),ht.ae (componentL2_coe b u)] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

lemma componentL2_finiteDifference (b a : E3) (h : ℝ) (u : DerivativeL2) :
    componentL2 b (finiteDifferenceL2 a h u) = finiteDifferenceL2 a h (componentL2 b u) := by
  rw [finiteDifferenceL2_apply,map_smul,map_sub,componentL2_translate,finiteDifferenceL2_apply]

theorem weak_interior_secondDerivative (R S T : ℝ) (hRS : R < S)
    (A : E3 → E3 →L[ℝ] E3) (C L c : ℝ) (hc : 0 < c) (hL0 : 0 ≤ L)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a b : E3) :
    ∃ v : ValueL2,
      ‖v‖ ≤ ‖b‖*((((2*C+2)/c+1)*(D+K*L))+D)*‖a‖*‖sobolevDerivative T u‖ ∧
      HasWeakDirectionalDerivative
        (componentL2 b (scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative T u))) v a := by
  apply bounded_finiteDifference_has_weakDerivative
  have hcont : ContinuousAt (fun h : ℝ ↦ R+‖h • a‖) 0 := by fun_prop
  have he : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), R+‖h • a‖ < S :=
    hcont.eventually (gt_mem_nhds (by simpa only [zero_smul,norm_zero,add_zero] using hRS))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with h hh
  rw [← componentL2_finiteDifference]
  have h1 := finiteDifference_cutoff_bound χ hχ K D hK hD a h (sobolevDerivative T u)
  have h2 := weak_gradient_finiteDifference_bound R S T A C L c hc hL0 hA hC hL hpos u hu
    χ hχ hsupp K D hK hD a (-h) (by simpa only [neg_smul,norm_neg] using hh.le)
  calc
    _ ≤ ‖b‖ * ‖finiteDifferenceL2 a h (scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative T u))‖ := componentL2_norm b _
    _ ≤ ‖b‖ * (‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a (-h) (sobolevDerivative T u))‖ + D*‖a‖*‖sobolevDerivative T u‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg b)
    _ ≤ ‖b‖ * ((((2*C+2)/c+1)*(D+K*L))*‖a‖*‖sobolevDerivative T u‖+D*‖a‖*‖sobolevDerivative T u‖) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 le_rfl) (norm_nonneg b)
    _ = _ := by ring

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
