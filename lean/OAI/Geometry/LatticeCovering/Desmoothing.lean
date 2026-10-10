import OAI.Geometry.LatticeCovering.ProjectionBounds

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.Desmoothing
open Set
open scoped RealInnerProductSpace

lemma convex_escape {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {S : Set E} (hS : Convex ℝ S) (hc : IsClosed S)
    {y : E} (hy : y ∉ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ w : E, ‖w-y‖ ≤ δ ∧ ∀ x ∈ S, δ ≤ ‖w-x‖ := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀,hx₀⟩
  · exact ⟨y,by simpa using hδ,by simp⟩
  obtain ⟨L,a,hL,ha⟩ := geometric_hahn_banach_closed_point hS hc hy
  have hLne : L ≠ 0 := by
    intro he
    have hh := (hL x₀ hx₀).trans ha
    simp only [he,zero_apply] at hh
    exact lt_irrefl _ hh
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have hv : v ≠ 0 := by
    intro he
    have h := congrArg (InnerProductSpace.toDual ℝ E) he
    apply hLne
    simpa only [v,LinearIsometryEquiv.apply_symm_apply,map_zero] using h
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖=1 := norm_smul_inv_norm hv
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨y+δ•u,?_,?_⟩
  · simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ,hu,mul_one,le_refl]
  · intro x hx
    have hpos : 0 < ⟪u,y-x⟫ := by
      have he : ⟪v,y-x⟫=L y-L x := by
        rw [inner_sub_right]
        simp only [v,InnerProductSpace.toDual_symm_apply]
      change 0 < ⟪‖v‖⁻¹ • v,y-x⟫
      rw [inner_smul_left,conj_trivial,he]
      exact mul_pos (inv_pos.mpr hvp) (sub_pos.mpr ((hL x hx).trans ha))
    have he : ⟪u,y+δ•u-x⟫=⟪u,y-x⟫+δ := by
      rw [show y+δ•u-x=(y-x)+δ•u by abel,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
      ring
    have H := real_inner_le_norm u (y+δ•u-x)
    rw [he,hu,one_mul] at H
    linarith


end SingleLatticeCovering.Desmoothing

end
end

section

namespace SingleLatticeCovering.Desmoothing
open Set MeasureTheory Isotropization GaussianDensity
open scoped ENNReal RealInnerProductSpace Topology

lemma logConcave_superlevel {k : ℕ} {f : Isotropization.E k → ℝ} (hf : LogConcave f)
    {c : ℝ} (hc : 0 < c) : Convex ℝ {x | c ≤ f x} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_smul,one_smul,zero_add] using hy
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simpa only [hb0,ha1,zero_smul,one_smul,add_zero] using hx
  have H := hf.2 x y a b (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)) hab
  have hprod : c^a*c^b ≤ (f x)^a*(f y)^b :=
    mul_le_mul (Real.rpow_le_rpow hc.le hx ha) (Real.rpow_le_rpow hc.le hy hb)
      (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (hf.1 x) _)
  rw [←Real.rpow_add hc a b,hab,Real.rpow_one] at hprod
  exact hprod.trans H

lemma density_le_peak {k : ℕ} {b : ℝ} (hb : 0 < b) (z : Isotropization.E k) :
    density b z ≤ (normalizer k b)⁻¹ := by
  unfold density
  exact mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k hb).le)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖z‖]))

lemma density_le_tail {k : ℕ} {b δ : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ)
    {z : Isotropization.E k} (hz : δ ≤ ‖z‖) :
    density b z ≤ (normalizer k b)⁻¹*Real.exp (-b*δ^2) := by
  unfold density
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos k hb).le)
  apply Real.exp_le_exp.mpr
  have hh := pow_le_pow_left₀ hδ hz 2
  nlinarith

lemma integrable_density_mul {k : ℕ} {f : Isotropization.E k → ℝ} (hi : Integrable f volume)
    {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    Integrable (fun x => density b (w-x)*f x) volume := by
  apply hi.bdd_mul (c := (normalizer k b)⁻¹) ((continuous_density k b).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖density b (w-x)‖ ≤ (normalizer k b)⁻¹
    simpa only [Real.norm_eq_abs,abs_of_nonneg (density_pos hb (w-x)).le] using density_le_peak hb (w-x))

lemma integral_density_sub_left {k : ℕ} {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    (∫ x : Isotropization.E k, density b (w-x))=1 := by
  rw [integral_sub_left_eq_self,integral_density hb]

lemma integrable_density_sub_left {k : ℕ} {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    Integrable (fun x : Isotropization.E k => density b (w-x)) volume := by
  have he (x : Isotropization.E k) : density b (w-x)=density b (x-w) := by
    unfold density
    rw [norm_sub_rev]
  simp only [he]
  exact integrable_translated_density hb w

lemma convolution_upper_of_far_superlevel {k : ℕ} {f : Isotropization.E k → ℝ}
    (hi : Integrable f volume) (hn : ∀ x, 0 ≤ f x) (hmass : ∫ x, f x=1)
    {b δ c : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (w : Isotropization.E k)
    (hfar : ∀ x, c ≤ f x → δ ≤ ‖w-x‖) :
    (∫ x : Isotropization.E k, density b (w-x)*f x) ≤ c+(normalizer k b)⁻¹*Real.exp (-b*δ^2) := by
  let q := (normalizer k b)⁻¹*Real.exp (-b*δ^2)
  have hq : 0 ≤ q := mul_nonneg (inv_nonneg.mpr (normalizer_pos k hb).le) (Real.exp_pos _).le
  have hpoint (x : Isotropization.E k) : density b (w-x)*f x ≤ c*density b (w-x)+q*f x := by
    by_cases hx : f x ≤ c
    · have H := mul_le_mul_of_nonneg_left hx (density_pos hb (w-x)).le
      nlinarith [mul_nonneg hq (hn x)]
    · have H := mul_le_mul_of_nonneg_right (density_le_tail hb hδ (hfar x (le_of_not_ge hx))) (hn x)
      change density b (w-x)*f x ≤ c*density b (w-x)+q*f x
      linarith [mul_nonneg hc (density_pos hb (w-x)).le]
  have H := integral_mono (integrable_density_mul hi hb w)
    (((integrable_density_sub_left hb w).const_mul c).add (hi.const_mul q)) hpoint
  change (∫ x, density b (w-x)*f x) ≤ ∫ x, c*density b (w-x)+q*f x at H
  rw [integral_add ((integrable_density_sub_left hb w).const_mul c) (hi.const_mul q),
    integral_const_mul,integral_const_mul,integral_density_sub_left hb w,hmass,mul_one,mul_one] at H
  exact H



theorem logConcave_desmoothing {k : ℕ} {f : Isotropization.E k → ℝ} (hf : LogConcave f)
    (hus : UpperSemicontinuous f) (hi : Integrable f volume) (hmass : ∫ x, f x=1)
    {b δ c : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) (hc : 0 < c) (y : Isotropization.E k)
    (hlower : ∀ w : Isotropization.E k, ‖w-y‖ ≤ δ →
      c+(normalizer k b)⁻¹*Real.exp (-b*δ^2) < ∫ x : Isotropization.E k, density b (w-x)*f x) :
    c ≤ f y := by
  by_contra h
  obtain ⟨w,hw,hfar⟩ := convex_escape (logConcave_superlevel hf hc)
    (hus.isClosed_preimage c) h hδ
  exact (not_lt_of_ge (convolution_upper_of_far_superlevel hi hf.1 hmass hb hδ hc.le w hfar)) (hlower w hw)


end SingleLatticeCovering.Desmoothing

end

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Filter Topology Isotropization Sections Prekopa
open scoped ENNReal

noncomputable def canonical {m D : ℕ} (K : Set ((Fin m → ℝ) × E D)) (y : E D) : ℝ :=
  ((volume K)⁻¹).toReal*(volume (fiber K y)).toReal

lemma canonical_nonneg {m D : ℕ} (K : Set ((Fin m → ℝ) × E D)) (y : E D) :
    0 ≤ canonical K y := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma canonical_measurable {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K) :
    Measurable (canonical K) :=
  ((measurable_fiber_measure volume hK.measurableSet).ennreal_toReal).const_mul _

lemma canonical_usc {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K) :
    UpperSemicontinuous (canonical K) := by
  let C := ((volume K)⁻¹).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  intro y t ht
  by_cases hC0 : C=0
  · have hf : canonical K=fun _ => (0 : ℝ) := by funext z; simp [canonical,←show C=((volume K)⁻¹).toReal from rfl,hC0]
    rw [hf] at ht ⊢
    exact Filter.Eventually.of_forall (fun _ => ht)
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have hyt : (volume (fiber K y)).toReal < t/C := (lt_div_iff₀ hCp).mpr (by simpa [canonical,mul_comm,C] using ht)
  have H := upperSemicontinuous_fiber_measure volume hK y (ENNReal.ofReal (t/C))
    ((ENNReal.lt_ofReal_iff_toReal_lt (fiber_compact hK y).measure_ne_top).mpr hyt)
  filter_upwards [H] with z hz
  have hz' := (ENNReal.lt_ofReal_iff_toReal_lt (fiber_compact hK z).measure_ne_top).mp hz
  simpa [canonical,C,mul_comm] using (lt_div_iff₀ hCp).mp hz'

lemma canonical_map {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K)
    (hK0 : volume K ≠ 0) :
    Measure.map Prod.snd ((volume K)⁻¹ • volume.restrict K)=
      volume.withDensity (fun y => ENNReal.ofReal (canonical K y)) := by
  have hct : (volume K)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hK0
  have hf (y : E D) : ENNReal.ofReal (canonical K y)= (volume K)⁻¹*volume (fiber K y) := by
    rw [canonical,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hct,
      ENNReal.ofReal_toReal (fiber_compact hK y).measure_ne_top]
  have H := map_snd_uniform (volume : Measure (Fin m → ℝ)) (volume : Measure (E D)) hK.measurableSet
  change Measure.map Prod.snd ((volume K)⁻¹ • volume.restrict K)=
    volume.withDensity (fun y => (volume K)⁻¹*volume (fiber K y)) at H
  simpa only [←hf] using H

lemma canonical_mass {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K)
    (hK0 : volume K ≠ 0) : Integrable (canonical K) volume ∧ (∫ y, canonical K y)=1 := by
  have hmap := canonical_map hK hK0
  have H := congrArg (fun μ : Measure (E D) => μ univ) hmap
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,Set.preimage_univ,
    Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,
    ENNReal.inv_mul_cancel hK0 hK.measure_ne_top,withDensity_apply _ MeasurableSet.univ] at H
  simp only [Measure.restrict_univ] at H
  have hm : AEMeasurable (fun y => ENNReal.ofReal (canonical K y)) volume :=
    (canonical_measurable hK).ennreal_ofReal.aemeasurable
  have hi := integrable_toReal_of_lintegral_ne_top hm (H.symm ▸ ENNReal.one_ne_top)
  have he := integral_toReal hm (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
  simp only [ENNReal.toReal_ofReal (canonical_nonneg K _)] at hi he
  exact ⟨hi,by rw [←H,ENNReal.toReal_one] at he; exact he⟩



end SingleLatticeCovering.CanonicalDensity

end

section
noncomputable section
namespace SingleLatticeCovering.LinearCoordinates
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

lemma map_uniform_coordinates {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    (e : E ≃ₗ[ℝ] F) (K : Set E) :
    Measure.map e ((μ K)⁻¹ • μ.restrict K)=(ν (e '' K))⁻¹ • ν.restrict (e '' K) := by
  let em : E ≃ᵐ F := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let c : ℝ≥0∞ := addHaarScalarFactor (μ.map e) ν
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν).ne'
  have hct : c ≠ ∞ := ENNReal.coe_ne_top
  have hmap : μ.map em=c • ν := isAddLeftInvariant_eq_smul (μ.map e) ν
  have hpre : em ⁻¹' (e '' K)=K := Set.preimage_image_eq _ e.injective
  have hval : μ K=c*ν (e '' K) := by
    have H := congrArg (fun γ : Measure F => γ (e '' K)) hmap
    rw [em.map_apply,hpre] at H
    exact H
  have hrestr : (μ.restrict K).map em=c • ν.restrict (e '' K) := by
    have H := em.restrict_map μ (e '' K)
    rw [hmap,Measure.restrict_smul,hpre] at H
    exact H.symm
  change ((μ K)⁻¹ • μ.restrict K).map em=_
  rw [Measure.map_smul _ em.measurable.aemeasurable,hrestr,smul_smul]
  congr 1
  rw [hval,ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  calc
    c⁻¹*(ν (e '' K))⁻¹*c=(c⁻¹*c)*(ν (e '' K))⁻¹ := by ac_rfl
    _ = (ν (e '' K))⁻¹ := by rw [ENNReal.inv_mul_cancel hc hct,one_mul]


end SingleLatticeCovering.LinearCoordinates

end
end

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Topology Isotropization Sections Prekopa
open scoped ENNReal RealInnerProductSpace

lemma linear_body_properties {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗ[ℝ] F) {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let H := e.toContinuousLinearEquiv.toHomeomorph
  refine ⟨hK.image H.continuous,hc.linear_image e.toLinearMap,?_⟩
  change (interior (H '' K)).Nonempty
  rw [←H.image_interior]
  exact hi.image H

lemma image_volume_ne_zero {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hi : (interior K).Nonempty) : volume (e '' K) ≠ 0 := by
  have hJ : (interior (e '' K)).Nonempty := by
    change (interior (e.toContinuousLinearEquiv.toHomeomorph '' K)).Nonempty
    rw [←e.toContinuousLinearEquiv.toHomeomorph.image_interior]
    exact hi.image e
  exact ne_of_gt ((isOpen_interior.measure_pos volume hJ).trans_le (measure_mono interior_subset))

lemma projected_uniform_density {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K) :
    μ.map (fun x => (e x).2)=volume.withDensity (fun y => ENNReal.ofReal (canonical (e '' K) y)) := by
  let : IsAddHaarMeasure (volume : Measure ((Fin m → ℝ) × Isotropization.E D)) := by
    change IsAddHaarMeasure ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Isotropization.E D)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hJ : IsCompact (e '' K) := hK.image e.toContinuousLinearEquiv.continuous
  rw [hdef]
  change Measure.map (Prod.snd ∘ e.toContinuousLinearEquiv) _ = _
  rw [←Measure.map_map measurable_snd e.toContinuousLinearEquiv.continuous.measurable]
  change Measure.map Prod.snd (Measure.map e _) = _
  rw [LinearCoordinates.map_uniform_coordinates (volume : Measure (Isotropization.E n))
    (volume : Measure ((Fin m → ℝ) × Isotropization.E D)) e K]
  exact canonical_map hJ (image_volume_ne_zero e hi)

lemma projected_convolution {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (b : ℝ) (y : Isotropization.E D) :
    (∫ x, GaussianDensity.density b (y-(e x).2) ∂μ)=
      ∫ z, GaussianDensity.density b (y-z)*canonical (e '' K) z := by
  have H := integral_map (μ := μ) (φ := fun x => (e x).2)
    (f := fun z => GaussianDensity.density b (y-z))
    ((continuous_snd.comp e.toContinuousLinearEquiv.continuous).measurable.aemeasurable)
    (((GaussianDensity.continuous_density D b).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  rw [projected_uniform_density e hK hi μ hdef] at H
  rw [←H]
  have hJ : IsCompact (e '' K) := hK.image e.toContinuousLinearEquiv.continuous
  have HH := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure (Isotropization.E D)))
    (f := fun z => ENNReal.ofReal (canonical (e '' K) z))
    (g := fun z => GaussianDensity.density b (y-z))
    ((canonical_measurable hJ).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))
  simpa only [ENNReal.toReal_ofReal (canonical_nonneg _ _),smul_eq_mul,mul_comm] using HH


end SingleLatticeCovering.CanonicalDensity

end

section
noncomputable section
namespace SingleLatticeCovering.LinearCoordinates
open LinearMap Module



theorem exists_coordinates {m D : ℕ}
    (A : EuclideanSpace ℝ (Fin (m+D)) →ₗ[ℝ] EuclideanSpace ℝ (Fin D))
    (hA : Function.Surjective A) :
    ∃ e : EuclideanSpace ℝ (Fin (m+D)) ≃ₗ[ℝ] ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D)),
      ∀ x, (e x).2=A x := by
  obtain ⟨R,hR⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  have hR' (y : EuclideanSpace ℝ (Fin D)) : A (R y)=y := by
    have H := LinearMap.congr_fun hR y
    simpa only [LinearMap.comp_apply,LinearMap.id_apply] using H
  let p : EuclideanSpace ℝ (Fin (m+D)) →ₗ[ℝ] A.ker :=
    { toFun := fun x => ⟨x-R (A x),by simp only [LinearMap.mem_ker,map_sub,hR',sub_self]⟩
      map_add' := by intro x y; ext; simp only [map_add,Submodule.coe_add]; abel_nf
      map_smul' := by intro a x; ext; simp only [map_smul,Submodule.coe_smul,smul_sub,RingHom.id_apply] }
  have hbi : Function.Bijective (p.prod A) := by
    constructor
    · intro x y hxy
      have h1 := congrArg (fun z : A.ker × EuclideanSpace ℝ (Fin D) => (z.1 : EuclideanSpace ℝ (Fin (m+D)))) hxy
      have h2 := congrArg Prod.snd hxy
      change A x=A y at h2
      change x-R (A x)=y-R (A y) at h1
      rw [h2] at h1
      exact sub_left_injective h1
    · rintro ⟨z,y⟩
      refine ⟨(z : EuclideanSpace ℝ (Fin (m+D)))+R y,?_⟩
      have he : A (z+R y)=y := by simp only [map_add,hR',LinearMap.mem_ker.mp z.property,zero_add]
      apply Prod.ext
      · apply Subtype.ext
        change z+R y-R (A (z+R y))=z
        rw [he]
        abel
      · exact he
  let e₀ := LinearEquiv.ofBijective (p.prod A) hbi
  have hker : Module.finrank ℝ A.ker=m := by
    have H := A.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hA,finrank_top,finrank_euclideanSpace_fin,finrank_euclideanSpace_fin] at H
    omega
  let e₁ : A.ker ≃ₗ[ℝ] (Fin m → ℝ) := LinearEquiv.ofFinrankEq _ _ (by simpa only [Module.finrank_fin_fun] using hker)
  refine ⟨e₀.trans (e₁.prodCongr (LinearEquiv.refl ℝ _)),fun x => rfl⟩


end SingleLatticeCovering.LinearCoordinates

end
end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial CanonicalDensity
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def localStep (R : ℝ) : ℝ := 1/(100*(R+1))
noncomputable def tailError (D : ℕ) (r R : ℝ) : ℝ :=
  (normalizer D (r^2/2))⁻¹*Real.exp (-(r^2/2)*(localStep R)^2)

lemma localStep_pos {R : ℝ} (hR : 0 ≤ R) : 0 < localStep R := by unfold localStep; positivity
lemma localStep_le_one {R : ℝ} (hR : 0 ≤ R) : localStep R ≤ 1 := by
  unfold localStep
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith



theorem actual_canonical_lower {m k D : ℕ} (hn : 0 < m+D) (hk : 2 ≤ k)
    {K : Set (Isotropization.E (m+D))} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E (m+D))) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε R : ℝ} (hs : s^2*((m+D : ℕ):ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) (hDε : (D:ℝ)*ε ≤ 1/48) (hR : 0 ≤ R)
    (hloss : shellLoss (m+D) k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss (m+D) k s r T ε ≤ 1/8)
    (herr : projectionError (m+D) D s r ≤ densityFloor D R/128)
    (htail : tailError D r R ≤ densityFloor D R/128) :
    ∃ u : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧
      ∃ e : Isotropization.E (m+D) ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D),
        ∀ y : Isotropization.E D, ‖y‖ ≤ 2*R →
          density (1/(2*u)) y/2 ≤ canonical (e '' K) y := by
  obtain ⟨u,hu,hu4,g,hg⟩ := actual_smoothed_lower hn hk hK hc μ hdef hμ hiso hs hr hT hε hε1 hDε hloss hloss8
  have hu0 : 0 < u := by linarith
  have hr0 : r ≠ 0 := by linarith
  have hb : 0 < r^2/2 := by positivity
  have hδ : 0 ≤ localStep R := (localStep_pos hR).le
  have hδ1 := localStep_le_one hR
  have hfloor := densityFloor_pos D R
  let A : Isotropization.E (m+D) →ₗ[ℝ] Isotropization.E D := s • colLinear g
  have hconv (y : Isotropization.E D) :
      normalizedProjection μ s r g y = ∫ x, density (r^2/2) (y-A x) ∂μ := by
    exact normalizedProjection_kernel μ s r g y
  have hsurj : Function.Surjective A := by
    apply surjective_of_smoothed_lower μ A hb
    intro y hy
    have hyd : ‖y‖ ≤ 2*(R+1) := by rw [hy]; linarith
    have hl := variance_density_floor hu hu4 hR hyd
    have ht : (normalizer D (r^2/2))⁻¹*Real.exp (-(r^2/2)) ≤ tailError D r R := by
      unfold tailError
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos D hb).le)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (localStep R),sq_le_sq₀ hδ (by norm_num : (0:ℝ) ≤ 1) |>.mpr hδ1]
    have H := hg y
    rw [hconv] at H
    linarith
  obtain ⟨e,he⟩ := LinearCoordinates.exists_coordinates A hsurj
  obtain ⟨hJ,hJc,hJi⟩ := linear_body_properties e hK hc hi
  have hmass := canonical_mass hJ (image_volume_ne_zero e hi)
  have heconv (w : Isotropization.E D) : normalizedProjection μ s r g w =
      ∫ z, density (r^2/2) (w-z)*canonical (e '' K) z := by
    rw [hconv]
    simp_rw [←he]
    exact projected_convolution e hK hi μ hdef (r^2/2) w
  refine ⟨u,hu,hu4,e,fun y hy => ?_⟩
  apply Desmoothing.logConcave_desmoothing (f := canonical (e '' K)) (logConcave_canonical_density hJ hJc)
    (canonical_usc hJ) hmass.1 hmass.2 hb hδ (half_pos (density_pos (by positivity) y)) y
  intro w hw
  have hl := variance_density_nearby hu hR hδ (show localStep R ≤ 1/(100*(R+1)) from le_rfl) hy hw
  have hy' : ‖y‖ ≤ 2*(R+1) := by linarith
  have hf := variance_density_floor hu hu4 hR hy'
  have H := hg w
  rw [heconv] at H
  change density (1/(2*u)) y/2+tailError D r R < _
  linarith


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

lemma normalizer_scaling (D : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    normalizer D (b/a^2)=a^D*normalizer D b := by
  unfold normalizer
  rw [show Real.pi/(b/a^2)=a^2*(Real.pi/b) by field_simp,
    Real.mul_rpow (sq_nonneg a) (by positivity),←Real.rpow_natCast a 2,
    ←Real.rpow_mul ha.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*((D:ℝ)/2)=(D:ℝ) by ring,Real.rpow_natCast]

lemma density_scaling {D : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : E D) :
    a^D*density (b/a^2) (a•y)=density b y := by
  rw [density,density,normalizer_scaling D ha hb,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  have hpow : a^D ≠ 0 := pow_ne_zero _ (ne_of_gt ha)
  have hN := ne_of_gt (normalizer_pos D hb)
  have he : -(b/a^2)*(a*‖y‖)^2=-b*‖y‖^2 := by field_simp
  rw [he,mul_inv_rev]
  field_simp

end SingleLatticeCovering.GaussianDensity
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Isotropization Sections
open scoped ENNReal

noncomputable def verticalScale (m D : ℕ) {a : ℝ} (ha : a ≠ 0) :
    ((Fin m → ℝ) × E D) ≃ₗ[ℝ] ((Fin m → ℝ) × E D) :=
  (LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.smulOfNeZero ℝ (E D) a ha)

lemma verticalScale_fiber {m D : ℕ} {a : ℝ} (ha : a ≠ 0)
    (J : Set ((Fin m → ℝ) × E D)) (y : E D) :
    fiber (verticalScale m D ha '' J) y=fiber J (a⁻¹•y) := by
  ext x
  change (x,y) ∈ verticalScale m D ha '' J ↔ (x,a⁻¹•y) ∈ J
  change (x,y) ∈ (verticalScale m D ha).toEquiv '' J ↔ (x,a⁻¹•y) ∈ J
  rw [(verticalScale m D ha).toEquiv.image_eq_preimage_symm]
  rfl

lemma verticalScale_volume {m D : ℕ} {a : ℝ} (ha : 0 < a)
    {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J) :
    volume (verticalScale m D (ne_of_gt ha) '' J)=ENNReal.ofReal (a^D)*volume J := by
  let S := verticalScale m D (ne_of_gt ha)
  have hm : Measurable (fun y : E D => a⁻¹•y) := by fun_prop
  have H := Measure.map_prod_map (volume : Measure (Fin m → ℝ)) (volume : Measure (E D))
    measurable_id hm
  rw [Measure.map_id,Measure.map_addHaar_smul _ (inv_ne_zero (ne_of_gt ha)),
    finrank_euclideanSpace_fin,inv_pow,inv_inv,abs_of_pos (pow_pos ha D),Measure.prod_smul_right] at H
  change ENNReal.ofReal (a^D) • (volume : Measure ((Fin m → ℝ) × E D)) = Measure.map S.symm volume at H
  have HJ := congrArg (fun μ : Measure ((Fin m → ℝ) × E D) => μ J) H
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply (show Measurable S.symm from S.symm.toContinuousLinearEquiv.continuous.measurable) hJ.measurableSet] at HJ
  have he : S.symm ⁻¹' J=S '' J := by
    change S.toEquiv.symm ⁻¹' J=S.toEquiv '' J
    exact S.toEquiv.image_eq_preimage_symm J |>.symm
  rw [he] at HJ
  exact HJ.symm

lemma canonical_verticalScale {m D : ℕ} {a : ℝ} (ha : 0 < a)
    {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J) (y : E D) :
    canonical (verticalScale m D (ne_of_gt ha) '' J) y=(a^D)⁻¹*canonical J (a⁻¹•y) := by
  rw [canonical,verticalScale_fiber,verticalScale_volume ha hJ,
    ENNReal.toReal_inv,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_pos ha D).le,mul_inv_rev]
  unfold canonical
  rw [ENNReal.toReal_inv]
  ring

lemma standardize_lower {m D : ℕ} {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J)
    {u R : ℝ} (hu : 1/4 ≤ u) (hu4 : u ≤ 4) (hR : 0 ≤ R)
    (hlow : ∀ y : E D, ‖y‖ ≤ 2*R → GaussianDensity.density (1/(2*u)) y/2 ≤ canonical J y) :
    ∃ S : ((Fin m → ℝ) × E D) ≃ₗ[ℝ] ((Fin m → ℝ) × E D),
      ∀ y : E D, ‖y‖ ≤ R → GaussianDensity.density (1/2) y/2 ≤ canonical (S '' J) y := by
  have hu0 : 0 < u := by linarith
  have ha := Real.sqrt_pos.mpr hu0
  have ha0 := ne_of_gt ha
  refine ⟨verticalScale m D (inv_ne_zero ha0),fun y hy => ?_⟩
  have ha2 : Real.sqrt u ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
  have hy' : ‖Real.sqrt u•y‖ ≤ 2*R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left hy ha.le).trans (mul_le_mul_of_nonneg_right ha2 hR)
  have H := mul_le_mul_of_nonneg_left (hlow _ hy') (pow_pos ha D).le
  rw [canonical_verticalScale (inv_pos.mpr ha) hJ,inv_inv,inv_pow,inv_inv]
  have hd := GaussianDensity.density_scaling (b := (1:ℝ)/2) ha (by norm_num) y
  rw [Real.sq_sqrt hu0.le,show (1/2:ℝ)/u=1/(2*u) by ring] at hd
  rw [←mul_div_assoc,hd] at H
  exact H


end SingleLatticeCovering.CanonicalDensity

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory Set
open scoped ENNReal

lemma normalizer_inv_bound (D : ℕ) {r : ℝ} (hr : 0 < r) :
    (normalizer D (r^2/2))⁻¹ ≤ r^D := by
  have H := normalizer_scaling D (inv_pos.mpr hr) (by norm_num : (0:ℝ) < 1/2)
  have he : (1/2:ℝ)/(r⁻¹)^2=r^2/2 := by field_simp
  rw [he,inv_pow] at H
  have hN : 1 ≤ normalizer D (1/2) := by
    unfold normalizer
    apply Real.one_le_rpow (by have hp := Real.pi_gt_three; linarith) (by positivity)
  rw [H,mul_inv_rev,inv_inv]
  exact mul_le_of_le_one_left (pow_pos hr D).le ((inv_le_one₀ (normalizer_pos D (by norm_num))).mpr hN)

lemma volume_closedBall_bound (D : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume.real (Metric.closedBall (0:E D) T) ≤ Real.exp (T^2)*normalizer D 1 := by
  have _ := hT
  let B : Set (E D) := Metric.closedBall 0 T
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hkernel := integrable_kernel (k := D) (by norm_num : (0:ℝ) < 1)
  have H := setIntegral_mono_on (integrableOn_const (C := Real.exp (-T^2)) hBc.measure_lt_top.ne)
    hkernel.integrableOn hBc.measurableSet (fun y hy => by
      have hn : ‖y‖ ≤ T := by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hy
      change Real.exp (-T^2) ≤ Real.exp (-1*‖y‖^2)
      apply Real.exp_le_exp.mpr
      nlinarith [pow_le_pow_left₀ (norm_nonneg y) hn 2])
  have hle : (∫ y : E D in B, Real.exp (-1*‖y‖^2)) ≤ normalizer D 1 := by
    rw [←integral_kernel (k := D) (by norm_num : (0:ℝ) < 1)]
    exact setIntegral_le_integral hkernel (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))
  rw [setIntegral_const,smul_eq_mul] at H
  have Hm := mul_le_mul_of_nonneg_right (H.trans hle) (Real.exp_pos (T^2)).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] at Hm
  simpa only [mul_comm] using Hm

lemma normalizer_dimension_mono {D k : ℕ} (hD : D ≤ k) : normalizer D (1/8) ≤ normalizer k (1/8) := by
  unfold normalizer
  apply Real.rpow_le_rpow_of_exponent_le (by have hp := Real.pi_gt_three; linarith)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hD) (by norm_num)

lemma densityFloor_dimension_mono {D k : ℕ} (hD : D ≤ k) (R : ℝ) : densityFloor k R ≤ densityFloor D R := by
  unfold densityFloor
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (normalizer_pos D (by norm_num)) (normalizer_dimension_mono hD))
    (Real.exp_pos _).le

end SingleLatticeCovering.GaussianDensity
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory Set Isotropization GaussianDensity
open scoped ENNReal

lemma root_error_identity {n k : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    projectionError n k (1/Real.sqrt (n:ℝ)) r =
      (normalizer k (r^2/2))⁻¹*r*Real.sqrt (k:ℝ)/Real.sqrt (Real.sqrt (n:ℝ)) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg (n:ℝ))
  have hpos := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn0)
  unfold projectionError
  rw [abs_of_nonneg (by positivity)]
  have hs := Real.sqrt_pos.mpr hn0
  field_simp
  nlinarith only [congrArg (fun z : ℝ => r*z*Real.sqrt (k:ℝ)/(normalizer k (r^2/2))) hsq]

lemma normalization_second {n : ℕ} (hn : 0 < n) : (1/Real.sqrt (n:ℝ))^2*(n:ℝ)=1 := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [div_pow,Real.sq_sqrt hn0.le,one_pow,one_div,inv_mul_cancel₀ hn0.ne']

end SingleLatticeCovering.GaussianProjection

end

section

end

end OAI
