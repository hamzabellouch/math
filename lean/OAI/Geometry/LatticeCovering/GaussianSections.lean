import OAI.Geometry.LatticeCovering.Isotropy

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

lemma map_normalizedRestriction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (K : Set X) :
    (((μ K)⁻¹ • μ.restrict K).map e)=((ν (e '' K))⁻¹ • ν.restrict (e '' K)) := by
  have hval : μ K=ν (e '' K) := by
    rw [←he.map_eq,e.map_apply,Set.preimage_image_eq _ e.injective]
  have hre : (μ.restrict K).map e=ν.restrict (e '' K) := by
    rw [←he.map_eq,e.restrict_map,Set.preimage_image_eq _ e.injective]
  rw [Measure.map_smul _ e.measurable.aemeasurable,hre,hval]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]




lemma canonical_gaussian_coefficient_of_density (μ : Measure E) [IsAddHaarMeasure μ]
    (ν : Measure F) [IsAddHaarMeasure ν] {K : Set (E × F)} (hK : IsCompact K)
    (hK0 : (μ.prod ν) K ≠ 0) {S c : ℝ} (hc : 0 ≤ c)
    {g : F → ℝ≥0∞} (hg : AEMeasurable g ν)
    (heq : Measure.map Prod.snd (((μ.prod ν) K)⁻¹ • (μ.prod ν).restrict K)=ν.withDensity g)
    (hlower : ∀ᵐ y ∂ν, ‖y‖ < S → ENNReal.ofReal (c*gaussian F y) ≤ g y) :
    ∀ y : F, ‖y‖ < S → c*((μ.prod ν) K).toReal*gaussian F y ≤
      (μ (fiber K y)).toReal := by
  have hcont : Continuous (fun y : F => ENNReal.ofReal (c*((μ.prod ν) K).toReal*gaussian F y)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_gaussian)
  have hae : ∀ᵐ y ∂ν, ‖y‖ < S →
      ENNReal.ofReal (c*((μ.prod ν) K).toReal*gaussian F y) ≤ μ (fiber K y) := by
    filter_upwards [canonical_density_ae μ ν hK.measurableSet hg heq,hlower] with y hy hl hys
    rw [←hy] at hl
    have hm := mul_le_mul' (le_refl ((μ.prod ν) K)) (hl hys)
    rw [←mul_assoc,ENNReal.mul_inv_cancel hK0 (hK.measure_ne_top (μ := μ.prod ν)),one_mul] at hm
    have ht := ENNReal.toReal_mono ((fiber_compact hK y).measure_ne_top (μ := μ)) hm
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg hc (gaussian_pos y).le)] at ht
    apply ENNReal.ofReal_le_of_le_toReal
    nlinarith [ht]
  have hall := canonical_marginal_lower μ ν hK hcont hae
  intro y hy
  have hh := ENNReal.toReal_mono ((fiber_compact hK y).measure_ne_top (μ := μ)) (hall y hy)
  rwa [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hc ENNReal.toReal_nonneg) (gaussian_pos y).le)] at hh


end SingleLatticeCovering.Sections

end
end

section


noncomputable section
namespace SingleLatticeCovering.Inputs
open Isotropization Sections Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal RealInnerProductSpace

def orthogonalCoordinates {m D : ℕ} (U : E (m+D) ≃ₗᵢ[ℝ] E (m+D)) :
    E (m+D) ≃ₗ[ℝ] ((Fin m → ℝ) × E D) :=
  U.toLinearEquiv.trans ((WithLp.linearEquiv 2 ℝ (Fin (m+D) → ℝ)).trans (flatten m D).symm)

lemma orthogonalCoordinates_measurePreserving {m D : ℕ}
    (U : E (m+D) ≃ₗᵢ[ℝ] E (m+D)) : MeasurePreserving (orthogonalCoordinates U) volume volume := by
  have hf : MeasurePreserving (flatten m D).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
      volume volume := flatten_measurePreserving m D
  exact hf.symm.comp ((PiLp.volume_preserving_ofLp (Fin (m+D))).comp U.measurePreserving)





def EldanKlartagAt (α β γ C₀ : ℝ) (n : ℕ) : Prop :=
  ∀ m D : ℕ, m+D=n → 0 < D → (D : ℝ) ≤ (n : ℝ)^α →
    ∀ μ : Measure (E (m+D)), IsProbabilityMeasure μ → MemLp id 2 μ → IsIsotropic μ →
      (∃ f : E (m+D) → ℝ, Measurable f ∧ LogConcave f ∧
        μ=volume.withDensity (fun x => ENNReal.ofReal (f x))) →
      ∃ U : E (m+D) ≃ₗᵢ[ℝ] E (m+D), ∃ g : E D → ℝ,
        Measurable g ∧
        μ.map (fun x => (orthogonalCoordinates U x).2)=
          volume.withDensity (fun y => ENNReal.ofReal (g y)) ∧
        ∀ y : E D, ‖y‖ ≤ (n : ℝ)^β →
          |g y / gaussian (E D) y-1| ≤ C₀*(n : ℝ)^(-γ)

lemma gaussian_relative_lower {D : ℕ} {g : E D → ℝ} {y : E D} {ε : ℝ}
    (h : |g y / gaussian (E D) y-1| ≤ ε) :
    (1-ε)*gaussian (E D) y ≤ g y := by
  have hh := (abs_le.mp h).1
  apply (le_div_iff₀ (gaussian_pos y)).mp
  linarith

lemma orthogonalCoordinates_uniform {m D : ℕ}
    (U : E (m+D) ≃ₗᵢ[ℝ] E (m+D)) (K : Set (E (m+D))) :
    (uniformLaw K).map (orthogonalCoordinates U)=
      ((volume (orthogonalCoordinates U '' K))⁻¹ • volume.restrict (orthogonalCoordinates U '' K)) := by
  exact map_normalizedRestriction volume volume
    (orthogonalCoordinates U).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
    (orthogonalCoordinates_measurePreserving U) K

lemma body_marginal_eq {m D : ℕ} {K : Set (E (m+D))}
    (U : E (m+D) ≃ₗᵢ[ℝ] E (m+D)) {g : E D → ℝ}
    (heq : (uniformLaw K).map (fun x => (orthogonalCoordinates U x).2)=
      volume.withDensity (fun y => ENNReal.ofReal (g y))) :
    Measure.map Prod.snd ((volume (orthogonalCoordinates U '' K))⁻¹ •
      volume.restrict (orthogonalCoordinates U '' K))=
      volume.withDensity (fun y => ENNReal.ofReal (g y)) := by
  have hm : Measurable (orthogonalCoordinates U) :=
    (orthogonalCoordinates U).toContinuousLinearEquiv.continuous.measurable
  rw [←orthogonalCoordinates_uniform,Measure.map_map measurable_snd hm]
  exact heq

end SingleLatticeCovering.Inputs

end
end

section

noncomputable section
namespace SingleLatticeCovering.Inputs
open Isotropization Sections Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal RealInnerProductSpace

lemma orthogonalBody_interior {m D : ℕ} (U : E (m+D) ≃ₗᵢ[ℝ] E (m+D))
    {K : Set (E (m+D))} (hi : (interior K).Nonempty) :
    (interior (orthogonalCoordinates U '' K)).Nonempty := by
  let H := (orthogonalCoordinates U).toContinuousLinearEquiv.toHomeomorph
  change (interior (H '' K)).Nonempty
  rw [←H.image_interior]
  exact hi.image H

lemma orthogonalBody_flatten {m D : ℕ} (U : E (m+D) ≃ₗᵢ[ℝ] E (m+D))
    (K : Set (E (m+D))) :
    flatten m D '' (orthogonalCoordinates U '' K)=WithLp.ofLp '' (U '' K) := by
  simp only [Set.image_image]
  congr 1
  funext x
  exact (flatten m D).apply_symm_apply (WithLp.ofLp (U x))




lemma canonical_sections_of_marginal {m D : ℕ} {K : Set (E (m+D))}
    (hK : IsCompact K) (hi : (interior K).Nonempty)
    (U : E (m+D) ≃ₗᵢ[ℝ] E (m+D)) {g : E D → ℝ} (hg : Measurable g)
    (heq : (uniformLaw K).map (fun x => (orthogonalCoordinates U x).2)=
      volume.withDensity (fun y => ENNReal.ofReal (g y)))
    {S ε : ℝ} (hc : 0 ≤ 1-ε)
    (hbound : ∀ y : E D, ‖y‖ ≤ S → |g y/gaussian (E D) y-1| ≤ ε) :
    ∀ y : Fin D → ℝ, ‖WithLp.toLp 2 y‖ < S →
      (1-ε)*(volume (WithLp.ofLp '' (U '' K))).toReal*Folded.gamma y ≤
        (volume (coordinateFiber (WithLp.ofLp '' (U '' K)) y)).toReal := by
  let P := orthogonalCoordinates U '' K
  have hP : IsCompact P := hK.image (orthogonalCoordinates U).toContinuousLinearEquiv.continuous
  have hiP : (interior P).Nonempty := orthogonalBody_interior U hi
  have hP0 : volume P ≠ 0 := ne_of_gt
    ((isOpen_interior.measure_pos volume hiP).trans_le (measure_mono interior_subset))
  have hdensity := body_marginal_eq U heq
  have hlow : ∀ᵐ y : E D ∂volume, ‖y‖ < S →
      ENNReal.ofReal ((1-ε)*gaussian (E D) y) ≤ ENNReal.ofReal (g y) := by
    filter_upwards [] with y hy
    exact ENNReal.ofReal_le_ofReal (gaussian_relative_lower (hbound y (le_of_lt hy)))
  have hall := canonical_gaussian_coefficient_of_density (volume : Measure (Fin m → ℝ))
    (volume : Measure (E D)) hP hP0 hc (ENNReal.measurable_ofReal.comp hg).aemeasurable hdensity hlow
  have hvol : volume (WithLp.ofLp '' (U '' K))=volume P := by
    rw [←orthogonalBody_flatten]
    exact flatten_volume m D hP
  have hfib (y : Fin D → ℝ) : fiber P (WithLp.toLp 2 y)=
      coordinateFiber (WithLp.ofLp '' (U '' K)) y := by
    rw [←orthogonalBody_flatten]
    have hp : (flatten m D).symm '' (flatten m D '' P)=P := (flatten m D).symm_image_image P
    rw [←hp]
    exact flatten_fiber _ _
  intro y hy
  have h := hall (WithLp.toLp 2 y) hy
  rw [hfib,gaussian_toLp] at h
  change (1-ε)*(volume P).toReal*Folded.gamma y ≤ _ at h
  rwa [←hvol] at h


end SingleLatticeCovering.Inputs

end
end

section

noncomputable section
namespace SingleLatticeCovering.Inputs
open Isotropization Sections Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal RealInnerProductSpace





theorem gaussianPositions_of_EldanKlartagAt {α β γ C₀ : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hβ : 0 < β) (herror : C₀*(n : ℝ)^(-γ) ≤ 1)
    (hEK : EldanKlartagAt α β γ C₀ n) : GaussianPositions α (β/2) γ C₀ n := by
  intro m D hsize hD hDn K hK hc hi
  let v : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] E (m+D) :=
    (WithLp.linearEquiv 2 ℝ (Fin (m+D) → ℝ)).symm.toAffineEquiv
  let Hv := (WithLp.linearEquiv 2 ℝ (Fin (m+D) → ℝ)).symm.toContinuousLinearEquiv.toHomeomorph
  have hKv : IsCompact (v '' K) := hK.image Hv.continuous
  have hcv : Convex ℝ (v '' K) := hc.affine_image v.toAffineMap
  have hiv : (interior (v '' K)).Nonempty := by
    change (interior (Hv '' K)).Nonempty
    rw [←Hv.image_interior]
    exact hi.image Hv
  obtain ⟨e,hKe,hce,hie,hprob,hmem,hiso,hf,hlog,hden⟩ :=
    isotropic_logConcave_affine_body hKv hcv hiv
  obtain ⟨U,g,hg,hmap,hbound⟩ := hEK m D hsize hD hDn (uniformLaw (e '' (v '' K)))
    hprob hmem hiso ⟨uniformPdf (e '' (v '' K)),hf,hlog,hden⟩
  let ef : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ) :=
    ((v.trans e).trans U.toLinearEquiv.toAffineEquiv).trans
      (WithLp.linearEquiv 2 ℝ (Fin (m+D) → ℝ)).toAffineEquiv
  have himage : ef '' K=WithLp.ofLp '' (U '' (e '' (v '' K))) := by
    simp only [Set.image_image]
    rfl
  have hcanon := canonical_sections_of_marginal hKe hie U hg hmap (sub_nonneg.mpr herror) hbound
  refine ⟨ef,fun y hy => ?_⟩
  rw [himage]
  apply hcanon y
  apply hy.trans_lt
  have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact Real.rpow_lt_rpow_of_exponent_lt hnreal (by linarith)



theorem gaussianPositions_of_eventual_EldanKlartagAt {α β γ C₀ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ)
    (hEK : ∀ᶠ n : ℕ in atTop, EldanKlartagAt α β γ C₀ n) :
    ∀ᶠ n : ℕ in atTop, GaussianPositions α (β/2) γ C₀ n := by
  have hp : Tendsto (fun n : ℕ => C₀*(n : ℝ)^(-γ)) atTop (𝓝 0) := by
    have hr := tendsto_rpow_neg_atTop hγ
    simpa using (hr.comp tendsto_natCast_atTop_atTop).const_mul C₀
  filter_upwards [hEK,eventually_ge_atTop 2,hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hEK hn he
  exact gaussianPositions_of_EldanKlartagAt hn hβ (le_of_lt he) hEK


end SingleLatticeCovering.Inputs

end
end

section

noncomputable section
namespace SingleLatticeCovering.Horizontal
open Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise

lemma latticeProjection_isOpen {m : ℕ} (L : FullLattice m) :
    IsOpenMap (latticeProjection L.module) := by
  have hp : IsOpenMap (fun x : Fin m → ℝ => fun i => (x i : AddCircle (1 : ℝ))) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall (fun _ => QuotientAddGroup.mk'_surjective _))
  exact hp.comp (latticeBasis L.module).equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenMap



lemma exists_torus_transport {m : ℕ} (L N : FullLattice m)
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hker : ∀ x, e x ∈ N.module ↔ x ∈ L.module) :
    ∃ T : Torus m ≃+ Torus m, Continuous T ∧
      MeasurePreserving T (torusMeasure m) (torusMeasure m) ∧
      ∀ x, T (latticeProjection L.module x)=latticeProjection N.module (e x) := by
  let p := latticeProjection L.module
  let q := (latticeProjection N.module).toAddMonoidHom.comp e.toAddMonoidHom
  have hp : Function.Surjective p := latticeProjection_surjective L.module
  have hq : Function.Surjective q := (latticeProjection_surjective N.module).comp e.surjective
  have heq {x y : Fin m → ℝ} : p x=p y ↔ q x=q y := by
    have h : p (x-y)=0 ↔ q (x-y)=0 :=
      ((latticeProjection_eq_zero_iff L.module (x-y)).trans
      ((hker (x-y)).symm.trans (latticeProjection_eq_zero_iff N.module (e (x-y))).symm))
    simpa only [map_sub,sub_eq_zero] using h
  let lift : Torus m → Torus m := fun t => q (Classical.choose (hp t))
  have hlift (x) : lift (p x)=q x := heq.mp (Classical.choose_spec (hp (p x)))
  let f : Torus m →+ Torus m :=
    { toFun := lift
      map_zero' := by simpa only [map_zero] using hlift 0
      map_add' := by
        intro a b
        obtain ⟨x,rfl⟩ := hp a
        obtain ⟨y,rfl⟩ := hp b
        rw [←map_add,hlift,map_add,hlift,hlift] }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨x,rfl⟩ := hp a
      obtain ⟨y,rfl⟩ := hp b
      exact heq.mpr (by simpa only [f,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hlift] using hab)
    · intro t
      obtain ⟨x,hx⟩ := hq t
      exact ⟨p x,(hlift x).trans hx⟩
  have hcont : Continuous f := by
    apply ((latticeProjection_isOpen L).isQuotientMap p.continuous hp).continuous_iff.mpr
    have hh : (f ∘ p)=q := funext hlift
    rw [hh]
    exact (latticeProjection N.module).continuous.comp e.toContinuousLinearEquiv.continuous
  let T := AddEquiv.ofBijective f hf
  refine ⟨T,hcont,?_,hlift⟩
  exact f.measurePreserving hcont hf.2 rfl

namespace FullLattice

def image {m : ℕ} (L : FullLattice m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) : FullLattice m :=
  ⟨LatticeGeometry.image L.module e,inferInstance,inferInstance⟩

lemma image_covolume {m : ℕ} (L : FullLattice m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) :
    ZLattice.covolume (L.image e).module volume =
      |LinearMap.det e.toLinearMap| * ZLattice.covolume L.module volume :=
  LatticeGeometry.image_covolume L.module e



lemma image_hole {m : ℕ} (L : FullLattice m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    {J : Set (Fin m → ℝ)} (hJ : IsCompact J) : (L.image e).hole (e '' J)=L.hole J := by
  obtain ⟨T,hTc,hTm,hT⟩ := exists_torus_transport L (L.image e) e (by
    intro x
    change e.symm (e x) ∈ L.module ↔ x ∈ L.module
    rw [e.symm_apply_apply])
  have himage : latticeProjection (L.image e).module '' (e '' J)=
      T '' (latticeProjection L.module '' J) := by
    simp only [image_image]
    congr 1
    funext x
    exact (hT x).symm
  have hmeas : MeasurableSet ((latticeProjection (L.image e).module '' (e '' J))ᶜ) :=
    ((hJ.image e.toContinuousLinearEquiv.continuous).image
      (latticeProjection (L.image e).module).continuous).measurableSet.compl
  unfold hole
  rw [←hTm.measure_preimage hmeas.nullMeasurableSet,himage,preimage_compl,
    Set.preimage_image_eq _ T.injective]
end FullLattice

end SingleLatticeCovering.Horizontal

end
end

section

noncomputable section
namespace SingleLatticeCovering.Inputs
open Completion Horizontal MeasureTheory Set Topology
open scoped ENNReal Pointwise




def determinantScale (m : ℕ) (Dh : ℝ) (hDh : 0 < Dh) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
  LinearEquiv.smulOfNeZero ℝ (Fin m → ℝ) (Dh^((m : ℝ)⁻¹))
    (ne_of_gt (Real.rpow_pos_of_pos hDh _))

lemma determinantScale_det {m : ℕ} (hm : 0 < m) (Dh : ℝ) (hDh : 0 < Dh) :
    LinearMap.det (determinantScale m Dh hDh).toLinearMap=Dh := by
  change LinearMap.det (Dh^((m : ℝ)⁻¹) • (LinearMap.id : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)))=Dh
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdim : Module.finrank ℝ (Fin m → ℝ)=m := by simp
  rw [hdim,←Real.rpow_natCast,←Real.rpow_mul hDh.le,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne'),Real.rpow_one]

lemma compact_linear_preimage {m : ℕ} {J : Set (Fin m → ℝ)} (hJ : IsCompact J)
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) : IsCompact (e.symm '' J) :=
  hJ.image e.symm.toContinuousLinearEquiv.continuous

lemma interior_linear_preimage {m : ℕ} {J : Set (Fin m → ℝ)} (hJ : (interior J).Nonempty)
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) : (interior (e.symm '' J)).Nonempty := by
  let H := e.symm.toContinuousLinearEquiv.toHomeomorph
  change (interior (H '' J)).Nonempty
  rw [←H.image_interior]
  exact hJ.image H

lemma determinant_preimage_volume {m : ℕ}
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (Dh : ℝ) (hDh : 0 < Dh)
    (hdet : |LinearMap.det e.toLinearMap|=Dh) (J : Set (Fin m → ℝ)) :
    (volume (e.symm '' J)).toReal=(volume J).toReal/Dh := by
  have h := LatticeGeometry.affine_image_volume e 0 (e.symm '' J)
  have he : (fun x => e x+0) '' (e.symm '' J)=J := by
    simp only [add_zero]
    change e '' (e.symm '' J)=J
    exact e.image_symm_image J
  rw [he,hdet] at h
  have hh := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hDh.le] at hh
  apply (eq_div_iff hDh.ne').mpr
  linarith




def MeanHoleModel.scale {m : ℕ} {CR : ℝ} (M : MeanHoleModel m 1 CR)
    (hm : 0 < m) (Dh : ℝ) (hDh : 0 < Dh) : MeanHoleModel m Dh CR := by
  let e := determinantScale m Dh hDh
  have hdet : |LinearMap.det e.toLinearMap|=Dh := by
    rw [determinantScale_det hm,abs_of_pos hDh]
  letI := M.measurable
  letI : IsProbabilityMeasure M.measure := M.probability
  refine {
    Sample := M.Sample
    measurable := M.measurable
    measure := M.measure
    probability := M.probability
    lattice := fun x => (M.lattice x).image e
    covolume := ?_
    measurable_hole := ?_
    mean := ?_ }
  · intro x
    rw [FullLattice.image_covolume,hdet,M.covolume,mul_one]
  · intro J hJ hc hi
    have hh (x) : ((M.lattice x).image e).hole J=(M.lattice x).hole (e.symm '' J) := by
      have h := (M.lattice x).image_hole e (compact_linear_preimage hJ e)
      have he : e '' (e.symm '' J)=J := e.image_symm_image J
      rwa [he] at h
    simp_rw [hh]
    exact M.measurable_hole _ (compact_linear_preimage hJ e) (hc.linear_image e.symm.toLinearMap)
      (interior_linear_preimage hi e)
  · intro J hJ hc hi hu
    have hh (x) : ((M.lattice x).image e).hole J=(M.lattice x).hole (e.symm '' J) := by
      have h := (M.lattice x).image_hole e (compact_linear_preimage hJ e)
      have he : e '' (e.symm '' J)=J := e.image_symm_image J
      rwa [he] at h
    have hv := determinant_preimage_volume e Dh hDh hdet J
    have hu' : (volume (e.symm '' J)).toReal/1 ≤ FinalRates.eta m := by rwa [hv,div_one]
    have hhmean := M.mean _ (compact_linear_preimage hJ e) (hc.linear_image e.symm.toLinearMap)
      (interior_linear_preimage hi e) hu'
    simp_rw [hh]
    simpa only [div_one,hv,neg_div] using hhmean


end SingleLatticeCovering.Inputs

end
end

section

noncomputable section
namespace SingleLatticeCovering.Assembly
open Inputs MeasureTheory Filter
open scoped Pointwise






theorem main_reduction_to_cited_inputs {α β γ C₀ CR : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀) (hCR : 0 ≤ CR)
    (hEK : ∀ᶠ n : ℕ in atTop, EldanKlartagAt α β γ C₀ n)
    (hRS : ∀ m : ℕ, 2 ≤ m → Nonempty (MeanHoleModel m 1 CR)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  apply all_dimensions_main_reduction hα (div_pos hβ (by norm_num)) hγ hC₀ hCR
    (gaussianPositions_of_eventual_EldanKlartagAt hβ hγ hEK)
  intro m hm Dh hDh
  obtain ⟨M⟩ := hRS m hm
  exact ⟨M.scale (by omega) Dh hDh⟩


end SingleLatticeCovering.Assembly

end
end









noncomputable section
namespace SingleLatticeCovering.FiniteKernel
open Module Submodule MeasureTheory
open scoped BigOperators Pointwise

variable {ι : Type*} [Fintype ι]

abbrev integerLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

def integerCoordinates : integerLattice ι ≃ₗ[ℤ] (ι → ℤ) :=
  ((Pi.basisFun ℝ ι).restrictScalars ℤ).equivFun

lemma integerCoordinates_cast (x : integerLattice ι) (i : ι) :
    ((integerCoordinates x i : ℤ) : ℝ) = (x : ι → ℝ) i := by
  have h := (Pi.basisFun ℝ ι).restrictScalars_repr_apply ℤ x i
  simpa [integerCoordinates] using h

lemma integerLattice_covolume : ZLattice.covolume (integerLattice ι) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume),
    ZSpan.fundamentalDomain_pi_basisFun]
  simp [measureReal_def, volume_pi, Measure.pi_pi, Real.volume_Ico]

variable {U : Type*} [AddCommGroup U]

def kernelLattice (A : integerLattice ι →ₗ[ℤ] U) : Submodule ℤ (ι → ℝ) :=
  (LinearMap.ker A).map (integerLattice ι).subtype

lemma kernelLattice_le (A : integerLattice ι →ₗ[ℤ] U) :
    kernelLattice A ≤ integerLattice ι := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

instance kernelLattice_discrete (A : integerLattice ι →ₗ[ℤ] U) :
    DiscreteTopology (kernelLattice A) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology (integerLattice ι))
    (kernelLattice_le A)

lemma mem_kernelLattice_iff (A : integerLattice ι →ₗ[ℤ] U) (x : integerLattice ι) :
    (x : ι → ℝ) ∈ kernelLattice A ↔ A x = 0 := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    have : y=x := Subtype.ext hxy
    subst y
    exact hy
  · intro h
    exact ⟨x,h,rfl⟩

instance kernelLattice_full [Finite U] (A : integerLattice ι →ₗ[ℤ] U) :
    IsZLattice ℝ (kernelLattice A) where
  span_top := by
    classical
    let : Fintype U := Fintype.ofFinite U
    let q := Fintype.card U
    have hqpos : 0 < q := Fintype.card_pos
    apply top_unique
    rw [←(Pi.basisFun ℝ ι).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let z := (Pi.basisFun ℝ ι).restrictScalars ℤ i
    have hz : (q:ℤ) • (z : ι → ℝ) ∈ kernelLattice A := by
      apply (mem_kernelLattice_iff A ((q:ℤ) • z)).mpr
      rw [map_smul]
      simp [q]
    have hh := (Submodule.span ℝ (kernelLattice A : Set (ι → ℝ))).smul_mem
      ((q:ℝ)⁻¹) (Submodule.subset_span hz)
    have hq : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
    have he : (q:ℝ)⁻¹ • ((q:ℤ) • (z : ι → ℝ)) = (Pi.basisFun ℝ ι) i := by
      ext j
      simp [z, hq]
    rwa [he] at hh

lemma kernelLattice_relIndex (A : integerLattice ι →ₗ[ℤ] U) :
    (kernelLattice A).toAddSubgroup.relIndex (integerLattice ι).toAddSubgroup =
      A.toAddMonoidHom.ker.index := by
  have he : (kernelLattice A).toAddSubgroup.comap (integerLattice ι).toAddSubgroup.subtype =
      A.toAddMonoidHom.ker := by
    ext x
    exact mem_kernelLattice_iff A x
  change ((kernelLattice A).toAddSubgroup.comap (integerLattice ι).toAddSubgroup.subtype).index = _
  rw [he]


theorem kernelLattice_covolume [Finite U] (A : integerLattice ι →ₗ[ℤ] U)
    (hA : Function.Surjective A) :
    ZLattice.covolume (kernelLattice A) = Nat.card U := by
  classical
  have h := ZLattice.covolume_div_covolume_eq_relIndex
    (kernelLattice A) (integerLattice ι) (kernelLattice_le A)
  rw [integerLattice_covolume, div_one, kernelLattice_relIndex] at h
  have hi : A.toAddMonoidHom.ker.index = Nat.card U := by
    rw [AddSubgroup.index_ker]
    have hr : A.toAddMonoidHom.range = ⊤ := AddMonoidHom.range_eq_top.mpr hA
    rw [hr]
    exact Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup U) ≃+ U).toEquiv
  simpa [hi] using h




def gridRelationForm {r d : ℕ} (q : ℕ) (a : Fin r → ℤ) :
    integerLattice (Fin r × Fin d) →ₗ[ℤ] (Fin d → ZMod q) where
  toFun x j := ∑ i, (a i : ZMod q) * (integerCoordinates x (i,j) : ZMod q)
  map_add' x y := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext j
    simp only [map_smul, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, RingHom.id_apply,
      Finset.mul_sum, Int.cast_id]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma gridRelationForm_surjective {r d q : ℕ} (a : Fin r → ℤ)
    (h : ∃ z : Fin r → ℤ, (∑ i, a i*z i : ZMod q) = 1) :
    Function.Surjective (gridRelationForm (d:=d) q a) := by
  classical
  obtain ⟨z,hz⟩ := h
  intro c
  choose k hk using (fun j => ZMod.intCast_surjective (c j))
  refine ⟨integerCoordinates.symm (fun ij => z ij.1*k ij.2),?_⟩
  ext j
  change (∑ i, (a i : ZMod q) *
    (integerCoordinates (integerCoordinates.symm (fun ij : Fin r × Fin d => z ij.1*k ij.2)) (i,j) : ZMod q)) = c j
  simp only [LinearEquiv.apply_symm_apply, Int.cast_mul, ←mul_assoc, ←Finset.sum_mul]
  rw [hz, one_mul, hk]

lemma primitive_bezout_mod {r : ℕ} (a : Fin (r+1) → ℤ)
    (ha : Finset.univ.gcd a = 1) :
    ∃ z : Fin r → ℤ, (∑ i, a i.succ*z i : ZMod (a 0).natAbs) = 1 := by
  obtain ⟨z,hz⟩ := Finset.gcd_eq_sum_mul Finset.univ a
  rw [ha, Fin.sum_univ_succ] at hz
  refine ⟨fun i => z i.succ,?_⟩
  have hcast := congrArg (fun t : ℤ => (t : ZMod (a 0).natAbs)) hz
  have hzero : (a 0 : ZMod (a 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natAbs_dvd.mpr (dvd_refl (a 0))
  simpa [Int.cast_add, Int.cast_mul, Int.cast_sum, hzero] using hcast.symm


theorem primitive_grid_covolume {r d : ℕ} (a : Fin (r+1) → ℤ)
    (ha0 : a 0 ≠ 0) (hprim : Finset.univ.gcd a = 1) :
    ZLattice.covolume (kernelLattice (gridRelationForm (d:=d) (a 0).natAbs (fun i => a i.succ))) =
      |(a 0 : ℝ)|^d := by
  let : NeZero (a 0).natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
  rw [kernelLattice_covolume _ (gridRelationForm_surjective _ (primitive_bezout_mod a hprim)),
    Nat.card_eq_fintype_card, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ZMod.card, Nat.cast_pow]
  simp



end SingleLatticeCovering.FiniteKernel


end
end

end OAI
