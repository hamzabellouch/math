import Mathlib
import OAI.Geometry.CubicTorus.Curvature.MinimizerJacobiEquation
import OAI.Geometry.CubicTorus.Rigidity.TwoVolumeNodal
import OAI.Geometry.CubicTorus.Profiles.GainEnclosure150

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_positive_support_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H)
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0)
    (X : Cover → Cover) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hXp : ∀ m x,X (x+latticeVector m)=X x)
    (hdX : ∀ᵐ z ∂(μ : Measure NormalBundle),fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover)
    (hpos : ∀ᵐ z ∂(μ : Measure NormalBundle),0<⟪N z.1,X z.1⟫) :
    ∃ c : Cover,∃ r : ℝ,0<r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  obtain ⟨hfirst,hsecond⟩ := periodic_minkowski_identities μ H N hN hp hae hCMC hj X hX hXp hdX
  have hm : (μ.mass : ℝ)=2*isoperimetricProfile V := by
    rw [hμ.1,isoperimetricProfile_eq_of_isMinimizerAt hmin]
    ring
  have hH : H≠0 := by
    intro hz
    rw [hz,zero_mul] at hfirst
    have hh := isoperimetricProfile_pos hV
    rw [hm] at hfirst
    nlinarith
  let q (z : NormalBundle) := coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
  let s (z : NormalBundle) := ⟪N z.1,X z.1⟫
  have hq : Continuous q := (normal_curvature_continuous hN).comp normalEmbedding_continuous.fst
  have hs : Continuous s := (hN.continuous.comp normalEmbedding_continuous.fst).inner (𝕜 := ℝ)
    (hX.continuous.comp normalEmbedding_continuous.fst)
  have hqi := hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure NormalBundle))
  have hsi := hs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure NormalBundle))
  have hqsi := (hq.mul hs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure NormalBundle))
  change Integrable (fun z ↦ q z*s z) (μ : Measure NormalBundle) at hqsi
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hnon : ∀ᵐ z ∂(μ : Measure NormalBundle),0≤2*q z-H^2 := by
    filter_upwards [hae,hbd] with z hn hb
    have hh := isMinimizerAt_mean_curvature_bound hV hE hmin hμ hN hp
      (hae.mono fun _ h ↦ h.1) z.1 hb hn.2.1
    rw [hn.2.2] at hh
    exact sub_nonneg.mpr hh
  have hi : Integrable (fun z ↦ (2*q z-H^2)*s z) (μ : Measure NormalBundle) :=
    (((hq.const_mul 2).sub continuous_const).mul hs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz : (∫ z,(2*q z-H^2)*s z ∂(μ : Measure NormalBundle))=0 := by
    have he : (fun z ↦ (2*q z-H^2)*s z)=(fun z ↦ 2*(q z*s z)-H^2*s z) :=
      funext (fun z ↦ by ring)
    rw [he,integral_sub (hqsi.const_mul 2) (hsi.const_mul (H^2)),integral_const_mul,integral_const_mul]
    change 2*(∫ z,q z*s z ∂(μ : Measure NormalBundle))-H^2*(∫ z,s z ∂(μ : Measure NormalBundle))=0
    change (∫ z,q z*s z ∂(μ : Measure NormalBundle))=H*(μ.mass : ℝ) at hsecond
    rw [hsecond]
    change H*(∫ z,s z ∂(μ : Measure NormalBundle))=2*(μ.mass : ℝ) at hfirst
    nlinarith [congrArg (fun t : ℝ ↦ H*t) hfirst]
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (by filter_upwards [hnon,hpos] with z hn hpz; exact mul_nonneg hn hpz.le) hi).mp hz
  have hqvalue : ∀ᵐ z ∂(μ : Measure NormalBundle),q z=H^2/2 := by
    filter_upwards [hzero,hpos] with z hz hpz
    have hh := (mul_eq_zero.mp hz).resolve_right hpz.ne'
    linarith
  have heq : (∫ z,q z ∂(μ : Measure NormalBundle))=H^2*isoperimetricProfile V := by
    rw [integral_congr_ae hqvalue,integral_const,smul_eq_mul,Measure.real_def,
      ←FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hm]
    ring
  obtain ⟨hr0,hr,c,hc⟩ := isMinimizerAt_mean_square_equality_spherical hV hE hmin hc hμ hN hp
    (hae.mono fun _ h ↦ ⟨h.1,h.2.1⟩) hH (hae.mono fun _ h ↦ h.2.2) heq
  exact ⟨c,|2/H|,hr0,hr,hc⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_strict_one_vertex_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (b : Fin 3 → Bool)
    (hsg : ∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative E) →
      if b i then 0<N x i else N x i<0)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (hv : ∀ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    ∃ c : Cover,∃ r : ℝ,0<r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  let c := orientedUpperVertex b (fun _ ↦ false)
  have hgap : ∀ x∈centeredLiftCell c,quotientMap x∈frontier (openRepresentative E) →
      ∀ i : Fin 3,c i-1/2<x i ∧ x i<c i+1/2 := by
    intro x hx hb
    exact isMinimizerAt_one_vertex_gap hV hmin hR b hd hv x hx (frontier_subset_closure hb)
  obtain ⟨X,hX,hXp,hXe,hdX⟩ := exists_boundary_periodic_position c hgap
  obtain ⟨ν,H,M,hM,hMp,hν,hMae,hMb,hCMC,_,hj⟩ :=
    Periodic.isMinimizerAt_stationary_translation_system hV hE hmin
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hν.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hMNeq (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) : M x=N x := by
    obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin x hx
    exact (hw ν hν M hM hMp hMae).trans (hw μ hμ N hN hp hae).symm
  have hpos : ∀ᵐ z ∂(ν : Measure NormalBundle),0<⟪M z.1,X z.1⟫ := by
    filter_upwards [hbd] with z hz
    obtain ⟨y,hy,hq⟩ := exists_centeredLiftCell c z.1
    have hyb : quotientMap y∈frontier (openRepresentative E) := by rwa [hq]
    have hh := isMinimizerAt_strict_support hV hE hmin hR hμ hN hp hae b hsg hyb (hgap y hy hyb)
    have he := hXe y hy hyb
    change X y=y-c at he
    rw [←he] at hh
    obtain ⟨m,hm⟩ := same_quotient_lattice hq
    rw [hm,hp,hXp] at hh
    rwa [hMNeq z.1 hz]
  apply isMinimizerAt_positive_support_spherical hV hE hmin hc hν hM hMp _ hCMC hj X hX hXp _ hpos
  · filter_upwards [hMae,hbd] with z hn hb
    exact ⟨hn,hMb z.1 hb⟩
  · exact hbd.mono (fun z hz ↦ hdX z.1 hz)

theorem isMinimizerAt_nonstandard_occupied_axial_vertex {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ b : Fin 3 → Bool,
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E) ∧
      ∃ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∈openRepresentative E := by
  classical
  obtain ⟨μ,H,N,b,hμ,hN,hp,hae,hb,hsg,hd⟩ := isMinimizerAt_nonstandard_strict_octant hV hmin hc hstd hR
  refine ⟨b,hd,?_⟩
  by_contra hn
  push Not at hn
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have hO : openRepresentative F=openRepresentative E := openRepresentative_congr_ae hFE
  have hRF (i : Fin 3) : F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) :=
    hFE.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [hO]
  have hsgF : ∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
      quotientMap x∈frontier (openRepresentative F) → if b i then 0<N x i else N x i<0 := by rwa [hO]
  have hdF : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F := by rwa [hO]
  have hnF : ∀ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative F := by rwa [hO]
  obtain ⟨c,r,hr0,hr,hbd⟩ := isMinimizerAt_strict_one_vertex_spherical
    ⟨hV.1,by linarith [hV.2]⟩ hF hmF hcF hRF (hμ.congr_ae hFE.symm) hN hp hae b hsgF hdF hnF
  obtain ⟨hvol,hcong⟩ := isMinimizerAt_spherical_standard_ball hV hF hmF hr0 hr hbd
  apply hstd
  unfold StandardRegionAt SmallStandardRegion
  rw [ite_eq_left hV.2]
  obtain ⟨φ,hφ⟩ := hcong
  exact Or.inl ⟨hvol,φ,hFE.symm.trans hφ⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
namespace CubicTorus

lemma CongruentAE.isometry_preimage {E F : Set Torus} (h : CongruentAE E F)
    (φ : Torus ≃ᵢ Torus) : CongruentAE (φ ⁻¹' E) F := by
  obtain ⟨ψ,hψ⟩ := h
  refine ⟨ψ.trans φ.symm,?_⟩
  have hh := (torusIsometry_measurePreserving φ).quasiMeasurePreserving.preimage_ae_eq hψ
  have he : φ ⁻¹' (ψ '' F) = (ψ.trans φ.symm) '' F := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      refine ⟨y,hy,?_⟩
      change φ.symm (ψ y)=x
      rw [he,φ.symm_apply_apply]
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,by simp⟩
  rwa [he] at hh

lemma smallStandardRegion_isometry_preimage {V : ℝ} {E : Set Torus}
    (h : SmallStandardRegion V E) (φ : Torus ≃ᵢ Torus) :
    SmallStandardRegion V (φ ⁻¹' E) := by
  rcases h with ⟨hv,hc⟩|⟨hl,hu,hc⟩|⟨hv,hc⟩
  · exact Or.inl ⟨hv,hc.isometry_preimage φ⟩
  · exact Or.inr (Or.inl ⟨hl,hu,hc.isometry_preimage φ⟩)
  · exact Or.inr (Or.inr ⟨hv,hc.isometry_preimage φ⟩)

lemma standardRegionAt_isometry_preimage {V : ℝ} {E : Set Torus}
    (h : StandardRegionAt V E) (φ : Torus ≃ᵢ Torus) :
    StandardRegionAt V (φ ⁻¹' E) := by
  unfold StandardRegionAt at h ⊢
  split_ifs at h ⊢ with hv
  · exact smallStandardRegion_isometry_preimage h φ
  · exact smallStandardRegion_isometry_preimage h φ

lemma standardRegionAt_isometry_preimage_iff (V : ℝ) (E : Set Torus)
    (φ : Torus ≃ᵢ Torus) : StandardRegionAt V (φ ⁻¹' E) ↔ StandardRegionAt V E := by
  constructor
  · intro h
    have hh := standardRegionAt_isometry_preimage h φ.symm
    have he : φ.symm ⁻¹' (φ ⁻¹' E)=E := by
      ext x
      simp only [Set.mem_preimage,φ.apply_symm_apply]
    rwa [he] at hh
  · exact fun h ↦ standardRegionAt_isometry_preimage h φ

def flatTranslation (a : Torus) : Torus ≃ᵢ Torus where
  toFun := fun z ↦ z+a
  invFun := fun z ↦ z-a
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  isometry_toFun := isometry_iff_dist_eq.mpr fun _ _ ↦ dist_add_right _ _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
namespace CubicTorus

theorem isMinimizerAt_nonstandard_small_side_vertices {V : ℝ}
    (hV : V∈Ioo (0 : ℝ) (1/2)) {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hstd : ¬StandardRegionAt V E) :
    ∃ (a : Torus) (b : Fin 3 →Bool),
      let F := (fun z : Torus ↦ z+a) ⁻¹' E
      IsMinimizerAt V F ∧ ¬StandardRegionAt V F ∧
      (∀ i : Fin 3,F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F)) ∧
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F) ∧
      (∃ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∈openRepresentative F) ∧
      ∀ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then false else true))∉openRepresentative F := by
  have hV01 : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hc : IsPreconnected (frontier (openRepresentative E)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV01 hmin).resolve_right (fun h ↦ hstd h.2.2)
  obtain ⟨a,ha⟩ := isMinimizerAt_common_reflection_origin hV01 hmin hc
  let F := (fun z : Torus ↦ z+a) ⁻¹' E
  have hmF : IsMinimizerAt V F := isMinimizerAt_translation hmin a
  have hsF : ¬StandardRegionAt V F := by
    intro hs
    exact hstd ((standardRegionAt_isometry_preimage_iff V E (flatTranslation a)).mp hs)
  have hcF : IsPreconnected (frontier (openRepresentative F)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV01 hmF).resolve_right (fun h ↦ hsF h.2.2)
  obtain ⟨b,hd,haxis⟩ := isMinimizerAt_nonstandard_occupied_axial_vertex
    ⟨hV.1,hV.2.le⟩ hmF hcF hsF ha
  exact ⟨a,b,hmF,hsF,ha,hd,haxis,
    isMinimizerAt_small_side_no_face_vertex hV hmF hcF ha b hd⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
namespace CubicTorus

lemma three_axes_dichotomy (P : Fin 3 →Prop) (hp : ∃ i,P i)
    (hno : ∀ i,¬P i → ¬(∀ j : Fin 2,P (i.succAbove j))) :
    (∀ i,P i) ∨ ∃ i,∀ j,P j ↔j=i := by
  classical
  by_cases hall : ∀ i,P i
  · exact Or.inl hall
  push Not at hall
  obtain ⟨k,hk⟩ := hall
  have hn := hno k hk
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  obtain ⟨i,hi⟩ := hp
  have hik : i≠k := fun h ↦ hk (h ▸ hi)
  have hikj : i≠k.succAbove j := fun h ↦ hj (h ▸ hi)
  have hkj : k.succAbove j≠k := Fin.succAbove_ne k j
  refine Or.inr ⟨i,fun l ↦ ⟨fun hl ↦ ?_,fun he ↦ he ▸ hi⟩⟩
  have hlk : l≠k := fun h ↦ hk (h ▸ hl)
  have hlkj : l≠k.succAbove j := fun h ↦ hj (h ▸ hl)
  omega

theorem isMinimizerAt_nonstandard_V2_axial_patterns {E : Set Torus}
    (hmin : IsMinimizerAt (1/Real.pi) E) (hstd : ¬StandardRegionAt (1/Real.pi) E) :
    ∃ (a : Torus) (b : Fin 3 →Bool),
      let F := (fun z : Torus ↦ z+a) ⁻¹' E
      IsMinimizerAt (1/Real.pi) F ∧ ¬StandardRegionAt (1/Real.pi) F ∧
      (∀ i : Fin 3,F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F)) ∧
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F) ∧
      (∀ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then false else true))∉openRepresentative F) ∧
      ((∀ i : Fin 3,quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∈openRepresentative F) ∨
        ∃ i : Fin 3,∀ k : Fin 3,
          quotientMap (orientedUpperVertex b (fun j ↦ if j=k then true else false))∈openRepresentative F ↔k=i) := by
  have hV : (1/Real.pi)∈Ioo (0 : ℝ) (1/2) :=
    ⟨by positivity,by rw [div_lt_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]⟩
  obtain ⟨a,b,hmF,hsF,hR,hd,haxis,hface⟩ :=
    isMinimizerAt_nonstandard_small_side_vertices hV hmin hstd
  refine ⟨a,b,hmF,hsF,hR,hd,hface,?_⟩
  exact three_axes_dichotomy _ haxis
    (isMinimizerAt_fixed_downset_not_three_vertices hmF hsF hR b hd)

end CubicTorus

end
end

end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisReflection_eq_coordinateReflection (i : Fin 3) :
    (axisReflection i).torus=coordinateReflectionEquiv i := by
  apply IsometryEquiv.ext
  intro x
  ext j
  change (axisReflection i).torus x j=coordinateReflection i x j
  simp only [axisReflection_torus_apply,coordinateReflection_apply]

lemma quotient_orientedUpperVertex_eq (s b : Fin 3 → Bool) :
    quotientMap (orientedUpperVertex s b)=quotientMap (chamberVertex s b) := by
  have he : orientedUpperVertex s b=chamberVertex s b+
      latticeVector (fun i => if s i then 0 else if b i then 0 else 1) := by
    ext i
    simp only [orientedUpperVertex,upperVertex,chamberVertex,chamberCorner,latticeVector,
      WithLp.ofLp_toLp,PiLp.add_apply]
    cases s i <;> cases b i <;> norm_num
  rw [he,quotientMap_add,quotientMap_latticeVector,add_zero]

theorem isMinimizerAt_chamber_upper_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i) :
    ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE s x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E := by
  have hsign (x : Cover) (hx : x∈upperOctant)
      (hb : quotientMap x∈frontier (openRepresentative E)) (i : Fin 3) :
      if s i then 0≤N x i else N x i≤0 := by
    have hh : quotientMap x∈coordinateHalf i 0 := by
      simpa [chamberCorner] using (mem_coordinateHalf_of_interval (fun _ => true) i
        (show x i∈Ioo (chamberCorner (fun _ => true) i) (chamberCorner (fun _ => true) i+1/2) by
          convert hx i using 1; norm_num [chamberCorner]))
    cases hsi : s i
    · simp only [Bool.false_eq_true,ite_false]
      have hbr : quotientMap (coverCoordinateReflection i x)∈frontier (openRepresentative E) := by
        rw [quotientMap_coordinateReflection]
        change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
        rwa [frontier_reflection_invariant hE i (hs i)]
      have hhr : quotientMap (coverCoordinateReflection i x)∈coordinateHalf i (1/2) := by
        rw [quotientMap_coordinateReflection,←coordinateReflection_preimage_half]
        simpa only [mem_preimage,coordinateReflection_involutive] using hh
      have hn := hsg (coverCoordinateReflection i x) i (by simpa [hsi] using And.intro hbr hhr)
      have he := congrArg (fun v : Cover => v i)
        (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hb)
      simp only [coverCoordinateReflection_apply,ite_true] at he
      linarith
    · simp only [ite_true]
      exact (hsg x i (by simpa [hsi] using And.intro hb hh)).le
  intro x hx y hy hxy hyE
  apply isMinimizerAt_convex_phase_monotone hV hE hm hμ hp ha
    isOpen_upperOctant convex_upperOctant (fun z hz i ↦ ⟨by linarith [(hz i).1],(hz i).2⟩)
    hx hy hyE
  intro z hz hb
  simp only [PiLp.inner_apply,PiLp.sub_apply,RCLike.inner_apply,RCLike.conj_to_real]
  apply Finset.sum_nonneg
  intro i hi
  have hn := hsign z hz hb i
  have ho := hxy i
  cases hsi : s i <;> simp only [hsi,Bool.false_eq_true,ite_false,ite_true] at hn ho
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ho) hn
  · exact mul_nonneg (sub_nonneg.mpr ho) hn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_separator_positive (f : smoothPeriodicScalars)
    (S : Set Torus) (s : Torus → ℝ) (hs : Continuous s)
    (hz : ∀ a ∈ S, s a = 0 → f.val (representative a) = 0) :
    IsPositiveNodalPiece f S {a | a ∈ S ∧ 0 < f.val (representative a) ∧ 0 < s a} := by
  constructor
  · refine ⟨{a | 0 < s a}, isOpen_lt continuous_const hs, ?_⟩
    ext a
    simp only [mem_ofPred_eq, mem_inter_iff]
    tauto
  · refine ⟨{a | 0 ≤ s a}, isClosed_le continuous_const hs, ?_⟩
    ext a
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨ha, hf, hsa⟩
      exact ⟨⟨ha, hf⟩, hsa.le⟩
    · rintro ⟨⟨ha, hf⟩, hsa⟩
      refine ⟨ha, hf, lt_of_le_of_ne hsa ?_⟩
      intro he
      exact (ne_of_gt hf) (hz a ha he.symm)

lemma positiveNodalPiece_separator_negative (f : smoothPeriodicScalars)
    (S : Set Torus) (s : Torus → ℝ) (hs : Continuous s)
    (hz : ∀ a ∈ S, s a = 0 → f.val (representative a) = 0) :
    IsPositiveNodalPiece f S {a | a ∈ S ∧ 0 < f.val (representative a) ∧ s a < 0} := by
  simpa only [neg_pos] using positiveNodalPiece_separator_positive f S (fun a => -s a)
    hs.neg (fun a ha he => hz a ha (neg_eq_zero.mp he))

theorem double_reflection_nodal_vanish (f : smoothPeriodicScalars)
    (S : Set Torus) (r t : Torus → Torus) (s : Torus → ℝ)
    (hs : Continuous s)
    (hr : ∀ a ∈ S, r a ∈ S) (ht : ∀ a ∈ S, t a ∈ S)
    (hfr : ∀ a ∈ S, f.val (representative (r a)) = -f.val (representative a))
    (hft : ∀ a ∈ S, f.val (representative (t a)) = -f.val (representative a))
    (hsr : ∀ a, s (r a) = -s a) (hst : ∀ a, s (t a) = s a)
    (hz : ∀ a ∈ S, s a = 0 → f.val (representative a) = 0)
    (hnodal : ∀ D A : Set Torus, IsPositiveNodalPiece f S D →
      IsPositiveNodalPiece f S A → D.Nonempty → A.Nonempty → ¬Disjoint D A) :
    ∀ a ∈ S, f.val (representative a) = 0 := by
  have hno : ¬ ∃ a ∈ S, 0 < f.val (representative a) := by
    rintro ⟨a, ha, hfa⟩
    let D : Set Torus := {a | a ∈ S ∧ 0 < f.val (representative a) ∧ 0 < s a}
    let A : Set Torus := {a | a ∈ S ∧ 0 < f.val (representative a) ∧ s a < 0}
    have hD := positiveNodalPiece_separator_positive f S s hs hz
    have hA := positiveNodalPiece_separator_negative f S s hs hz
    have hfb : 0 < f.val (representative (t (r a))) := by
      rw [hft (r a) (hr a ha), hfr a ha, neg_neg]
      exact hfa
    have hsb : s (t (r a)) = -s a := by rw [hst, hsr]
    have hsa : s a ≠ 0 := by
      intro he
      exact (ne_of_gt hfa) (hz a ha he)
    have hnon : D.Nonempty ∧ A.Nonempty := by
      rcases lt_or_gt_of_ne hsa with hneg | hpos
      · exact ⟨⟨t (r a), ht (r a) (hr a ha), hfb, by rw [hsb]; linarith⟩,
          ⟨a, ha, hfa, hneg⟩⟩
      · exact ⟨⟨a, ha, hfa, hpos⟩,
          ⟨t (r a), ht (r a) (hr a ha), hfb, by rw [hsb]; linarith⟩⟩
    apply hnodal D A hD hA hnon.1 hnon.2
    rw [Set.disjoint_left]
    intro b hb hc
    exact (not_lt_of_gt hb.2.2) hc.2.2
  intro a ha
  have hle : f.val (representative a) ≤ 0 := le_of_not_gt (fun h => hno ⟨a, ha, h⟩)
  have hge : 0 ≤ f.val (representative a) := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    apply hno
    refine ⟨r a, hr a ha, ?_⟩
    rw [hfr a ha]
    linarith
  exact le_antisymm hle hge

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_odd_periodic_local_identity {R : ℝ} (hR : 0 ≤ R) (hR' : R < 1/2) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      (∀ x, g (-x) = -g x) ∧ ∀ x, |x| ≤ R → g =ᶠ[𝓝 x] id := by
  obtain ⟨g, hg, hp, he⟩ := exists_periodic_local_identity hR hR'
  let f : ℝ → ℝ := fun x => (g x - g (-x))/2
  refine ⟨f, (hg.sub (hg.comp contDiff_id.neg)).div_const 2, ?_, ?_, ?_⟩
  · intro x
    change (g (x+1)-g (-(x+1)))/2=(g x-g (-x))/2
    rw [hp x]
    have h := hp.sub_eq (-x)
    convert congrArg (fun z : ℝ => (g x-z)/2) h using 1; congr 2; ring_nf
  · intro x
    dsimp [f]
    rw [neg_neg]
    ring
  · intro x hx
    have hneg := (he (-x) (by simpa only [abs_neg] using hx)).comp_tendsto
      (continuous_neg.continuousAt : Tendsto (fun y : ℝ => -y) (𝓝 x) (𝓝 (-x)))
    filter_upwards [he x hx, hneg] with y hy hny
    change (g y - g (-y))/2 = y
    change g y=y at hy
    change g (-y)= -y at hny
    rw [hy, hny]
    ring

theorem TrueRadialTube.odd_periodic_transverse_germs {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      (∀ x, g (-x) = -g x) ∧
      ∀ p, (g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id) := by
  obtain ⟨R, hR, hR', hb⟩ := hr.uniform_square_gap
  obtain ⟨g, hg, hp, ho, he⟩ := exists_odd_periodic_local_identity hR hR'
  exact ⟨g, hg, hp, ho, fun p =>
    ⟨he _ ((le_max_left _ _).trans (hb p)), he _ ((le_max_right _ _).trans (hb p))⟩⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem TrueRadialTube.exists_odd_rotation_nodal_restriction {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x)
      (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1),
      (∀ x, g (-x) = -g x) ∧ IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ p,(g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id)) ∧
      ∀ D A : Set Torus,
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (periodicRotationNormalScalar g hg hp c N hN hNp)
          (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  obtain ⟨μ,H,N,hN,hNp,hμ,ha,hu,hCMC,hs,hj⟩ := Periodic.isMinimizerAt_full_jacobi_system hV hE hm
  obtain ⟨g,hg,hp,ho,he⟩ := hr.odd_periodic_transverse_germs
  have hzero := periodicRotationNormalScalar_mean_zero hμ g hg hp c N hN hNp ha
  have hrot : ∀ w ∈ surfaceH1 μ, surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (periodicRotationNormalScalar g hg hp c N hN hNp)) w = 0 := by
    rw [periodicRotationNormalScalar_eq]
    apply isMinimizerAt_rotation_jacobi_from_germs hV hE hm hμ hN hNp ha
      (fun x hx => (hu x hx).1) hCMC hj
    intro x hx
    rw [← hr.boundary_range] at hx
    obtain ⟨p,hpx⟩ := hx
    obtain ⟨m,hm⟩ := same_quotient_lattice hpx.symm
    have h₁ : x 1-c 1-(m 1 : ℝ)=(r p • unitAngle p.2).re := by
      rw [hm]
      simp [latticeVector]
      ring
    have h₂ : x 2-c 2-(m 2 : ℝ)=(r p • unitAngle p.2).im := by
      rw [hm]
      simp [latticeVector]
      ring
    refine ⟨c 1+(m 1 : ℝ),c 2+(m 2 : ℝ),?_,?_⟩
    · simpa only [sub_add_eq_sub_sub] using
        periodicCoordinate_germ g hg hp c 1 x (m 1) (by rw [h₁]; exact (he p).1)
    · simpa only [sub_add_eq_sub_sub] using
        periodicCoordinate_germ g hg hp c 2 x (m 2) (by rw [h₂]; exact (he p).2)
  refine ⟨μ,N,hN,hNp,g,hg,hp,ho,hμ,ha,he,?_⟩
  intro D A hD hA hDn hAn
  exact isMinimizerAt_general_positive_nodal_not_disjoint hV hE hm hr.frontier_preconnected
    hμ N hN hNp ha (fun x hx => (hu x hx).1) hs
    (periodicRotationNormalScalar g hg hp c N hN hNp) hzero hrot hD hA hDn hAn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma odd_periodic_chamberCorner (g : ℝ → ℝ) (hp : Function.Periodic g 1)
    (ho : ∀ x, g (-x) = -g x) (b : Fin 3 → Bool) (i : Fin 3) (x : ℝ) :
    g (-x - chamberCorner b i) = -g (x - chamberCorner b i) := by
  cases hi : b i
  · simpa only [chamberCorner, hi, Bool.false_eq_true, ite_false, sub_zero] using ho x
  · change g (-x - (if b i then (1/2 : ℝ) else 0)) =
      -g (x - (if b i then (1/2 : ℝ) else 0))
    rw [hi, ite_eq_left rfl]
    have he : -x - (1/2 : ℝ) = -(x-1/2)-1 := by ring
    rw [he, hp.sub_eq, ho]

lemma periodicRotationNormalScalar_apply (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c : Cover) (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x) (x : Cover) :
    (periodicRotationNormalScalar g hg hp c N hN hNp).val x =
      g (x 1-c 1)*N x 2-g (x 2-c 2)*N x 1 := by
  rw [periodicRotationNormalScalar_eq]
  simp only [Submodule.coe_sub, Pi.sub_apply, smoothScalarMul, Pi.mul_apply,
    normalComponentScalar_apply]
  rfl

lemma isMinimizerAt_normal_reflection_apply {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (i j : Fin 3) (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {x : Cover} (hx : quotientMap x ∈ frontier (openRepresentative E)) :
    N (coverCoordinateReflection i x) j = if j=i then -N x j else N x j := by
  have h := congrArg (fun y : Cover => y j)
    (isMinimizerAt_normal_reflection hV hE hm hμ hN hNp hae i hs x hx)
  simp only [coverCoordinateReflection_apply] at h
  split_ifs at h ⊢ <;> linarith

lemma isMinimizerAt_rotation_reflection_odd {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (b : Fin 3 → Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (ho : ∀ x,g (-x) = -g x)
    (i : Fin 3) (hi : i=1 ∨ i=2)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {a : Torus} (ha : a ∈ frontier (openRepresentative E)) :
    (periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp).val
        (representative (coordinateReflection i a)) =
      -(periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp).val
        (representative a) := by
  let f := periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp
  have he : f.val (representative (coordinateReflection i a)) =
      f.val (coverCoordinateReflection i (representative a)) := by
    rw [← quotientMap_representative a, ← quotientMap_coordinateReflection]
    rw [quotientMap_representative]
    exact periodic_representative f.property.2 _
  change f.val _ = -f.val _
  rw [he]
  dsimp only [f]
  rw [periodicRotationNormalScalar_apply, periodicRotationNormalScalar_apply]
  have hx : quotientMap (representative a) ∈ frontier (openRepresentative E) := by
    rwa [quotientMap_representative]
  rw [isMinimizerAt_normal_reflection_apply hV hE hm hμ hN hNp hae i 1 hs hx,
    isMinimizerAt_normal_reflection_apply hV hE hm hμ hN hNp hae i 2 hs hx]
  rcases hi with rfl | rfl
  · simp only [coverCoordinateReflection_apply,
      show (2 : Fin 3) ≠ 1 from by decide, ite_true, ite_false, odd_periodic_chamberCorner g hp ho]
    ring
  · simp only [coverCoordinateReflection_apply, show (1 : Fin 3) ≠ 2 from by decide,
      ite_true, ite_false, odd_periodic_chamberCorner g hp ho]
    ring

lemma descent_coordinateSine_other_reflection {i j : Fin 3} (hij : i ≠ j) (a : Torus) :
    coordinateSine i (representative (coordinateReflection j a)) =
      coordinateSine i (representative a) := by
  rw [← quotientMap_representative a, ← quotientMap_coordinateReflection,
    periodic_representative (coordinateSine_periodic i)]
  simp only [coordinateSine, coverCoordinateReflection_apply, ite_eq_right hij]
  rw [quotientMap_representative]

theorem TrueRadialTube.exists_rotation_zero {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (b : Fin 3 → Bool) {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E (chamberCorner b) r)
    (hs₁ : coordinateReflection 1 ⁻¹' E =ᵐ[torusVolume] E)
    (hs₂ : coordinateReflection 2 ⁻¹' E =ᵐ[torusVolume] E) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hNp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ p, let x := coordinateSectionPoint (chamberCorner b) p.1 (r p • unitAngle p.2)
        (r p • unitAngle p.2).re * N x 2 - (r p • unitAngle p.2).im * N x 1 = 0 := by
  obtain ⟨μ,N,hN,hNp,g,hg,hp,ho,hμ,ha,he,hnodal⟩ := hr.exists_odd_rotation_nodal_restriction hV hE hm
  let f := periodicRotationNormalScalar g hg hp (chamberCorner b) N hN hNp
  have hfo (i : Fin 3) (hi : i=1 ∨ i=2)
      (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
      ∀ a ∈ frontier (openRepresentative E), f.val (representative (coordinateReflection i a)) =
        -f.val (representative a) := fun a habd =>
    isMinimizerAt_rotation_reflection_odd hV hE hm hμ hN hNp ha b g hg hp ho i hi hs habd
  have hrS (i : Fin 3) (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
      ∀ a ∈ frontier (openRepresentative E), coordinateReflection i a ∈ frontier (openRepresentative E) := by
    intro a ha
    change a ∈ coordinateReflection i ⁻¹' frontier (openRepresentative E)
    rwa [frontier_reflection_invariant hE i hs]
  have hv := double_reflection_nodal_vanish f (frontier (openRepresentative E))
    (coordinateReflection 1) (coordinateReflection 2) (fun a => coordinateSine 1 (representative a))
    (continuous_periodic_descent (coordinateSine_contDiff 1).continuous (coordinateSine_periodic 1))
    (hrS 1 hs₁) (hrS 2 hs₂) (hfo 1 (Or.inl rfl) hs₁) (hfo 2 (Or.inr rfl) hs₂)
    (descent_coordinateSine_reflection 1)
    (descent_coordinateSine_other_reflection (by decide : (1 : Fin 3) ≠ 2))
    (fun a ha hz => by have h := hfo 1 (Or.inl rfl) hs₁ a ha
                       rw [coordinateReflection_fixed_of_sine_zero 1 hz] at h
                       linarith)
    hnodal
  refine ⟨μ,N,hN,hNp,hμ,ha,?_⟩
  intro p
  let x := coordinateSectionPoint (chamberCorner b) p.1 (r p • unitAngle p.2)
  have hx : quotientMap x ∈ frontier (openRepresentative E) := by
    rw [← hr.boundary_range]
    exact ⟨p,rfl⟩
  have h := hv (quotientMap x) hx
  rw [periodic_representative f.property.2] at h
  change f.val x=0 at h
  dsimp only [f] at h
  rw [periodicRotationNormalScalar_apply] at h
  have hx₁ : x 1-chamberCorner b 1=(r p • unitAngle p.2).re := by simp [x]
  have hx₂ : x 2-chamberCorner b 2=(r p • unitAngle p.2).im := by simp [x]
  rw [hx₁,hx₂,(he p).1.eq_of_nhds,(he p).2.eq_of_nhds] at h
  exact h

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinatePlaneLift_quarter_inner (n : Cover) (z : ℂ) :
    ⟪n,coordinatePlaneLift (Complex.I*z)⟫ = z.re*n 2-z.im*n 1 := by
  rw [coordinatePlaneProjection_inner]
  simp only [coordinatePlaneProjection_re,coordinatePlaneProjection_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,zero_sub]
  ring

lemma coordinatePlaneLift_frame_norm (n : Cover) {z : ℂ} (hz : ‖z‖=1) :
    (n 0)^2+⟪n,coordinatePlaneLift z⟫^2+⟪n,coordinatePlaneLift (Complex.I*z)⟫^2=‖n‖^2 := by
  have hz' : z.re^2+z.im^2=1 := by
    have h := congrArg (fun x : ℝ => x^2) hz
    rw [Complex.sq_norm,Complex.normSq_apply] at h
    nlinarith only [h]
  rw [coordinatePlaneProjection_inner,coordinatePlaneLift_quarter_inner]
  simp only [coordinatePlaneProjection_re,coordinatePlaneProjection_im]
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  nlinarith [congrArg (fun q : ℝ => q*((n 1)^2+(n 2)^2)) hz']

lemma coordinateSectionPoint_axial_hasDerivAt {c : Cover} {a t : ℝ}
    {r : ℝ → ℝ} {d : ℝ} (hr : HasDerivAt r d t) :
    HasDerivAt (fun u => coordinateSectionPoint c u (r u • unitAngle a))
      (EuclideanSpace.single 0 1 + d • coordinatePlaneLift (unitAngle a)) t := by
  have h₁ := (((hasDerivAt_id t).sub_const (c 0)).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).const_add c
  have h₂ := coordinatePlaneLift.hasFDerivAt.comp_hasDerivAt t (hr.smul_const (unitAngle a))
  simpa only [coordinateSectionPoint,sub_zero,one_smul,map_smul,Pi.add_def,Function.comp_def,id_eq] using h₁.add h₂

theorem TrueRadialTube.radial_independent_angle {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hrot : ∀ p, let x := coordinateSectionPoint c p.1 (r p • unitAngle p.2)
      (r p • unitAngle p.2).re*N x 2-(r p • unitAngle p.2).im*N x 1=0) :
    ∀ t a, r (t,a) = r (t,0) := by
  intro t
  have hs : Differentiable ℝ (fun a : ℝ => r (t,a)) :=
    (hr.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hd : ∀ a, deriv (fun a : ℝ => r (t,a)) a=0 := by
    intro a
    let x := coordinateSectionPoint c t (r (t,a) • unitAngle a)
    let n := N x
    let u := coordinatePlaneLift (unitAngle a)
    let w := coordinatePlaneLift (Complex.I*unitAngle a)
    let d := deriv (fun b : ℝ => r (t,b)) a
    let e := deriv (fun b : ℝ => r (b,a)) t
    have hb : quotientMap x ∈ frontier (openRepresentative E) := hr.2.2.2.2.1 (t,a)
    have hn : ‖n‖=1 := isMinimizerAt_normal_unit_boundary hV hE hm hμ hN.continuous hp ha x hb
    have hrpos : 0<r (t,a) := (hr.2.2.2.1 (t,a)).1
    have hw : ⟪n,w⟫=0 := by
      have h := hrot (t,a)
      change (r (t,a) • unitAngle a).re*n 2-(r (t,a) • unitAngle a).im*n 1=0 at h
      simp only [Complex.smul_re,Complex.smul_im,smul_eq_mul] at h
      change ⟪n,coordinatePlaneLift (Complex.I*unitAngle a)⟫=0
      rw [coordinatePlaneLift_quarter_inner]
      apply (mul_eq_zero.mp (show r (t,a)*((unitAngle a).re*n 2-(unitAngle a).im*n 1)=0 by nlinarith)).resolve_left hrpos.ne'
    have ht : n 0+e*⟪n,u⟫=0 := by
      have hr' : Differentiable ℝ (fun b : ℝ => r (b,a)) :=
        (hr.1.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
      have h := isMinimizerAt_boundary_curve_tangent hV hE hm hμ hN hp ha
        (coordinateSectionPoint_axial_hasDerivAt (c := c) (a := a) (hr' t).hasDerivAt)
        (Eventually.of_forall (fun b => hr.2.2.2.2.1 (b,a)))
      simpa only [real_inner_smul_right,inner_add_right,EuclideanSpace.inner_single_right,
        conj_trivial,one_mul] using h
    have hv : d*⟪n,u⟫+(2*Real.pi*r (t,a))*⟪n,w⟫=0 := by
      have h := isMinimizerAt_radial_curve_tangent hV hE hm hμ hN hp ha
        (c := c) (t := t) (fun b => (hs b).hasDerivAt)
        (fun b => by simpa only [radialCurve,← Complex.real_smul] using hr.2.2.2.2.1 (t,b)) a
      have he : radialVelocity (fun b => r (t,b)) (deriv (fun b => r (t,b))) a =
          d • unitAngle a+(2*Real.pi*r (t,a)) • (Complex.I*unitAngle a) := by
        simp only [radialVelocity,Complex.real_smul,d,Complex.ofReal_mul]
        ring
      rw [he,map_add,map_smul,map_smul,inner_add_right,real_inner_smul_right,real_inner_smul_right] at h
      simpa only [radialCurve,← Complex.real_smul] using h
    have hu : ⟪n,u⟫≠0 := by
      intro hu
      have hn0 : n 0=0 := by simpa only [hu,mul_zero,add_zero] using ht
      have h := coordinatePlaneLift_frame_norm n (unitAngle_norm a)
      change (n 0)^2+⟪n,u⟫^2+⟪n,w⟫^2=‖n‖^2 at h
      rw [hn0,hu,hw,hn] at h
      norm_num at h
    have hm : d*⟪n,u⟫=0 := by simpa only [hw,mul_zero,add_zero] using hv
    exact (mul_eq_zero.mp hm).resolve_right hu
  intro a
  exact is_const_of_deriv_eq_zero hs hd a 0

end CubicTorus

end
end

end OAI
