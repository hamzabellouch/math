import Mathlib
import OAI.Geometry.CubicTorus.Reflection.ChamberPositionProducer

namespace OAI

section

noncomputable section
open Set MeasureTheory
namespace CubicTorus

lemma measurable_sliceJensenG : Measurable sliceJensenG := by
  unfold sliceJensenG
  fun_prop

lemma sliceJensenG_bounds {x : ℝ} (hx : 0≤x) :
    (7/25 : ℝ)≤ sliceJensenG x ∧ sliceJensenG x≤1 := by
  by_cases hxd : sliceJensenCutoff≤x
  · rw [sliceJensenG_cutoff x hxd]; norm_num
  have hd : x<sliceJensenCutoff := lt_of_not_ge hxd
  have hx1 : x<1 := hd.trans sliceJensenCutoff_lt_one
  have hs : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hsq : (Real.sqrt (1-x^2))^2=1-x^2 := Real.sq_sqrt (by nlinarith)
  have hslow : (1/7 : ℝ)≤Real.sqrt (1-x^2) := by
    rw [← sqrt_cutoff]
    apply Real.sqrt_le_sqrt
    nlinarith [sliceJensenCutoff_pos]
  have hsone : Real.sqrt (1-x^2)≤1 := by
    nlinarith [sq_nonneg x,Real.sqrt_nonneg (1-x^2)]
  rw [sliceJensenG,min_eq_left hd.le]
  constructor
  · apply (le_div_iff₀ hs).mpr
    nlinarith [sq_nonneg (7*Real.sqrt (1-x^2)-1)]
  · apply (div_le_one hs).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hsone) (show 0≤49*Real.sqrt (1-x^2)-1 by linarith)]

lemma antitoneOn_sliceJensenG : AntitoneOn sliceJensenG (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0≤x at hx
  change 0≤y at hy
  by_cases hdy : sliceJensenCutoff≤y
  · rw [sliceJensenG_cutoff y hdy]
    exact (sliceJensenG_bounds hx).1
  have hyd : y<sliceJensenCutoff := lt_of_not_ge hdy
  have hxd : x<sliceJensenCutoff := lt_of_le_of_lt hxy hyd
  have hx1 := hxd.trans sliceJensenCutoff_lt_one
  have hy1 := hyd.trans sliceJensenCutoff_lt_one
  have hsx : 0<Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by nlinarith [hx])
  have hsy : 0<Real.sqrt (1-y^2) := Real.sqrt_pos.mpr (by nlinarith [hy])
  have hsqx : (Real.sqrt (1-x^2))^2=1-x^2 := Real.sq_sqrt (by nlinarith [hx])
  have hsqy : (Real.sqrt (1-y^2))^2=1-y^2 := Real.sq_sqrt (by nlinarith [hy])
  have hslow : (1/7 : ℝ)≤Real.sqrt (1-y^2) := by
    rw [← sqrt_cutoff]
    apply Real.sqrt_le_sqrt
    nlinarith [sliceJensenCutoff_pos,hy]
  have hsxy : Real.sqrt (1-y^2)≤Real.sqrt (1-x^2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [hx,hy]
  have hprod : 0≤49*Real.sqrt (1-x^2)*Real.sqrt (1-y^2)-1 := by
    nlinarith [mul_le_mul_of_nonneg_right hslow (le_trans (by norm_num : (0 : ℝ)≤1/7) (hslow.trans hsxy)),
      mul_le_mul_of_nonneg_left (hslow.trans hsxy) (by norm_num : (0 : ℝ)≤1/7)]
  rw [sliceJensenG,sliceJensenG,min_eq_left hyd.le,min_eq_left hxd.le]
  apply (div_le_div_iff₀ hsy hsx).mpr
  have hp := mul_nonneg (sub_nonneg.mpr hsxy) hprod
  nlinarith [hsqx,hsqy]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_area_coordinate_jensen {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγ0 : ∀ v,0≤γ v)
    (hγJ : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      γ (axialSectionArea (openRepresentative E) i t)≤
        sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
          (axialCirclePerimeter (openRepresentative E) i t).toReal)) :
    IntegrableOn γ (Ioo
      (axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2))
      (axialSectionArea (openRepresentative E) i (chamberCorner s i))) ∧
    (49/50 : ℝ)*(μ.mass : ℝ)*axialFluxWeight μ i+
      2*(∫ v in Ioo (axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2))
        (axialSectionArea (openRepresentative E) i (chamberCorner s i)),γ v)≤(μ.mass : ℝ) := by
  obtain ⟨hn,hJi,hJ⟩ := isMinimizerAt_integrated_jensen hV hE hm hμ hN hp ha hs hsg hH i
  have hperiod : axialSectionArea (openRepresentative E) i 1=
      axialSectionArea (openRepresentative E) i 0 := by
    simpa only [zero_add] using axialSectionArea_periodic (openRepresentative E) i 0
  have hanti := isMinimizerAt_antitoneOn_axialSectionArea hV hE hm hμ hN hp ha hs hsg i
  have hends : axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2)≤
      axialSectionArea (openRepresentative E) i (chamberCorner s i) :=
    hanti ⟨le_rfl,by linarith⟩ ⟨by linarith,le_rfl⟩ (by linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ)≤1)] at hJi
  obtain ⟨hgi,hg⟩ := chamber_area_lower_bound
    (isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i)
    (isMinimizerAt_absolutelyContinuous_axialSectionArea hV hE hm hμ hN hp ha hs hsg hH i)
    hperiod (s i) hends hn hJi hγ hγ0 hγJ
  refine ⟨hgi,?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    ← restrict_Ioo_eq_restrict_Ioc] at hJ
  change 2*(∫ v in Ioo (axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2))
    (axialSectionArea (openRepresentative E) i (chamberCorner s i)),γ v)≤_ at hg
  linarith

theorem isMinimizerAt_nonstandard_jensen_system {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmE : IsMinimizerAt V E) (hnstd : ¬SmallStandardRegion V E) :
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (H : ℝ) (s : Fin 3 → Bool),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (∀ i : Fin 3,∀ (γ : ℝ → ℝ),Measurable γ → (∀ v,0≤γ v) →
        (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
          γ (axialSectionArea (openRepresentative F) i t)≤
            sliceJensenG (axialJensenFlux (openRepresentative F) μ H V i t/
              (axialCirclePerimeter (openRepresentative F) i t).toReal)) →
        IntegrableOn γ (Ioo
          (axialSectionArea (openRepresentative F) i (chamberCorner s i+1/2))
          (axialSectionArea (openRepresentative F) i (chamberCorner s i))) ∧
        (49/50 : ℝ)*(μ.mass : ℝ)*axialFluxWeight μ i+
          2*(∫ v in Ioo (axialSectionArea (openRepresentative F) i (chamberCorner s i+1/2))
            (axialSectionArea (openRepresentative F) i (chamberCorner s i)),γ v)≤(μ.mass : ℝ)) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨b,F,μ,N,hN,hp,s,H,hF,he,hmF,hc,hμ,ha,hs,hsg,hH,rest⟩ :=
    isMinimizerAt_nonstandard_section_system hV hmE hnstd
  refine ⟨b,F,μ,H,s,hF,he,hmF,hc,hμ,hH,?_⟩
  intro i γ hγ hγ0 hγJ
  exact isMinimizerAt_area_coordinate_jensen hV' hF hmF hμ hN hp ha hs hsg hH i hγ hγ0 hγJ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma chamberFoldLift_opposite_coordinate (s : Fin 3 → Bool) (i : Fin 3)
    {x : Cover} (hx : x i=chamberCorner s i+1/2) :
    chamberFoldLift s (quotientMap x) i=chamberCorner s i+1/2 := by
  let a := quotientMap x-quotientMap (chamberCorner s)
  have hq : quotientMap (shortestLift a)=quotientMap (x-chamberCorner s) := by
    rw [quotientMap_shortestLift,quotientMap_sub]
  obtain ⟨m,hm⟩ := same_quotient_lattice hq
  have hi := congrArg (fun z : Cover => z i) hm
  change shortestLift a i=x i-chamberCorner s i+(m i : ℝ) at hi
  have hb := abs_shortestLift_coordinate a i
  obtain ⟨hl,hu⟩ := abs_le.mp hb
  have hm0 : m i≤0 := by exact_mod_cast (show (m i : ℝ)≤0 by linarith)
  have hm1 : (-1 : ℤ) ≤ m i := by exact_mod_cast (show (-1 : ℝ)≤(m i : ℝ) by linarith)
  have hm' : m i=0 ∨ m i= -1 := by omega
  rw [chamberFoldLift_apply]
  congr 1
  change |shortestLift a i|=1/2
  rcases hm' with he|he
  · rw [he,Int.cast_zero,hx] at hi
    rw [show shortestLift a i=1/2 by linarith,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  · rw [he,Int.cast_neg,Int.cast_one,hx] at hi
    rw [show shortestLift a i= -(1/2) by linarith,abs_neg,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]

theorem isMinimizerAt_vacant_axial_section {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i) (i : Fin 3)
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    ∀ x : Cover,x i=chamberCorner s i+1/2 → quotientMap x∉closure (openRepresentative E) := by
  intro x hx hxE
  have hsF := fun j => openRepresentative_reflection_invariant hE j (hs j)
  exact isMinimizerAt_vacant_face hV hE hm hμ ha hsg hs i hv
    (chamberFoldLift_mem s (quotientMap x)) (chamberFoldLift_opposite_coordinate s i hx)
    ((chamberFoldLift_mem_iff (reflection_invariant_closure hsF) s (quotientMap x)).mpr hxE)

lemma axialSectionArea_eq_zero_of_empty {E : Set Torus} {i : Fin 3} {t : ℝ}
    (he : ∀ x : Cover,x i=t → quotientMap x∉E) : axialSectionArea E i t=0 := by
  have hz : axialSection E i t=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact he ((axialSplit i).symm (t,y)) (axialSplit_symm_axis i _) hy.2
  simp [axialSectionArea,hz]

lemma axialSectionIntegral_eq_zero_of_empty {E : Set Torus} {i : Fin 3} {t : ℝ}
    (he : ∀ x : Cover,x i=t → quotientMap x∉E) (g : Cover → ℝ) :
    axialSectionIntegral E i g t=0 := by
  unfold axialSectionIntegral
  have hz : ∀ y : Plane,characteristic E (quotientMap ((axialSplit i).symm (t,y)))=0 := by
    intro y
    exact indicator_of_notMem (he _ (axialSplit_symm_axis i _)) _
  simp only [hz,zero_mul,integral_zero]

lemma axialSlicePerimeter_eq_zero_of_empty {E : Set Torus} {i : Fin 3} {t : ℝ}
    (he : ∀ x : Cover,x i=t → quotientMap x∉E) : axialSlicePerimeter E i t=0 := by
  apply le_antisymm _ (by positivity)
  simpa using axialSlicePerimeter_le (q := 0) (fun F _ _ => (axialSectionIntegral_eq_zero_of_empty he (divergence F)).le)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

theorem contDiffAt_continuous_implicit_root {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {f : A × ℝ → ℝ} {r : A → ℝ} {a : A}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (a,r a)) (hr : ContinuousAt r a)
    (hz : ∀ᶠ b in 𝓝 a,f (b,r b)=f (a,r a))
    (hi : (fderiv ℝ f (a,r a) ∘L ContinuousLinearMap.inr ℝ A ℝ).IsInvertible) :
    ContDiffAt ℝ (⊤ : ℕ∞) r a := by
  have hp : ((⊤ : ℕ∞) : WithTop ℕ∞)≠0 := by simp
  have ht : Tendsto (fun b => (b,r b)) (𝓝 a) (𝓝 (a,r a)) := continuousAt_id.prodMk hr
  have he := ht.eventually (hf.eventually_apply_eq_iff_implicitFunction hp hi)
  apply (hf.contDiffAt_implicitFunction hp hi).congr_of_eventuallyEq
  filter_upwards [he,hz] with b hb hbz
  exact ((hb.mp hbz)).symm

lemma real_clm_isInvertible {L : ℝ →L[ℝ] ℝ} (hL : L 1≠0) : L.IsInvertible := by
  have he (t : ℝ) : L t=t*L 1 := by
    simpa only [smul_eq_mul,mul_one] using L.map_smul t (1 : ℝ)
  have hinj : Function.Injective L := by
    intro t u h
    rw [he t,he u] at h
    exact mul_right_cancel₀ hL h
  have hbij : Function.Bijective L :=
    ⟨hinj,(LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv,rfl⟩

theorem contDiffAt_continuous_implicit_root_of_deriv {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {f : A × ℝ → ℝ} {r : A → ℝ} {a : A} {d : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (a,r a)) (hr : ContinuousAt r a)
    (hz : ∀ᶠ b in 𝓝 a,f (b,r b)=f (a,r a))
    (hd : HasDerivAt (fun t => f (a,t)) d (r a)) (hdn : d≠0) :
    ContDiffAt ℝ (⊤ : ℕ∞) r a := by
  apply contDiffAt_continuous_implicit_root hf hr hz
  apply real_clm_isInvertible
  have ht : HasDerivAt (fun t : ℝ => (a,t)) (0,1) (r a) :=
    (hasDerivAt_const (r a) a).prodMk (hasDerivAt_id (r a))
  have hh := (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (r a) ht
  have he := hd.unique hh
  change fderiv ℝ f (a,r a) (0,1)≠0
  rwa [← he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_smooth_boundary_exit {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {γ : A × ℝ → Cover} {r : A → ℝ} {a : A} {v : Cover}
    (hγ : ContDiffAt ℝ (⊤ : ℕ∞) γ (a,r a)) (hr : ContinuousAt r a)
    (hb : ∀ᶠ b in 𝓝 a,quotientMap (γ (b,r b))∈frontier (openRepresentative E))
    (hd : HasDerivAt (fun t => γ (a,t)) v (r a))
    (hv : ⟪N (γ (a,r a)),v⟫≠0) : ContDiffAt ℝ (⊤ : ℕ∞) r a := by
  let x := γ (a,r a)
  have hx : quotientMap x∈frontier (openRepresentative E) := hb.self_of_nhds
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hm hμ hN hp ha x hx
  have hc : N x=σ • graphSlopeNormal n (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  let δ : A × ℝ → Cover := fun p => γ p-x
  let F : A × ℝ → ℝ := fun p => g (normalPlaneCoordinates n (δ p))-⟪n,δ p⟫
  have hδ0 : δ (a,r a)=0 := sub_self _
  have hδ : ContDiffAt ℝ (⊤ : ℕ∞) δ (a,r a) := hγ.sub contDiffAt_const
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) F (a,r a) :=
    (hg.contDiffAt.comp _ ((normalPlaneCoordinates n).contDiff.contDiffAt.comp _ hδ)).sub
      (contDiffAt_const.inner ℝ hδ)
  have hF0 : F (a,r a)=0 := by simp [F,hδ0,hg0]
  have ht : Tendsto (fun b => δ (b,r b)) (𝓝 a) (𝓝 (0 : Cover)) := by
    have he : Tendsto δ (𝓝 (a,r a)) (𝓝 (δ (a,r a))) := hδ.continuousAt
    rw [hδ0] at he
    have hi : Tendsto (fun b : A => (b,r b)) (𝓝 a) (𝓝 (a,r a)) := continuousAt_id.prodMk hr
    exact he.comp hi
  have hz : ∀ᶠ b in 𝓝 a,F (b,r b)=F (a,r a) := by
    filter_upwards [hb,ht.eventually hcover] with b hb' hcov
    have he : x+δ (b,r b)=γ (b,r b) := by dsimp [δ]; abel
    rw [he] at hcov
    have hgph := (normalGraph_coordinates_eq_iff hn _ _).mp (hcov.mp hb')
    change g (normalPlaneCoordinates n (δ (b,r b)))-⟪n,δ (b,r b)⟫=F (a,r a)
    rw [hgph,sub_self,hF0]
  let w := normalPlaneCoordinates n v
  have hδd : HasDerivAt (fun t => δ (a,t)) v (r a) := by
    simpa only [sub_zero] using hd.sub_const x
  have hcd := (normalPlaneCoordinates n).hasFDerivAt.comp_hasDerivAt (r a) hδd
  have hgd := (hg.differentiable (by simp) (0 : Plane)).hasFDerivAt.comp_hasDerivAt_of_eq
    (r a) hcd (by simp [hδ0])
  have hnd := (innerSL ℝ n).hasFDerivAt.comp_hasDerivAt (r a) hδd
  have hFd : HasDerivAt (fun t => F (a,t)) (⟪gradient g 0,w⟫-⟪n,v⟫) (r a) := by
    rw [inner_gradient_left]
    exact hgd.sub hnd
  have hdn : ⟪gradient g 0,w⟫-⟪n,v⟫≠0 := by
    intro he
    apply hv
    change ⟪N x,v⟫=0
    rw [hc,graphSlopeNormal_weight hn,real_inner_smul_left,real_inner_smul_left,inner_sub_left,
      normalPlaneEmbedding_inner_coordinates hn]
    change σ*((cmcWeight (gradient g 0))⁻¹*(⟪n,v⟫-⟪gradient g 0,w⟫))=0
    rw [sub_eq_zero.mp he]
    ring
  exact contDiffAt_continuous_implicit_root_of_deriv hF hr hz hFd hdn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma unitAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) unitAngle := by
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)

theorem isMinimizerAt_smooth_radial_section {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E))
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2))
    (htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E) :
    ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧
      (∀ a,0<r a ∧ r a<unitSquareScale a) ∧
      (∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) t (r a • unitAngle a))∈frontier (openRepresentative E)) ∧
      (∀ a u,0≤u → u≤unitSquareScale a →
        (quotientMap (coordinateSectionPoint (chamberCorner s) t (u • unitAngle a))∈openRepresentative E ↔ u<r a)) ∧
      (∀ a u,0≤u → u≤unitSquareScale a →
        (quotientMap (coordinateSectionPoint (chamberCorner s) t (u • unitAngle a))∈closure (openRepresentative E) ↔ u≤r a)) := by
  let c := chamberCorner s
  let x := coordinateSectionPoint c t 0
  let y : ℝ → Cover := fun a => coordinateSectionPoint c t (unitSquareEnd a)
  have hx : x∈closedHalfBox c := coordinateSectionPoint_mem_box ht (by norm_num)
  have hy (a) : y a∈closedHalfBox c := by
    have hh := unitSquareEnd_coordinates a
    exact coordinateSectionPoint_mem_box ht ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  have hxy (a) (i : Fin 3) : x i≤y a i := by
    have hh := unitSquareEnd_coordinates a
    fin_cases i <;> simp [x,y] <;> first | exact hh.1 | exact hh.2.1
  have hsgc : ∀ z : Cover,quotientMap z∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N z i := by
    intro z hz i
    exact (hsg z i ⟨hz.1,mem_iInter.mp hz.2 i⟩).le
  have hv1' := isMinimizerAt_vacant_axial_section hV hE hm hμ ha hs hsgc 1 hv1
  have hv2' := isMinimizerAt_vacant_axial_section hV hE hm hμ ha hs hsgc 2 hv2
  have hyE (a) : quotientMap (y a)∉closure (openRepresentative E) := by
    rcases (unitSquareEnd_coordinates a).2.2.2.2 with he|he
    · exact hv1' (y a) (by simp [y,c,he])
    · exact hv2' (y a) (by simp [y,c,he])
  obtain ⟨q,hqc,hq,hb,ho,hcl,hf⟩ := isMinimizerAt_chamber_continuous_exit
    hV hE hm hμ hN hp ha hs hsg (continuous_const (y := x))
      (show Continuous y from (coordinateSectionPoint_contDiff c t).continuous.comp unitSquareEnd_continuous)
      (fun _ => hx) hy hxy (fun _ => htE) hyE
  have hqp : Function.Periodic q 1 := by
    intro a
    apply (hf a (q (a+1)) ⟨(hq _).1.le,(hq _).2.le⟩).mp
    simpa only [y,Function.comp_def,unitSquareEnd_periodic a] using hb (a+1)
  let r : ℝ → ℝ := fun a => q a*unitSquareScale a
  have hrc : Continuous r := hqc.mul unitSquareScale_continuous
  have hr (a) : 0<r a ∧ r a<unitSquareScale a := by
    exact ⟨mul_pos (hq a).1 (unitSquareScale_pos a),
      by simpa using mul_lt_mul_of_pos_right (hq a).2 (unitSquareScale_pos a)⟩
  have hsame (a u : ℝ) : chamberSegment x (y a) (u/unitSquareScale a)=
      coordinateSectionPoint c t (u • complexFold (unitAngle a)) := by
    rw [coordinateSectionPoint_segment]
    simp only [unitSquareEnd,smul_smul]
    rw [div_mul_cancel₀ _ (unitSquareScale_pos a).ne']
  have hreflect (F : Set Torus) (hF : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F) (a u : ℝ) (hu : 0≤u) :
      quotientMap (coordinateSectionPoint c t (u • complexFold (unitAngle a)))∈F ↔
        quotientMap (coordinateSectionPoint c t (u • unitAngle a))∈F := by
    rw [← complexFold_smul hu]
    rw [← coordinateSectionPoint_fold s t (u • unitAngle a)]
    exact localChamberFold_mem_iff hF s x _
  have hsO := fun i => openRepresentative_reflection_invariant hE i (hs i)
  have hsC := reflection_invariant_closure hsO
  have hsB := fun i => frontier_reflection_invariant hE i (hs i)
  have hbr (a) : quotientMap (coordinateSectionPoint c t (r a • unitAngle a))∈frontier (openRepresentative E) := by
    apply (hreflect _ hsB a (r a) (hr a).1.le).mp
    rw [← hsame]
    have hh : r a/unitSquareScale a=q a := by dsimp [r]; rw [mul_div_cancel_right₀ _ (unitSquareScale_pos a).ne']
    rw [hh]
    exact hb a
  refine ⟨r,?_,fun a => by simp only [r,hqp a,unitSquareScale_periodic a],hr,hbr,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro a
    let γ : ℝ × ℝ → Cover := fun p => coordinateSectionPoint c t (p.2 • unitAngle p.1)
    have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := (coordinateSectionPoint_contDiff c t).comp
      (contDiff_snd.smul (unitAngle_contDiff.comp contDiff_fst))
    have hder : HasDerivAt (fun u => γ (a,u)) (coordinatePlaneLift (unitAngle a)) (r a) := by
      have hh := coordinatePlaneLift.hasFDerivAt.comp_hasDerivAt (r a)
        ((hasDerivAt_id (r a)).smul_const (unitAngle a))
      simpa only [γ,coordinateSectionPoint,Function.comp_def,one_smul,id_eq] using hh.const_add (c+(t-c 0) • EuclideanSpace.single 0 1)
    have hz : r a • unitAngle a≠0 := smul_ne_zero (hr a).1.ne' (unitAngle_ne_zero a)
    have hgauge : complexSquareGauge (r a • unitAngle a)<1/2 := by
      rw [complexSquareGauge_smul (hr a).1.le]
      have hscl : unitSquareScale a*complexSquareGauge (unitAngle a)=1/2 := by
        dsimp [unitSquareScale]
        field_simp [(complexSquareGauge_pos (unitAngle_ne_zero a)).ne']
      calc
        r a*complexSquareGauge (unitAngle a)<unitSquareScale a*complexSquareGauge (unitAngle a) :=
          mul_lt_mul_of_pos_right (hr a).2 (complexSquareGauge_pos (unitAngle_ne_zero a))
        _=1/2 := hscl
    have hpos := isMinimizerAt_coordinate_plane_transverse hV hE hm hμ hN hp ha hs hsg hz hgauge (hbr a)
    have hne : ⟪N (γ (a,r a)),coordinatePlaneLift (unitAngle a)⟫≠0 := by
      intro he
      rw [map_smul,real_inner_smul_right] at hpos
      change 0<r a*⟪N (γ (a,r a)),coordinatePlaneLift (unitAngle a)⟫ at hpos
      rw [he,mul_zero] at hpos
      exact lt_irrefl _ hpos
    exact isMinimizerAt_smooth_boundary_exit hV hE hm hμ hN hp ha hγ.contDiffAt
      hrc.continuousAt (Filter.Eventually.of_forall hbr) hder hne
  · intro a u hu hule
    rw [← hreflect _ hsO a u hu,← hsame]
    rw [ho a (u/unitSquareScale a) ⟨div_nonneg hu (unitSquareScale_pos a).le,
      (div_le_one (unitSquareScale_pos a)).mpr hule⟩]
    exact div_lt_iff₀ (unitSquareScale_pos a)
  · intro a u hu hule
    rw [← hreflect _ hsC a u hu,← hsame]
    rw [hcl a (u/unitSquareScale a) ⟨div_nonneg hu (unitSquareScale_pos a).le,
      (div_le_one (unitSquareScale_pos a)).mpr hule⟩]
    exact div_le_iff₀ (unitSquareScale_pos a)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def permuteNormal (e : Fin 3 ≃ Fin 3) (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (torusCoordinatePermute e (quotientMap z.1)),
    ⟨coverCoordinatePermute e z.2,by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

lemma measurable_permuteNormal (e : Fin 3 ≃ Fin 3) : Measurable (permuteNormal e) := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp ((torusCoordinatePermute e).continuous.measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact ((coverCoordinatePermute e).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma permuteNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (e : Fin 3 ≃ Fin 3) (z : NormalBundle) :
    F (permuteNormal e z).1=F (coverCoordinatePermute e z.1) := by
  change F (representative (torusCoordinatePermute e (quotientMap z.1)))=_
  rw [← quotientMap_coordinatePermute]
  exact periodic_representative hp _

lemma permuteNormal_mass (μ : FiniteMeasure NormalBundle) (e : Fin 3 ≃ Fin 3) :
    ((μ.map (permuteNormal e)).mass : ℝ)=(μ.mass : ℝ) := by
  have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_permuteNormal e)
    MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
  simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
    FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh

lemma coverCoordinatePermute_inner (e : Fin 3 ≃ Fin 3) (x y : Cover) :
    ⟪coverCoordinatePermute e x,y⟫=⟪x,coverCoordinatePermute e.symm y⟫ := by
  rw [← (coverCoordinatePermute e).inner_map_map x (coverCoordinatePermute e.symm y),
    coverCoordinatePermute_inverse]

theorem isNormalMeasure_coordinatePermute {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (e : Fin 3 ≃ Fin 3) :
    IsNormalMeasure (torusCoordinatePermute e ⁻¹' E) (μ.map (permuteNormal e.symm)) := by
  constructor
  · rw [permuteNormal_mass,hμ.1,perimeter_coordinatePermute_measurable e hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (permuteNormal e.symm) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_permuteNormal e.symm).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_coordinatePermute e hF hE,← hμ.2 _ (coordinatePermutedField_admissible e.symm hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change ⟪coverCoordinatePermute e.symm z.2,F (permuteNormal e.symm z).1⟫=
        ⟪(z.2 : Cover),coverCoordinatePermute e (F (coverCoordinatePermute e.symm z.1))⟫
      rw [permuteNormal_periodic_eval hF.2.1,coverCoordinatePermute_inner,Equiv.symm_symm]

lemma permuted_normal_ae {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (e : Fin 3 ≃ Fin 3) :
    ∀ᵐ z ∂(μ.map (permuteNormal e.symm) : Measure NormalBundle),
      coordinatePermutedField e N z.1=(z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map (permuteNormal e.symm) (μ : Measure NormalBundle),_
  apply (ae_map_iff (measurable_permuteNormal e.symm).aemeasurable
    (measurableSet_eq_fun
      (((coverCoordinatePermute e.symm).continuous.comp (hN.comp (coverCoordinatePermute e).continuous)).measurable.comp
        (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [ha] with z hz
  change coordinatePermutedField e N (permuteNormal e.symm z).1=((permuteNormal e.symm z).2 : Cover)
  rw [permuteNormal_periodic_eval (coordinatePermutedField_periodic e hp)]
  change coverCoordinatePermute e.symm (N (coverCoordinatePermute e (coverCoordinatePermute e.symm z.1)))=_
  rw [coverCoordinatePermute_inverse,hz]
  rfl

lemma axialFluxWeight_permute (μ : FiniteMeasure NormalBundle) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    axialFluxWeight (μ.map (permuteNormal e)) i=axialFluxWeight μ (e i) := by
  unfold axialFluxWeight
  rw [permuteNormal_mass]
  congr 1
  change (∫ z,1-((z.2 : Cover) i)^2 ∂Measure.map (permuteNormal e) (μ : Measure NormalBundle))=_
  rw [integral_map (measurable_permuteNormal e).aemeasurable]
  · rfl
  · exact (continuous_const.sub (((EuclideanSpace.proj i).continuous.comp
      (continuous_subtype_val.comp continuous_snd)).pow 2)).aestronglyMeasurable

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma finitePerimeter_coordinatePermute {E : Set Torus} (hE : FinitePerimeter E)
    (e : Fin 3 ≃ Fin 3) : FinitePerimeter (torusCoordinatePermute e ⁻¹' E) := by
  refine ⟨hE.1.preimage (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving,?_⟩
  rw [perimeter_coordinatePermute e hE.1]
  exact hE.2

theorem isMinimizerAt_coordinatePermute {E : Set Torus} {V : ℝ}
    (hE : IsMinimizerAt V E) (e : Fin 3 ≃ Fin 3) :
    IsMinimizerAt V (torusCoordinatePermute e ⁻¹' E) := by
  refine ⟨finitePerimeter_coordinatePermute hE.1 e,?_,?_⟩
  · rw [volume_coordinatePermute e hE.1.1,hE.2.1]
  · intro F hF hvF
    rw [perimeter_coordinatePermute e hE.1.1]
    exact hE.2.2 F hF hvF

lemma volumeSupport_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    volumeSupport (torusCoordinatePermute e ⁻¹' E)=torusCoordinatePermute e ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (torusCoordinatePermute e ⁻¹' E)∩Metric.ball a r=
      torusCoordinatePermute e ⁻¹' (E∩Metric.ball (torusCoordinatePermute e a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,(torusCoordinatePermute e).isometry.dist_eq]
  rw [he,Measure.real_def,Measure.real_def,
    (torusCoordinatePermute_measurePreserving e).measure_preimage
      (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    openRepresentative (torusCoordinatePermute e ⁻¹' E)=torusCoordinatePermute e ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_coordinatePermute hE.compl]
  rfl

lemma frontier_openRepresentative_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    frontier (openRepresentative (torusCoordinatePermute e ⁻¹' E))=
      torusCoordinatePermute e ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_coordinatePermute hE e]
  exact (torusCoordinatePermute e).toHomeomorph.preimage_frontier _ |>.symm

lemma coordinateReflection_coordinatePermute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (z : Torus) :
    torusCoordinatePermute e (coordinateReflection i z)=
      coordinateReflection (e.symm i) (torusCoordinatePermute e z) := by
  ext j
  simp only [torusCoordinatePermute_apply,coordinateReflection_apply]
  simp only [show (j=e.symm i)↔e j=i from Equiv.eq_symm_apply e]

lemma reflection_invariant_coordinatePermute {E : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) (e : Fin 3 ≃ Fin 3) :
    ∀ i : Fin 3,coordinateReflection i ⁻¹' (torusCoordinatePermute e ⁻¹' E) =ᵐ[torusVolume]
      (torusCoordinatePermute e ⁻¹' E) := by
  intro i
  have hh := (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving.preimage_ae_eq (hs (e.symm i))
  have he : coordinateReflection i ⁻¹' (torusCoordinatePermute e ⁻¹' E)=
      torusCoordinatePermute e ⁻¹' (coordinateReflection (e.symm i) ⁻¹' E) := by
    ext z
    simp only [mem_preimage,coordinateReflection_coordinatePermute]
  rwa [he]

lemma coordinateHalf_coordinatePermute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (a : ℝ) (z : Torus) :
    torusCoordinatePermute e z∈coordinateHalf i a ↔ z∈coordinateHalf (e i) a := by
  rfl

lemma chamberVertex_coordinatePermute (e : Fin 3 ≃ Fin 3) (c b : Fin 3 → Bool) :
    coverCoordinatePermute e (chamberVertex (c ∘ e.symm) b)=chamberVertex c (b ∘ e) := by
  ext i
  simp [chamberVertex,chamberCorner]

lemma chamberSign_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) {N : Cover → Cover}
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (e : Fin 3 ≃ Fin 3) :
    ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative (torusCoordinatePermute e ⁻¹' E))∩
        coordinateHalf i (if (c ∘ e.symm) i then 0 else 1/2) →0<coordinatePermutedField e N x i := by
  intro x i hx
  apply hsg (coverCoordinatePermute e x) (e.symm i)
  constructor
  · rw [quotientMap_coordinatePermute]
    change quotientMap x∈torusCoordinatePermute e ⁻¹' frontier (openRepresentative E)
    rw [← frontier_openRepresentative_coordinatePermute hE e]
    exact hx.1
  · rw [quotientMap_coordinatePermute,coordinateHalf_coordinatePermute,Equiv.apply_symm_apply]
    exact hx.2

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

private lemma firstCornerPolynomial0_piece0 {d : ℝ}
    (hlo : (0 : ℝ) ≤ d) (hhi : d ≤ (1/4 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(0 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (6144/5 : ℝ)*(d-(0 : ℝ))^0*((1/4 : ℝ)-d)^6 +
        (321536/45 : ℝ)*(d-(0 : ℝ))^1*((1/4 : ℝ)-d)^5 +
        (153344/9 : ℝ)*(d-(0 : ℝ))^2*((1/4 : ℝ)-d)^4 +
        (191488/9 : ℝ)*(d-(0 : ℝ))^3*((1/4 : ℝ)-d)^3 +
        (131872/9 : ℝ)*(d-(0 : ℝ))^4*((1/4 : ℝ)-d)^2 +
        (237376/45 : ℝ)*(d-(0 : ℝ))^5*((1/4 : ℝ)-d)^1 +
        (34931/45 : ℝ)*(d-(0 : ℝ))^6*((1/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial0_piece1 {d : ℝ}
    (hlo : (1/4 : ℝ) ≤ d) (hhi : d ≤ (1/2 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(1/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/2 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (34931/45 : ℝ)*(d-(1/4 : ℝ))^0*((1/2 : ℝ)-d)^6 +
        (181796/45 : ℝ)*(d-(1/4 : ℝ))^1*((1/2 : ℝ)-d)^5 +
        (76292/9 : ℝ)*(d-(1/4 : ℝ))^2*((1/2 : ℝ)-d)^4 +
        (27424/3 : ℝ)*(d-(1/4 : ℝ))^3*((1/2 : ℝ)-d)^3 +
        (48016/9 : ℝ)*(d-(1/4 : ℝ))^4*((1/2 : ℝ)-d)^2 +
        (72256/45 : ℝ)*(d-(1/4 : ℝ))^5*((1/2 : ℝ)-d)^1 +
        (8896/45 : ℝ)*(d-(1/4 : ℝ))^6*((1/2 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial0_piece2 {d : ℝ}
    (hlo : (1/2 : ℝ) ≤ d) (hhi : d ≤ (3/4 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(1/2 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (3/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (8896/45 : ℝ)*(d-(1/2 : ℝ))^0*((3/4 : ℝ)-d)^6 +
        (34496/45 : ℝ)*(d-(1/2 : ℝ))^1*((3/4 : ℝ)-d)^5 +
        (10256/9 : ℝ)*(d-(1/2 : ℝ))^2*((3/4 : ℝ)-d)^4 +
        (8480/9 : ℝ)*(d-(1/2 : ℝ))^3*((3/4 : ℝ)-d)^3 +
        (5956/9 : ℝ)*(d-(1/2 : ℝ))^4*((3/4 : ℝ)-d)^2 +
        (17836/45 : ℝ)*(d-(1/2 : ℝ))^5*((3/4 : ℝ)-d)^1 +
        (1577/15 : ℝ)*(d-(1/2 : ℝ))^6*((3/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial0_piece3 {d : ℝ}
    (hlo : (3/4 : ℝ) ≤ d) (hhi : d ≤ (1 : ℝ)) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  have hl : 0 ≤ d-(3/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1 : ℝ)-d := sub_nonneg.mpr hhi
  have he : (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 =
      (1577/15 : ℝ)*(d-(3/4 : ℝ))^0*((1 : ℝ)-d)^6 +
        (38936/45 : ℝ)*(d-(3/4 : ℝ))^1*((1 : ℝ)-d)^5 +
        (27056/9 : ℝ)*(d-(3/4 : ℝ))^2*((1 : ℝ)-d)^4 +
        (47872/9 : ℝ)*(d-(3/4 : ℝ))^3*((1 : ℝ)-d)^3 +
        (44032/9 : ℝ)*(d-(3/4 : ℝ))^4*((1 : ℝ)-d)^2 +
        (96256/45 : ℝ)*(d-(3/4 : ℝ))^5*((1 : ℝ)-d)^1 +
        (14336/45 : ℝ)*(d-(3/4 : ℝ))^6*((1 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

lemma firstCornerPolynomial0_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ (3/10 : ℝ)-(2/9)*d-d^2*(1-d^2)^2 := by
  by_cases h1 : d ≤ 1/4
  · exact firstCornerPolynomial0_piece0 hd0 h1
  by_cases h2 : d ≤ 1/2
  · exact firstCornerPolynomial0_piece1 (by linarith) h2
  by_cases h3 : d ≤ 3/4
  · exact firstCornerPolynomial0_piece2 (by linarith) h3
  exact firstCornerPolynomial0_piece3 (by linarith) hd1

private lemma firstCornerPolynomial1_piece0 {d : ℝ}
    (hlo : (0 : ℝ) ≤ d) (hhi : d ≤ (1/4 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(0 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (21364736/405 : ℝ)*(d-(0 : ℝ))^0*((1/4 : ℝ)-d)^8 +
        (159121408/405 : ℝ)*(d-(0 : ℝ))^1*((1/4 : ℝ)-d)^7 +
        (513953792/405 : ℝ)*(d-(0 : ℝ))^2*((1/4 : ℝ)-d)^6 +
        (187977728/81 : ℝ)*(d-(0 : ℝ))^3*((1/4 : ℝ)-d)^5 +
        (1063959424/405 : ℝ)*(d-(0 : ℝ))^4*((1/4 : ℝ)-d)^4 +
        (254383744/135 : ℝ)*(d-(0 : ℝ))^5*((1/4 : ℝ)-d)^3 +
        (338610992/405 : ℝ)*(d-(0 : ℝ))^6*((1/4 : ℝ)-d)^2 +
        (28318096/135 : ℝ)*(d-(0 : ℝ))^7*((1/4 : ℝ)-d)^1 +
        (1025176/45 : ℝ)*(d-(0 : ℝ))^8*((1/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial1_piece1 {d : ℝ}
    (hlo : (1/4 : ℝ) ≤ d) (hhi : d ≤ (1/2 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(1/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1/2 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (1025176/45 : ℝ)*(d-(1/4 : ℝ))^0*((1/2 : ℝ)-d)^8 +
        (20890352/135 : ℝ)*(d-(1/4 : ℝ))^1*((1/2 : ℝ)-d)^7 +
        (182628368/405 : ℝ)*(d-(1/4 : ℝ))^2*((1/2 : ℝ)-d)^6 +
        (99176704/135 : ℝ)*(d-(1/4 : ℝ))^3*((1/2 : ℝ)-d)^5 +
        (295680064/405 : ℝ)*(d-(1/4 : ℝ))^4*((1/2 : ℝ)-d)^4 +
        (1356544/3 : ℝ)*(d-(1/4 : ℝ))^5*((1/2 : ℝ)-d)^3 +
        (13788928/81 : ℝ)*(d-(1/4 : ℝ))^6*((1/2 : ℝ)-d)^2 +
        (4814848/135 : ℝ)*(d-(1/4 : ℝ))^7*((1/2 : ℝ)-d)^1 +
        (48128/15 : ℝ)*(d-(1/4 : ℝ))^8*((1/2 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial1_piece2 {d : ℝ}
    (hlo : (1/2 : ℝ) ≤ d) (hhi : d ≤ (3/4 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(1/2 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (3/4 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (48128/15 : ℝ)*(d-(1/2 : ℝ))^0*((3/4 : ℝ)-d)^8 +
        (2115584/135 : ℝ)*(d-(1/2 : ℝ))^1*((3/4 : ℝ)-d)^7 +
        (12260096/405 : ℝ)*(d-(1/2 : ℝ))^2*((3/4 : ℝ)-d)^6 +
        (4338944/135 : ℝ)*(d-(1/2 : ℝ))^3*((3/4 : ℝ)-d)^5 +
        (11942464/405 : ℝ)*(d-(1/2 : ℝ))^4*((3/4 : ℝ)-d)^4 +
        (13395712/405 : ℝ)*(d-(1/2 : ℝ))^5*((3/4 : ℝ)-d)^3 +
        (11699216/405 : ℝ)*(d-(1/2 : ℝ))^6*((3/4 : ℝ)-d)^2 +
        (5426032/405 : ℝ)*(d-(1/2 : ℝ))^7*((3/4 : ℝ)-d)^1 +
        (984056/405 : ℝ)*(d-(1/2 : ℝ))^8*((3/4 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

private lemma firstCornerPolynomial1_piece3 {d : ℝ}
    (hlo : (3/4 : ℝ) ≤ d) (hhi : d ≤ (1 : ℝ)) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  have hl : 0 ≤ d-(3/4 : ℝ) := sub_nonneg.mpr hlo
  have hh : 0 ≤ (1 : ℝ)-d := sub_nonneg.mpr hhi
  have he : ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 =
      (984056/405 : ℝ)*(d-(3/4 : ℝ))^0*((1 : ℝ)-d)^8 +
        (10318864/405 : ℝ)*(d-(3/4 : ℝ))^1*((1 : ℝ)-d)^7 +
        (9189808/81 : ℝ)*(d-(3/4 : ℝ))^2*((1 : ℝ)-d)^6 +
        (22413056/81 : ℝ)*(d-(3/4 : ℝ))^3*((1 : ℝ)-d)^5 +
        (162792064/405 : ℝ)*(d-(3/4 : ℝ))^4*((1 : ℝ)-d)^4 +
        (15935488/45 : ℝ)*(d-(3/4 : ℝ))^5*((1 : ℝ)-d)^3 +
        (74067968/405 : ℝ)*(d-(3/4 : ℝ))^6*((1 : ℝ)-d)^2 +
        (2228224/45 : ℝ)*(d-(3/4 : ℝ))^7*((1 : ℝ)-d)^1 +
        (229376/45 : ℝ)*(d-(3/4 : ℝ))^8*((1 : ℝ)-d)^0 := by ring
  rw [he]
  positivity

lemma firstCornerPolynomial1_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ ((3/10 : ℝ)-(2/9)*d-(4/81)*(1-d^2)^2)*(1+(1-d^2))^2-
      (1-d^2)^2*((2/9)*(1+(1-d^2))+d)^2 := by
  by_cases h1 : d ≤ 1/4
  · exact firstCornerPolynomial1_piece0 hd0 h1
  by_cases h2 : d ≤ 1/2
  · exact firstCornerPolynomial1_piece1 (by linarith) h2
  by_cases h3 : d ≤ 3/4
  · exact firstCornerPolynomial1_piece2 (by linarith) h3
  exact firstCornerPolynomial1_piece3 (by linarith) hd1

end CubicTorus

end
end

end OAI
