import Mathlib
import OAI.Geometry.BallPacking.SurfaceArea.SurfacePrimitiveOperator

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def spatialCutoffDefect (κ : M → ℝ) (α : ManifoldOneForm Plane M) : ManifoldTwoForm Plane M :=
  manifoldExteriorOneForm (fun x => κ x • α x)-(fun x => κ x • manifoldExteriorOneForm α x)

theorem spatialCutoffDefect_smooth {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hα : SmoothOneFormFamily (fun _ : ℝ => α)) :
    SmoothTwoForm (spatialCutoffDefect κ α) :=
  ((manifoldExteriorOneForm_family_smooth (hα.spatial_smul hκ)).sub
    ((manifoldExteriorOneForm_family_smooth hα).spatial_smul hκ)).eval 0

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem spatialCutoffDefect_skew (κ : M → ℝ) (α : ManifoldOneForm Plane M)
    (x : M) (u v : Plane) : spatialCutoffDefect κ α x u v= -spatialCutoffDefect κ α x v u := by
  change manifoldExteriorOneForm (fun x => κ x • α x) x u v-
    κ x*manifoldExteriorOneForm α x u v= -(manifoldExteriorOneForm (fun x => κ x • α x) x v u-
    κ x*manifoldExteriorOneForm α x v u)
  rw [manifoldExteriorOneForm_skew (fun x => κ x • α x) x u v,
    manifoldExteriorOneForm_skew α x u v]
  ring

theorem spatialCutoffDefect_zero_of_locally_constant {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hα : SmoothOneFormFamily (fun _ : ℝ => α)) {x : M} {c : ℝ}
    (he : κ=ᶠ[𝓝 x] fun _ => c) : spatialCutoffDefect κ α x=0 := by
  have hform : (fun y => κ y • α y)=ᶠ[𝓝 x] c • α := by
    filter_upwards [he] with y hy
    change κ y • α y=c • α y
    rw [hy]
  have hc : κ x=c := he.eq_of_nhds
  unfold spatialCutoffDefect
  rw [Pi.sub_apply,manifoldExteriorOneForm_congr_of_eventuallyEq hform,
    manifoldExteriorOneForm_smul c (fun b y hy => (hα.spatial_smooth 0 b hy).contDiffWithinAt),hc]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change c*manifoldExteriorOneForm α x u v-c*manifoldExteriorOneForm α x u v=0
  ring

theorem spatialCutoffDefect_coefficient
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {y : Plane} (hy : y∈e.source) :
    partialChartCoefficient e (spatialCutoffDefect κ α) y=
      planarCurl (fun z => κ (e z) • euclideanPullbackOneForm (fun _ => α) e (0,z)) y-
        κ (e y)*planarCurl (fun z => euclideanPullbackOneForm (fun _ => α) e (0,z)) y := by
  unfold spatialCutoffDefect
  rw [partialChartCoefficient_sub,
    partialChartCoefficient_exterior e (hα.spatial_smul hκ) hy]
  have he : (fun z => euclideanPullbackOneForm (fun _ => fun x => κ x • α x) e (0,z))=
      (fun z => κ (e z) • euclideanPullbackOneForm (fun _ => α) e (0,z)) :=
    funext (euclideanPullbackOneForm_spatial_smul κ α e)
  rw [he]
  congr 1
  change κ (e y)*partialChartCoefficient e (manifoldExteriorOneForm α) y=_
  rw [partialChartCoefficient_exterior e hα hy]

end

theorem cutoffWedge_radial_angular {g : ℝ → ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (hz : radiusSq z≠0) :
    cutoffWedge (fun y => g (radiusSq y)) angularOneForm z=2*deriv g (radiusSq z) := by
  have hd := (hg.hasDerivAt.comp_hasFDerivAt z (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  unfold cutoffWedge
  rw [hd]
  simp only [smul_apply,smul_eq_mul,planarDot_apply,angularOneForm,
    planarArea_apply]
  unfold radiusSq at hz ⊢
  field_simp
  ring

theorem planar_residue_defect {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (hβ : DifferentiableAt ℝ β z)
    (hz : radiusSq z≠0) (c : ℝ) :
    planarCurl (fun y => (1-g (radiusSq y)) • (β y-(c/2) • angularOneForm y)) z-
      (1-g (radiusSq z))*planarCurl (fun y => β y-(c/2) • angularOneForm y) z=
      -cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z) := by
  have hgs := hg.comp z (radiusSq_hasFDerivAt z).differentiableAt
  have hrs := (differentiableAt_const (c := (1:ℝ))).sub hgs
  have hbs := hβ.sub ((angularOneForm_contDiffAt hz).differentiableAt (by simp) |>.const_smul (c/2))
  change DifferentiableAt ℝ (fun y => 1-g (radiusSq y)) z at hrs
  change DifferentiableAt ℝ (fun y => β y-(c/2) • angularOneForm y) z at hbs
  change DifferentiableAt ℝ (fun y => g (radiusSq y)) z at hgs
  rw [planarCurl_spatial_smul hrs hbs,add_sub_cancel_right]
  have hd := (hasFDerivAt_const (1:ℝ) z).sub hgs.hasFDerivAt
  change HasFDerivAt (fun y => 1-g (radiusSq y)) _ z at hd
  have he : cutoffWedge (fun y => 1-g (radiusSq y)) (fun y => β y-(c/2) • angularOneForm y) z=
      -cutoffWedge (fun y => g (radiusSq y)) β z+(c/2)*cutoffWedge (fun y => g (radiusSq y)) angularOneForm z := by
    unfold cutoffWedge
    rw [hd.fderiv]
    simp only [sub_apply,zero_apply,smul_apply,smul_eq_mul]
    ring
  rw [he,cutoffWedge_radial_angular hg hz]
  ring

theorem planarCurl_congr_of_eventuallyEq {α β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (he : α=ᶠ[𝓝 z] β) : planarCurl α z=planarCurl β z := by
  unfold planarCurl
  rw [he.fderiv_eq]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveCutoffDefect_zero_off_annuli {g : ℝ → ℝ} {r R : ℝ}
    (hc : HasCompactSupport g) (hr : 0<r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ)
    {x : locus a} (hx : x∉⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R) :
    spatialCutoffDefect (curveEndCutoff a g) (curveFSPrimitive a c) x=0 := by
  obtain ⟨b,hb⟩ := curveEndCutoff_locally_constant_off_annuli a hc hr hR h1 h0 hx
  exact spatialCutoffDefect_zero_of_locally_constant (curveFSPrimitive_smooth a c) hb

theorem curveCutoffDefect_end_coefficient {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ε : Fin m → Bool) (c : ℝ)
    {β : Plane → Plane →L[ℝ] ℝ} {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source)
    (he : β=ᶠ[𝓝 y] infinityRegularPrimitive a ε c) :
    partialChartCoefficient (infinityDiffeomorph a ε)
      (spatialCutoffDefect (curveEndCutoff a g) (curveFSPrimitive a c)) y=
      -cutoffWedge (fun z => g (radiusSq z)) β y+c*deriv g (radiusSq y) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hz : radiusSq y≠0 := by
    rw [← radiusSq_complex]
    exact ne_of_gt (Complex.normSq_pos.mpr hD.1)
  have hβ : DifferentiableAt ℝ β y :=
    ((infinityRegularPrimitive_contDiffAt a ε c hD.2).congr_of_eventuallyEq he).differentiableAt (by simp)
  have hα : (fun z => euclideanPullbackOneForm (fun _ => curveFSPrimitive a c)
      (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y] fun z => β z-(c/2) • angularOneForm z := by
    filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy,he] with z hz hez
    rw [curveFSPrimitive_infinity a ε c hz,hez]
  have hκα : (fun z => curveEndCutoff a g (infinityDiffeomorph a ε z) •
      euclideanPullbackOneForm (fun _ => curveFSPrimitive a c) (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y]
        fun z => (1-g (radiusSq z)) • (β z-(c/2) • angularOneForm z) := by
    filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy,hα] with z hz haz
    rw [curveEndCutoff_infinity a g ε hz,haz]
  rw [spatialCutoffDefect_coefficient _ (curveEndCutoff_smooth a hg hc)
    (curveFSPrimitive_smooth a c) hy,planarCurl_congr_of_eventuallyEq hκα,
    planarCurl_congr_of_eventuallyEq hα,curveEndCutoff_infinity a g ε hy]
  exact planar_residue_defect (hg.differentiable (by simp) _) hβ hz c

end

variable {m : ℕ} (a : Fin m → ℂ)

theorem exists_infinityRegularPrimitive_extension {R : ℝ}
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) (c : ℝ) :
    ∃ β : Plane → Plane →L[ℝ] ℝ,ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      β=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c := by
  let U : Set Plane := Complex.equivRealProdCLM.symm ⁻¹' infinityRegion a
  have hU : IsOpen U := (infinityRegion_open a).preimage Complex.equivRealProdCLM.symm.continuous
  have hKU : radialAnnulus 0 R⊆U := by
    intro y hy
    apply hR
    change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
    rw [radiusSq_complex]
    exact hy.2
  have hf : ContDiffOn ℝ ∞ (infinityRegularPrimitive a ε c) U :=
    fun y hy => (infinityRegularPrimitive_contDiffAt a ε c hy).contDiffWithinAt
  obtain ⟨χ,_hχ,_hχc,_hχU,_hr,_h1,hf,hc,he⟩ :=
    exists_smooth_compact_extension (radialAnnulus_compact 0 R) hU hKU hf
  exact ⟨fun y => χ y • infinityRegularPrimitive a ε c y,hf,hc,he⟩

theorem regular_extension_germ {R : ℝ} {ε : Fin m → Bool} {c : ℝ}
    {β : Plane → Plane →L[ℝ] ℝ}
    (he : β=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c)
    {z : Plane} (hz : radiusSq z≤R) : β=ᶠ[𝓝 z] infinityRegularPrimitive a ε c :=
  he.filter_mono (nhds_le_nhdsSet ⟨radiusSq_nonneg z,hz⟩)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Filter
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partitionFormMass_eq_partialChart_supported_integral
    {I : Type*} [Fintype I] {K S : Set M}
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (hpos : PositivePartialChart e) (hS : IsCompact S) (hSK : S⊆K) (hSe : S⊆e.target)
    (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉S→Ω x=0) :
    partitionFormMass B ρ Ω=∫ y in e.symm '' S,partialChartCoefficient e Ω y := by
  classical
  let D : I → ManifoldTwoForm Plane M := fun i x => ρ i x • Ω x
  let L : I → Set M := fun i => S∩tsupport (ρ i)
  have hL (i : I) : IsCompact (L i) := hS.inter_right (isClosed_tsupport (ρ i))
  have hLB (i : I) : L i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hLe (i : I) : L i⊆e.target := fun _ hx => hSe hx.1
  have hDs (i : I) : SmoothTwoForm (D i) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0
  have hDa (i : I) (x : M) (u v : Plane) : D i x u v= -D i x v u := by
    change ρ i x * Ω x u v= -(ρ i x * Ω x v u)
    rw [ha x u v,mul_neg]
  have hDz (i : I) (x : M) (hx : x∉L i) : D i x=0 := by
    by_cases hk : x∈S
    · have hi : x∉tsupport (ρ i) := fun hi => hx ⟨hk,hi⟩
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change ρ i x * Ω x u v=0
      rw [image_eq_zero_of_notMem_tsupport hi,zero_mul]
    · apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change ρ i x * Ω x u v=0
      rw [hz x hk]
      simp
  have hCS : IsCompact (e.symm '' S) :=
    hS.image_of_continuousOn (e.symm.contMDiffOn.continuousOn.mono hSe)
  have hse : e.symm '' S⊆e.source := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_target (hSe hx)
  have hI (i : I) : IntegrableOn (partialChartCoefficient e (D i)) (e.symm '' S) :=
    ((partialChartCoefficient_contDiffOn e (hDs i)).continuousOn.mono hse).integrableOn_compact hCS
  have hmass (i : I) : chartMass (B i).center (D i)=
      ∫ y in e.symm '' S,partialChartCoefficient e (D i) y := by
    rw [chartMass_eq_partialChart_integral e (hDa i) (hL i) (hLe i) (hLB i) (hDz i)
      (by
        rintro y ⟨x,hx,rfl⟩
        apply hpos (B i).center _ (e.map_target (hLe i hx))
        have heq : e (e.symm x)=x := e.right_inv (hLe i hx)
        exact heq.symm ▸ hLB i hx)]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hCS.measurableSet
      (image_mono inter_subset_left)
    intro y hy
    have hyn : e y∉L i := by
      intro hyl
      exact hy.2 ⟨e y,hyl,e.left_inv (hse hy.1)⟩
    simp only [partialChartCoefficient,euclideanPullbackTwoForm,hDz i (e y) hyn]
    rfl
  change (∑ i,chartMass (B i).center (D i))=_
  simp_rw [hmass]
  rw [← integral_finsetSum Finset.univ (fun i _ => hI i)]
  apply setIntegral_congr_fun hCS.measurableSet
  intro y hy
  have hey : e y∈S := by
    obtain ⟨x,hx,rfl⟩ := hy
    have heq : e (e.symm x)=x := e.right_inv (hSe hx)
    rwa [heq]
  have hs : (∑ i,ρ i (e y))=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (hSK hey)
  simp only [D,partialChartCoefficient_smul,← Finset.sum_mul,hs,one_mul]

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem SmoothTwoForm.indicator {U K : Set M} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K⊆U) {Ω : ManifoldTwoForm E M} (hΩ : SmoothTwoForm Ω)
    (hz : ∀ x,x∈U→x∉K→Ω x=0) : SmoothTwoForm (U.indicator Ω) := by
  classical
  intro c y hy
  let e := extChartAt 𝓘(ℝ,E) c
  let x := e.symm y
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hy)).continuousAt
  by_cases hx : x∈U
  · have hn := hi.preimage_mem_nhds (hU.mem_nhds hx)
    have he : chartTwoForm (U.indicator Ω) c=ᶠ[𝓝 y] chartTwoForm Ω c := by
      filter_upwards [hn] with z hz
      change ((U.indicator Ω) (e.symm z)).bilinearComp _ _=_
      rw [indicator_of_mem (show e.symm z∈U from hz)]
      rfl
    exact (((hΩ c).contDiffAt ((isOpen_extChartAt_target c).mem_nhds hy)).congr_of_eventuallyEq he).contDiffWithinAt
  · have hxK : x∉K := fun hk => hx (hKU hk)
    have hn := hi.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hxK)
    have he : chartTwoForm (U.indicator Ω) c=ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hn] with z hzk
      have hz0 : U.indicator Ω (e.symm z)=0 := by
        by_cases hzu : e.symm z∈U
        · rw [indicator_of_mem hzu,hz _ hzu hzk]
        · exact indicator_of_notMem hzu _
      change ((U.indicator Ω) (e.symm z)).bilinearComp _ _=0
      rw [hz0]
      ext u v
      rfl
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

 omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem indicator_twoForm_skew (U : Set M) {Ω : ManifoldTwoForm E M}
    (ha : ∀ x u v,Ω x u v= -Ω x v u) :
    ∀ x u v,(U.indicator Ω) x u v= -(U.indicator Ω) x v u := by
  classical
  intro x u v
  by_cases hx : x∈U
  · simpa only [indicator_of_mem hx] using ha x u v
  · simp only [indicator_of_notMem hx,zero_apply,neg_zero]

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

theorem partitionFormMass_finite_disjoint_charts
    {I J : Type*} [Fintype I] [Fintype J] {K : Set M} (hK : IsCompact K)
    (e : J → PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (hpos : ∀ j,PositivePartialChart (e j))
    (hdisj : Pairwise fun i j => Disjoint (e i).target (e j).target)
    (S : J → Set M) (hS : ∀ j,IsCompact (S j))
    (hSK : ∀ j,S j⊆K) (hSe : ∀ j,S j⊆(e j).target)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉⋃ j,S j→Ω x=0) :
    partitionFormMass B ρ Ω=∑ j,∫ y in (e j).symm '' S j,partialChartCoefficient (e j) Ω y := by
  classical
  have hzero (j : J) (x : M) (hx : x∈(e j).target) (hs : x∉S j) : Ω x=0 := by
    apply hz
    intro hall
    obtain ⟨i,hi⟩ := mem_iUnion.mp hall
    by_cases hij : i=j
    · exact hs (hij ▸ hi)
    · exact Set.disjoint_left.mp (hdisj hij) (hSe i hi) hx
  let D : J → smoothSupportedTwoForms (E := Plane) K := fun j =>
    ⟨(e j).target.indicator Ω,
      hΩ.indicator (e j).open_target (hS j).isClosed (hSe j) (hzero j),
      indicator_twoForm_skew _ ha,by
        intro x hx
        by_cases he : x∈(e j).target
        · rw [indicator_of_mem he]
          exact hzero j x he (fun hs => hx (hSK j hs))
        · exact indicator_of_notMem he _⟩
  have hDz (j : J) (x : M) (hx : x∉S j) : (D j : ManifoldTwoForm Plane M) x=0 := by
    change (e j).target.indicator Ω x=0
    by_cases he : x∈(e j).target
    · rw [indicator_of_mem he,hzero j x he hx]
    · exact indicator_of_notMem he _
  have hsum : ((∑ j,D j : smoothSupportedTwoForms (E := Plane) K) : ManifoldTwoForm Plane M)=Ω := by
    funext x
    simp only [Submodule.coe_sum,Finset.sum_apply]
    by_cases hex : ∃ j,x∈(e j).target
    · obtain ⟨j,hj⟩ := hex
      rw [Finset.sum_eq_single j]
      · exact indicator_of_mem hj _
      · intro i _ hij
        change (e i).target.indicator Ω x=0
        exact indicator_of_notMem (fun hi => Set.disjoint_left.mp (hdisj hij) hi hj) _
      · simp
    · have hx : ∀ j,x∉(e j).target := not_exists.mp hex
      have ho : Ω x=0 := hz x (by
        intro hall
        obtain ⟨j,hj⟩ := mem_iUnion.mp hall
        exact hx j (hSe j hj))
      rw [ho]
      apply Finset.sum_eq_zero
      intro j _
      exact indicator_of_notMem (hx j) _
  conv_lhs => rw [← hsum]
  change surfaceIntegralLinearMap hK B ρ hρ (∑ j,D j)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change partitionFormMass B ρ (D j : ManifoldTwoForm Plane M)=_
  rw [partitionFormMass_eq_partialChart_supported_integral (e j) (hpos j) (hS j)
    (hSK j) (hSe j) B ρ hρ (smoothSupportedTwoForms.smooth (D j))
    (smoothSupportedTwoForms.skew (D j)) (hDz j)]
  apply setIntegral_congr_fun ((hS j).image_of_continuousOn
    ((e j).symm.contMDiffOn.continuousOn.mono (hSe j))).measurableSet
  rintro y ⟨x,hx,rfl⟩
  have ht : e j ((e j).symm x)∈(e j).target :=
    (e j).map_source ((e j).map_target (hSe j hx))
  simp only [partialChartCoefficient,euclideanPullbackTwoForm,D,indicator_of_mem ht]

theorem partitionFormMass_cutoff_defect {I : Type*} [Fintype I] {K : Set M}
    (hor : PositivePlaneTransitions M) (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {κ : M → ℝ} {α : ManifoldOneForm Plane M}
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hz : ∀ x,x∉K→κ x=0) :
    partitionFormMass B ρ (fun x => κ x • manifoldExteriorOneForm α x)=
      -partitionFormMass B ρ (spatialCutoffDefect κ α) := by
  have hκα : SmoothOneFormFamily (fun _ : ℝ => fun x => κ x • α x) := hα.spatial_smul hκ
  have hβ : SmoothTwoForm (fun x => κ x • manifoldExteriorOneForm α x) :=
    ((manifoldExteriorOneForm_family_smooth hα).spatial_smul hκ).eval 0
  have hzβ : ∀ x,x∉K→(fun x => κ x • manifoldExteriorOneForm α x) x=0 := by
    intro x hx
    change κ x • manifoldExteriorOneForm α x=0
    rw [hz x hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ)*manifoldExteriorOneForm α x u v=0
    exact zero_mul _
  have hzδ : ∀ x,x∉K→spatialCutoffDefect κ α x=0 := by
    intro x hx
    apply spatialCutoffDefect_zero_of_locally_constant hα
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hz y hy
  have he : spatialCutoffDefect κ α+(fun x => κ x • manifoldExteriorOneForm α x)=
      manifoldExteriorOneForm (fun x => κ x • α x) := by
    unfold spatialCutoffDefect
    exact sub_add_cancel (manifoldExteriorOneForm (fun x => κ x • α x))
      (fun x => κ x • manifoldExteriorOneForm α x)
  have hm := partitionFormMass_compact_stokes hor hK B ρ hρ hκα (by
    intro x hx
    rw [hz x hx,zero_smul])
  rw [←he,partitionFormMass_add hK B ρ hρ (spatialCutoffDefect_smooth hκ hα) hβ hzδ hzβ] at hm
  exact eq_neg_of_add_eq_zero_right hm

end

theorem radialCutoff_deriv_zero_off_annulus {g : ℝ → ℝ} {r R : ℝ}
    (hr : 0<r) (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {z : Plane} (hz : z∉radialAnnulus r R) : deriv g (radiusSq z)=0 := by
  change ¬(r≤radiusSq z ∧ radiusSq z≤R) at hz
  rcases not_and_or.mp hz with hl|hh
  · have he : g=ᶠ[𝓝 (radiusSq z)] fun _ => 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show radiusSq z∈Ioo (-r) r from ⟨lt_of_lt_of_le (neg_neg_of_pos hr) (radiusSq_nonneg z),lt_of_not_ge hl⟩)] with t ht
      exact h1 t ht
    rw [he.deriv_eq,deriv_const]
  · have he : g=ᶠ[𝓝 (radiusSq z)] fun _ => 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds (show R<radiusSq z from lt_of_not_ge hh)] with t ht
      exact image_eq_zero_of_notMem_tsupport (fun hs => not_le_of_gt (show R<t from ht) (show t≤R from h0 hs))
    rw [he.deriv_eq,deriv_const]

theorem planarResidueDensity_zero_off {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (β : Plane → Plane →L[ℝ] ℝ) (c : ℝ) {z : Plane} (hz : z∉radialAnnulus r R) :
    -cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z)=0 := by
  have hd := ((hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  rw [radialCutoff_deriv_zero_off_annulus hr h1 h0 hz,zero_smul] at hd
  simp only [cutoffWedge,hd,zero_apply,zero_mul,sub_zero,neg_zero,
    radialCutoff_deriv_zero_off_annulus hr h1 h0 hz,mul_zero,add_zero]

theorem integral_planar_residue_annulus {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (c : ℝ) :
    (∫ z in radialAnnulus r R,-cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z))=
      (∫ z : Plane,g (radiusSq z)*planarCurl β z)-c*Real.pi := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => planarResidueDensity_zero_off hg hr h1 h0 β c hz)]
  exact integral_planar_residue_cutoff hg hc (h1 0 ⟨neg_neg_of_pos hr,hr⟩) hβ c

end PackingSufficiencySupport.Hamiltonian
end

end OAI
