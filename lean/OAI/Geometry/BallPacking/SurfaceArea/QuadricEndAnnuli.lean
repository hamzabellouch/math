import Mathlib
import OAI.Geometry.BallPacking.Toric.CubicRadialFamilyExtension

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

def curveEndAnnulus (ε : Fin m → Bool) (r R : ℝ) : Set (locus a) :=
  infinityDiffeomorph a ε '' radialAnnulus r R

theorem radialAnnulus_in_end {r R : ℝ} (hr : 0<r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    radialAnnulus r R⊆(infinityDiffeomorph a ε).source := by
  intro y hy
  rw [infinityDiffeomorph_source]
  refine ⟨?_,hR (by change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R; rw [radiusSq_complex];exact hy.2)⟩
  intro he
  have hey : y=0 := by
    apply Complex.equivRealProdCLM.symm.injective
    simpa only [map_zero] using he
  exact radialAnnulus_ne_zero hr hy hey

theorem curveEndAnnulus_compact {r R : ℝ} (hr : 0<r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    IsCompact (curveEndAnnulus a ε r R) :=
  (radialAnnulus_compact r R).image_of_continuousOn
    ((infinityDiffeomorph a ε).contMDiffOn.continuousOn.mono (radialAnnulus_in_end a hr hR ε))

theorem curveEndAnnulus_subset_target {r R : ℝ} (hr : 0<r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    curveEndAnnulus a ε r R⊆(infinityDiffeomorph a ε).target := by
  rintro x ⟨y,hy,rfl⟩
  exact (infinityDiffeomorph a ε).map_source (radialAnnulus_in_end a hr hR ε hy)

theorem endAnnulus_cover {r R : ℝ} (_hr : 0<r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) {x : locus a}
    (hx : curveProjection a x≠0)
    (hb : Complex.normSq (curveProjection a x)⁻¹∈Icc r R) :
    x∈⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R := by
  obtain ⟨ε,hε⟩ := exists_infinityBranch a hx (hR hb.2)
  apply mem_iUnion.mpr
  refine ⟨ε,(infinityDiffeomorph a ε).symm x,?_,?_⟩
  · change r≤radiusSq (Complex.equivRealProdCLM (curveProjection a x)⁻¹) ∧
      radiusSq (Complex.equivRealProdCLM (curveProjection a x)⁻¹)≤R
    rw [← radiusSq_complex,ContinuousLinearEquiv.symm_apply_apply]
    exact hb
  · exact (infinityDiffeomorph a ε).right_inv (by simpa only [infinityDiffeomorph_target] using hε)

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_punctured_germ (g : ℝ → ℝ) {x : locus a}
    (hx : curveProjection a x≠0) :
    curveEndCutoff a g=ᶠ[𝓝 x] fun y => 1-g (Complex.normSq (curveProjection a y)⁻¹) := by
  have hn : ∀ᶠ y in 𝓝 x,curveProjection a y≠0 :=
    (isOpen_ne_fun (curveProjection_continuous a) continuous_const).mem_nhds hx
  filter_upwards [hn] with y hy
  exact ite_eq_right hy

theorem curveEndCutoff_locally_constant_off_annuli {g : ℝ → ℝ} {r R : ℝ}
    (hc : HasCompactSupport g) (hr : 0<r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {x : locus a} (hx : x∉⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R) :
    ∃ c : ℝ,curveEndCutoff a g=ᶠ[𝓝 x] fun _ => c := by
  by_cases ht : curveProjection a x=0
  · refine ⟨1,?_⟩
    have hi := inverseComplementCutoff_one_near_zero (HasCompactSupport.comp_complex_normSq hc)
    have hp : Tendsto (curveProjection a) (𝓝 x) (𝓝 0) := by
      have hp := (curveProjection_continuous a).continuousAt (x := x)
      change Tendsto (curveProjection a) (𝓝 x) (𝓝 (curveProjection a x)) at hp
      rwa [ht] at hp
    exact hi.comp_tendsto hp
  · have hinv : ContinuousAt (fun y => Complex.normSq (curveProjection a y)⁻¹) x :=
      complex_normSq_smooth.continuous.continuousAt.comp
        ((curveProjection_continuous a).continuousAt.inv₀ ht)
    have hnot : Complex.normSq (curveProjection a x)⁻¹∉Icc r R :=
      fun hb => hx (endAnnulus_cover a hr hR ht hb)
    rcases not_and_or.mp hnot with hlow|hhigh
    · have hl : Complex.normSq (curveProjection a x)⁻¹∈Ioo (-r) r :=
        ⟨lt_of_lt_of_le (neg_neg_of_pos hr) (Complex.normSq_nonneg _),lt_of_not_ge hlow⟩
      have he : ∀ᶠ y in 𝓝 x,Complex.normSq (curveProjection a y)⁻¹∈Ioo (-r) r :=
        hinv (isOpen_Ioo.mem_nhds hl)
      refine ⟨0,?_⟩
      filter_upwards [curveEndCutoff_punctured_germ a g ht,he] with y hy he
      rw [hy,h1 _ he,sub_self]
    · have he : ∀ᶠ y in 𝓝 x,R<Complex.normSq (curveProjection a y)⁻¹ :=
        hinv (isOpen_Ioi.mem_nhds (lt_of_not_ge hhigh))
      refine ⟨1,?_⟩
      filter_upwards [curveEndCutoff_punctured_germ a g ht,he] with y hy he
      rw [hy,image_eq_zero_of_notMem_tsupport (fun hh => not_le_of_gt he (h0 hh)),sub_zero]

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem chartMass_exterior_eq_zero {c : M} {K : Set M}
    (hK : IsCompact K) (hKc : K⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    {α : ManifoldOneForm Plane M} (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hz : ∀ x,x∉K→α x=0) : chartMass c (manifoldExteriorOneForm α)=0 := by
  classical
  let e := extChartAt 𝓘(ℝ,Plane) c
  let L := e '' K
  have hL : IsCompact L := hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)
  have hLt : L⊆e.target := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hKc hx)
  have hcz (p : ℝ) (y : Plane) (hy : y∈e.target) (hn : y∉L) :
      chartOneForm α c y=0 := by
    have hx : e.symm y∉K := fun hk => hn ⟨_,hk,e.right_inv hy⟩
    change (α (e.symm y)).comp (chartDifferential c (e.symm y)).inverse=0
    rw [hz _ hx,ContinuousLinearMap.zero_comp]
  let β : Plane → Plane →L[ℝ] ℝ := fun y =>
    spatialZeroExtension e.target (fun q : ℝ × Plane => chartOneForm α c q.2) (0,y)
  have hβs : ContDiff ℝ ∞ β := by
    exact (spatialZeroExtension_smooth (isOpen_extChartAt_target c) hL.isClosed hLt
      (hα c) hcz).comp (contDiff_const.prodMk contDiff_id)
  have hβz (y : Plane) (hy : y∉L) : β y=0 := spatialZeroExtension_zero hcz 0 hy
  have hβc : HasCompactSupport β := HasCompactSupport.intro hL hβz
  have he (y : Plane) : extendedChartCoefficient c (fun _ : ℝ => manifoldExteriorOneForm α) (0,y)=
      fderiv ℝ β y (1,0) (0,1)-fderiv ℝ β y (0,1) (1,0) := by
    by_cases hy : y∈e.target
    · have hg : β =ᶠ[𝓝 y] chartOneForm α c := by
        filter_upwards [(isOpen_extChartAt_target c).mem_nhds hy] with z hz
        exact ite_eq_left hz
      change (if y∈e.target then chartTwoForm (manifoldExteriorOneForm α) c y (1,0) (0,1) else 0)=_
      rw [ite_eq_left hy,manifoldExteriorOneForm_chart
        (fun b z hz => (hα.spatial_smooth 0 b hz).contDiffWithinAt) hy,hg.fderiv_eq]
      rfl
    · have hn : y∉L := fun hyL => hy (hLt hyL)
      have hg : β =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hL.isClosed.isOpen_compl.mem_nhds hn] with z hz
        exact hβz z hz
      change (if y∈e.target then chartTwoForm (manifoldExteriorOneForm α) c y (1,0) (0,1) else 0)=_
      rw [ite_eq_right hy,hg.fderiv_eq]
      simp only [fderiv_const_apply,zero_apply,sub_self]
  unfold chartMass
  simp_rw [he]
  exact compact_planar_stokes hβs hβc

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I : Type*}

structure SurfaceMassTransferData (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M) where
  bump : ∀ i, BoxUnitBump (B i)
  common : BoxUnitBump B₀
  primitive : I → ManifoldOneForm Plane M
  supportSet : I → Set M
  compact_supportSet : ∀ i, IsCompact (supportSet i)
  zero_off : ∀ i x, x ∉ supportSet i → primitive i x=0
  primitive_spec : ∀ i, IsPrimitiveFamily (fun _ : ℝ => (bump i).form-common.form)
    (fun _ : ℝ => primitive i)

theorem exists_surface_mass_transfer_data [PreconnectedSpace M] (hpos : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M) :
    Nonempty (SurfaceMassTransferData B B₀) := by
  classical
  let β (i : I) : BoxUnitBump (B i) := Classical.choice (B i).exists_unit_bump
  obtain ⟨β₀⟩ := B₀.exists_unit_bump
  have hh (i : I) := surface_bump_difference (P := ℝ) hpos (β i) β₀
  choose K hK α hα hzero hd using hh
  refine ⟨⟨β,β₀,(fun i => α i 0),K,hK,(fun i => hzero i 0),?_⟩⟩
  intro i
  exact (IsPrimitiveFamily.const_slice (P := ℝ)
    (show IsPrimitiveFamily (fun _ : ℝ => (β i).form-β₀.form) (α i) from ⟨hα i,hd i⟩) 0)

end

theorem planarMarginal_add {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g)
    (A t : ℝ) : planarMarginal A (f+g) t = planarMarginal A f t+planarMarginal A g t := by
  exact intervalIntegral.integral_add
    ((hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable (-A) A)
    ((hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable (-A) A)

theorem planarMarginal_smul (f : Plane → ℝ) (A c t : ℝ) :
    planarMarginal A (c • f) t = c*planarMarginal A f t := by
  exact intervalIntegral.integral_const_mul c _

theorem planarPrimitiveX_add {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (A : ℝ) (ρ : ℝ → ℝ) (p : Plane) :
    planarPrimitiveX A (f+g) ρ p = planarPrimitiveX A f ρ p+planarPrimitiveX A g ρ p := by
  unfold planarPrimitiveX
  simp_rw [planarMarginal_add hf.continuous hg.continuous]
  rw [intervalIntegral.integral_add ((planarMarginal_smooth hf A).continuous.intervalIntegrable _ _)
    ((planarMarginal_smooth hg A).continuous.intervalIntegrable _ _)]
  ring

theorem planarPrimitiveY_add {f g : Plane → ℝ} (hf : Continuous f)
    (hg : Continuous g) {ρ : ℝ → ℝ} (hρ : Continuous ρ) (A : ℝ) (p : Plane) :
    planarPrimitiveY A (f+g) ρ p = planarPrimitiveY A f ρ p+planarPrimitiveY A g ρ p := by
  unfold planarPrimitiveY
  rw [planarMarginal_add hf hg]
  have he : (fun x => (f+g) (x,p.2)-ρ x*(planarMarginal A f p.2+planarMarginal A g p.2)) =
      (fun x => (f (x,p.2)-ρ x*planarMarginal A f p.2)+(g (x,p.2)-ρ x*planarMarginal A g p.2)) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact intervalIntegral.integral_add
    (((hf.comp (continuous_id.prodMk continuous_const)).sub (hρ.mul continuous_const)).intervalIntegrable _ _)
    (((hg.comp (continuous_id.prodMk continuous_const)).sub (hρ.mul continuous_const)).intervalIntegrable _ _)

theorem planarPrimitiveX_smul (f : Plane → ℝ) (A c : ℝ) (ρ : ℝ → ℝ) (p : Plane) :
    planarPrimitiveX A (c • f) ρ p = c*planarPrimitiveX A f ρ p := by
  unfold planarPrimitiveX
  simp_rw [planarMarginal_smul,intervalIntegral.integral_const_mul]
  ring

theorem planarPrimitiveY_smul (f : Plane → ℝ) (A c : ℝ) (ρ : ℝ → ℝ) (p : Plane) :
    planarPrimitiveY A (c • f) ρ p = c*planarPrimitiveY A f ρ p := by
  unfold planarPrimitiveY
  rw [planarMarginal_smul]
  have he : (fun x => (c • f) (x,p.2)-ρ x*(c*planarMarginal A f p.2)) =
      (fun x => c*(f (x,p.2)-ρ x*planarMarginal A f p.2)) := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,intervalIntegral.integral_const_mul]

def smoothPlanarFunctions : Submodule ℝ (Plane → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : Plane => (0:ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    exact contDiff_const.smul hf

def planarPrimitiveLinear (A : ℝ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    smoothPlanarFunctions →ₗ[ℝ] smoothPlanarFunctions × smoothPlanarFunctions where
  toFun f := (⟨planarPrimitiveX A f ρ,(planarPrimitive_smooth f.property hρ A).1⟩,
    ⟨planarPrimitiveY A f ρ,(planarPrimitive_smooth f.property hρ A).2⟩)
  map_add' f g := by
    apply Prod.ext <;> apply Subtype.ext <;> funext p
    · exact planarPrimitiveX_add f.property g.property A ρ p
    · exact planarPrimitiveY_add (show ContDiff ℝ ∞ (f:Plane→ℝ) from f.property).continuous (show ContDiff ℝ ∞ (g:Plane→ℝ) from g.property).continuous hρ.continuous A p
  map_smul' c f := by
    apply Prod.ext <;> apply Subtype.ext <;> funext p
    · exact planarPrimitiveX_smul f A c ρ p
    · exact planarPrimitiveY_smul f A c ρ p

def primitiveLineBump (A : ℝ) (hA : 0<A) : ℝ → ℝ :=
  (⟨A/2,A,by positivity,by linarith⟩ : ContDiffBump (0:ℝ)).normed volume

def fixedCovectorOperator (A : ℝ) (hA : 0<A) (f : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  planarCovector (planarPrimitiveX A f (primitiveLineBump A hA) z)
    (planarPrimitiveY A f (primitiveLineBump A hA) z)

theorem primitiveLineBump_smooth (A : ℝ) (hA : 0<A) : ContDiff ℝ ∞ (primitiveLineBump A hA) :=
  ContDiffBump.contDiff_normed _

theorem fixedCovectorOperator_add (A : ℝ) (hA : 0<A) {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    fixedCovectorOperator A hA (f+g) = fixedCovectorOperator A hA f+fixedCovectorOperator A hA g := by
  funext z
  unfold fixedCovectorOperator
  rw [planarPrimitiveX_add hf hg,planarPrimitiveY_add hf.continuous hg.continuous
    (primitiveLineBump_smooth A hA).continuous]
  simp only [planarCovector,add_smul,Pi.add_apply]
  abel

theorem fixedCovectorOperator_smul (A : ℝ) (hA : 0<A) (f : Plane → ℝ) (a : ℝ) :
    fixedCovectorOperator A hA (a • f) = a • fixedCovectorOperator A hA f := by
  funext z
  unfold fixedCovectorOperator
  rw [planarPrimitiveX_smul,planarPrimitiveY_smul]
  simp only [planarCovector,Pi.smul_apply,smul_add,smul_smul]

theorem fixedCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ContDiff ℝ ∞ (fun q : P × Plane => fixedCovectorOperator A hA (fun x => f (q.1,x)) q.2) ∧
      (∀ p x y, A ≤ |x| ∨ A ≤ |y| → fixedCovectorOperator A hA (fun z => f (p,z)) (x,y)=0) ∧
      (∀ p z, euclideanExteriorOneForm (fixedCovectorOperator A hA (fun x => f (p,x))) z =
        f (p,z) • planarArea) := by
  let b : ContDiffBump (0 : ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let ρ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρs (x : ℝ) (hx : A ≤ |x|) : ρ x=0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hh : |x|<A := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hh
  have hρ1 : (∫ x in -A..A, ρ x)=1 := by
    rw [integral_eq_full_of_box_support hρs]
    exact b.integral_normed
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hfc (y : P) : HasCompactSupport (fun x => f (y,x)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) A)
    intro p hp
    have hh : A < max |p.1| |p.2| := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hp
    exact hzero y p.1 p.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  have hg (y : P) : ContDiff ℝ ∞ (planarMarginal A (fun x => f (y,x))) :=
    planarMarginal_smooth (hfy y) A
  have hgt (y : P) (t : ℝ) (ht : A ≤ |t|) : planarMarginal A (fun x => f (y,x)) t=0 := by
    unfold planarMarginal
    have he : (fun x => f (y,(x,t))) = fun _ => (0:ℝ) := funext fun x => hzero y x t (Or.inr ht)
    rw [he,intervalIntegral.integral_zero]
  have hgm (y : P) (t : ℝ) : planarMarginal A (fun x => f (y,x)) t = ∫ x, f (y,(x,t)) :=
    integral_eq_full_of_box_support (fun x hx => hzero y x t (Or.inl hx))
  have hgm0 (y : P) : (∫ t in -A..A, planarMarginal A (fun x => f (y,x)) t)=0 := by
    rw [integral_eq_full_of_box_support (hgt y)]
    simp_rw [hgm]
    rw [←integral_prod_symm (fun x => f (y,x))]
    · exact hmass y
    · exact (hfy y).continuous.integrable_of_hasCompactSupport (hfc y)
  let U : P × Plane → ℝ := fun p => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2
  let V : P × Plane → ℝ := fun p => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2
  have hU : ContDiff ℝ ∞ U := (planarPrimitive_parameter_smooth hf hρ A).1
  have hV : ContDiff ℝ ∞ V := (planarPrimitive_parameter_smooth hf hρ A).2
  change ContDiff ℝ ∞ (fun q => planarCovector (U q) (V q)) ∧
    (∀ p x y, A ≤ |x| ∨ A ≤ |y| → planarCovector (U (p,(x,y))) (V (p,(x,y)))=0) ∧
    (∀ p z, euclideanExteriorOneForm (fun x => planarCovector (U (p,x)) (V (p,x))) z = f (p,z) • planarArea)
  refine ⟨planarCovector_smooth hU hV,?_,?_⟩
  · intro p x y h
    obtain ⟨h1,h2⟩ := planarPrimitive_zero_outside hA.le (hfy p).continuous hρ.continuous
      (hzero p) hρs hρ1 (hg p).continuous (hgm0 p) (x,y) h
    change planarCovector (planarPrimitiveX A (fun z => f (p,z)) ρ (x,y))
      (planarPrimitiveY A (fun z => f (p,z)) ρ (x,y))=0
    rw [h1,h2,planarCovector_zero]
  · intro p z
    have hUp : ContDiff ℝ ∞ (fun x => U (p,x)) := hU.comp (contDiff_const.prodMk contDiff_id)
    have hVp : ContDiff ℝ ∞ (fun x => V (p,x)) := hV.comp (contDiff_const.prodMk contDiff_id)
    rw [planarCovector_exterior hUp hVp]
    congr 1
    exact planarPrimitive_curl (hfy p).continuous hρ.continuous (hg p).continuous z

def translatedCovectorOperator (A : ℝ) (hA : 0<A) (a : Plane) (f : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  fixedCovectorOperator A hA (fun w => f (w+a)) (z-a)

theorem translatedCovectorOperator_add (A : ℝ) (hA : 0<A) (a : Plane)
    {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    translatedCovectorOperator A hA a (f+g) =
      translatedCovectorOperator A hA a f+translatedCovectorOperator A hA a g := by
  funext z
  change fixedCovectorOperator A hA ((fun w => f (w+a))+(fun w => g (w+a))) (z-a) = _
  have hfa : ContDiff ℝ ∞ (fun w => f (w+a)) := hf.comp (contDiff_id.add contDiff_const)
  have hga : ContDiff ℝ ∞ (fun w => g (w+a)) := hg.comp (contDiff_id.add contDiff_const)
  rw [fixedCovectorOperator_add A hA hfa hga]
  rfl

theorem translatedCovectorOperator_smul (A : ℝ) (hA : 0<A) (a : Plane)
    (f : Plane → ℝ) (r : ℝ) :
    translatedCovectorOperator A hA a (r • f) = r • translatedCovectorOperator A hA a f := by
  funext z
  change fixedCovectorOperator A hA (r • fun w => f (w+a)) (z-a) = _
  rw [fixedCovectorOperator_smul]
  rfl

theorem translated_covector_family_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {β : P × Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (a : Plane) :
    ContDiff ℝ ∞ (fun q : P × Plane => β (q.1,q.2-a)) :=
  hβ.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))

theorem covector_family_slice_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {β : P × Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (p : P) :
    ContDiff ℝ ∞ (fun z => β (p,z)) :=
  hβ.comp (contDiff_const.prodMk contDiff_id)

theorem translatedCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A) (a : Plane)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ContDiff ℝ ∞ (fun q : P × Plane => translatedCovectorOperator A hA a (fun x => f (q.1,x)) q.2) ∧
      (∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → translatedCovectorOperator A hA a (fun z => f (p,z)) (x,y)=0) ∧
      (∀ p z, euclideanExteriorOneForm (translatedCovectorOperator A hA a (fun x => f (p,x))) z =
        f (p,z) • planarArea) := by
  let g : P × Plane → ℝ := fun q => f (q.1,q.2+a)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hgzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → g (p,(x,y))=0 := by
    intro p x y h
    apply hzero
    simpa only [add_sub_cancel_right] using h
  have hgmass : ∀ p, (∫ x, g (p,x))=0 := by
    intro p
    exact (integral_add_right_eq_self (fun x => f (p,x)) a).trans (hmass p)
  have hs := fixedCovectorOperator_spec (P := P) (A := A) hA (f := g) hg hgzero hgmass
  refine ⟨?_,?_,?_⟩
  · have hh : ContDiff ℝ ∞ (fun q : P × Plane =>
        fixedCovectorOperator A hA (fun w => g (q.1,w)) (q.2-a)) :=
      translated_covector_family_smooth (β := fun q : P × Plane =>
        fixedCovectorOperator A hA (fun w => g (q.1,w)) q.2) hs.1 a
    exact hh
  · intro p x y h
    exact hs.2.1 p (x-a.1) (y-a.2) h
  · intro p z
    have hβp : ContDiff ℝ ∞ (fixedCovectorOperator A hA (fun x => g (p,x))) :=
      covector_family_slice_smooth (β := fun q : P × Plane =>
        fixedCovectorOperator A hA (fun w => g (q.1,w)) q.2) hs.1 p
    change euclideanExteriorOneForm (fun x => fixedCovectorOperator A hA (fun w => g (p,w)) (x-a)) z = _
    rw [translated_covector_exterior (a := a) (z := z) hβp,hs.2.2]
    simp only [g,sub_add_cancel]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

def boxCovectorOperator (B : SurfaceCoordinateBox M) (Ω : ManifoldTwoForm Plane M) :
    ManifoldOneForm Plane M :=
  chartSupportedOneForm B.center (translatedCovectorOperator B.radius B.radius_pos B.point
    (fun y => extendedChartCoefficient B.center (fun _ : ℝ => Ω) (0,y)))

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem chartSupportedOneForm_add (c : M) (α β : Plane → Plane →L[ℝ] ℝ) :
    chartSupportedOneForm c (α+β) = chartSupportedOneForm c α + chartSupportedOneForm c β := by
  funext x
  simp only [Pi.add_apply,chartSupportedOneForm]
  split_ifs
  · apply ContinuousLinearMap.ext
    intro u
    rfl
  · simp only [add_zero]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem chartSupportedOneForm_smul (c : M) (a : ℝ) (α : Plane → Plane →L[ℝ] ℝ) :
    chartSupportedOneForm c (a • α) = a • chartSupportedOneForm c α := by
  funext x
  simp only [Pi.smul_apply,chartSupportedOneForm]
  split_ifs
  · apply ContinuousLinearMap.ext
    intro u
    rfl
  · simp only [smul_zero]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem extendedChartCoefficient_smul (c : M) (a : ℝ) (Ω : ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => a • Ω) (0,y) =
      a * extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y) := by
  unfold extendedChartCoefficient spatialZeroExtension
  split_ifs <;> simp only [chartTwoForm_smul,smul_apply,smul_eq_mul,mul_zero]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem boxCovectorOperator_smul (B : SurfaceCoordinateBox M) (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    boxCovectorOperator B (a • Ω) = a • boxCovectorOperator B Ω := by
  unfold boxCovectorOperator
  have he : (fun y => extendedChartCoefficient B.center (fun _ : ℝ => a • Ω) (0,y)) =
      a • (fun y => extendedChartCoefficient B.center (fun _ : ℝ => Ω) (0,y)) := by
    funext y; exact extendedChartCoefficient_smul B.center a Ω y
  rw [he,translatedCovectorOperator_smul,chartSupportedOneForm_smul]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem static_chart_coefficient_smooth {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (c : M) {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0) :
    ContDiff ℝ ∞ (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)) :=
  (extendedChartCoefficient_smooth (P := ℝ) (c := c) (Ω := fun _ : ℝ => Ω)
    (SmoothTwoFormFamily.const (P := ℝ) (M := M) hΩ c) (K := K) hK hKc
    (fun _ x hx => hz x hx)).comp (f := fun y : Plane => ((0:ℝ),y))
      (contDiff_const.prodMk contDiff_id)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem boxCovectorOperator_add (B : SurfaceCoordinateBox M)
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKB : K ⊆ B.carrier) (hLB : L ⊆ B.carrier)
    (hzΩ : ∀ x, x ∉ K → Ω x=0) (hzΛ : ∀ x, x ∉ L → Λ x=0) :
    boxCovectorOperator B (Ω+Λ) = boxCovectorOperator B Ω + boxCovectorOperator B Λ := by
  unfold boxCovectorOperator
  have he : (fun y => extendedChartCoefficient B.center (fun _ : ℝ => Ω+Λ) (0,y)) =
      (fun y => extendedChartCoefficient B.center (fun _ : ℝ => Ω) (0,y)) +
        (fun y => extendedChartCoefficient B.center (fun _ : ℝ => Λ) (0,y)) := by
    funext y; exact extendedChartCoefficient_add B.center Ω Λ y
  rw [he,translatedCovectorOperator_add B.radius B.radius_pos B.point
    (static_chart_coefficient_smooth hΩ B.center hK (fun x hx => (hKB hx).1) hzΩ)
    (static_chart_coefficient_smooth hΛ B.center hL (fun x hx => (hLB hx).1) hzΛ),
    chartSupportedOneForm_add]

theorem boxCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (B : SurfaceCoordinateBox M)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u)
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (hz : ∀ p x, x ∉ K → Ω p x=0) (hmass : ∀ p, chartMass B.center (Ω p)=0) :
    SmoothOneFormFamily (fun p => boxCovectorOperator B (Ω p)) ∧
      (∀ p x, x ∉ B.compactCarrier → boxCovectorOperator B (Ω p) x=0) ∧
      (∀ p c y, y ∈ (extChartAt 𝓘(ℝ,Plane) c).target →
        euclideanExteriorOneForm (chartOneForm (boxCovectorOperator B (Ω p)) c) y =
          chartTwoForm (Ω p) c y) := by
  have hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) B.center).source := fun x hx => (hKB hx).1
  let f := extendedChartCoefficient B.center Ω
  have hf : ContDiff ℝ ∞ f := extendedChartCoefficient_smooth (hΩ B.center) hK hKc hz
  have hzero (p : P) (x y : ℝ) (hxy : B.radius ≤ |x-B.point.1| ∨ B.radius ≤ |y-B.point.2|) :
      f (p,(x,y))=0 := by
    apply extendedChartCoefficient_zero hz p
    rintro ⟨z,hzK,hzxy⟩
    have hb := (hKB hzK).2
    change extChartAt 𝓘(ℝ,Plane) B.center z ∈ Metric.ball B.point B.radius at hb
    rw [hzxy] at hb
    have hh : max |x-B.point.1| |y-B.point.2| < B.radius := by
      simpa only [Metric.mem_ball,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] using hb
    rcases hxy with hx|hy
    · exact False.elim ((not_lt_of_ge hx) (lt_of_le_of_lt (le_max_left _ _) hh))
    · exact False.elim ((not_lt_of_ge hy) (lt_of_le_of_lt (le_max_right _ _) hh))
  let β : P × Plane → Plane →L[ℝ] ℝ := fun q =>
    translatedCovectorOperator B.radius B.radius_pos B.point (fun y => f (q.1,y)) q.2
  have hs := translatedCovectorOperator_spec B.radius_pos B.point hf hzero hmass
  have hbzero (p : P) (z : Plane) (hz : z ∉ Metric.closedBall B.point B.radius) : β (p,z)=0 := by
    have hh : B.radius < max |z.1-B.point.1| |z.2-B.point.2| := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
        Real.norm_eq_abs,not_le] using hz
    exact hs.2.1 p z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  refine ⟨?_,?_,?_⟩
  · intro c
    exact chartSupportedOneForm_smooth hs.1 (isCompact_closedBall B.point B.radius) B.closed_subset hbzero c
  · intro p x hx
    exact chartSupportedOneForm_zero (hbzero p) hx
  · intro p c y hy
    have hp : ContDiff ℝ ∞ (fun z => β (p,z)) := hs.1.comp (contDiff_const.prodMk contDiff_id)
    change euclideanExteriorOneForm (chartOneForm (chartSupportedOneForm B.center (fun z => β (p,z))) c) y = _
    rw [chartSupportedOneForm_exterior hp (isCompact_closedBall B.point B.radius) B.closed_subset (hbzero p) hy]
    have he : euclideanExteriorOneForm (fun z => β (p,z)) = fun z => f (p,z) • planarArea := funext (hs.2.2 p)
    rw [he]
    exact congrArg (fun Ω => chartTwoForm Ω c y) (chartSupported_extendedCoefficient hskew hKc hz p)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
