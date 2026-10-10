import Mathlib
import OAI.Geometry.BallPacking.SurfaceArea.SurfaceCutoffDefect

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveEndAnnulus_coordinates {r R : ℝ} (hr : 0<r)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a) (ε : Fin m → Bool) :
    (infinityDiffeomorph a ε).symm '' curveEndAnnulus a ε r R=radialAnnulus r R :=
  (infinityDiffeomorph a ε).toPartialEquiv.symm_image_image_of_subset_source
    (radialAnnulus_in_end a hr hR ε)

theorem curveEndCutoff_partition_mass {I : Type*} [Fintype I] {K : Set (locus a)}
    (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox (locus a))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus a) K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκK : tsupport (curveEndCutoff a g)⊆K)
    (hSK : ∀ ε : Fin m → Bool,curveEndAnnulus a ε r R⊆K) (c : ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
    (he : ∀ ε,β ε=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c) :
    partitionFormMass B ρ (fun x => curveEndCutoff a g x • curveFSForm a c x)=
      (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z := by
  have hκ := curveEndCutoff_smooth a hg hc
  have hα := curveFSPrimitive_smooth a c
  have hzκ (x : locus a) (hx : x∉K) : curveEndCutoff a g x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hκK hh))
  have hm := partitionFormMass_cutoff_defect (positivePlaneTransitions a) hK B ρ hρ hκ hα hzκ
  rw [curveFSPrimitive_exterior] at hm
  rw [hm]
  have hd := partitionFormMass_finite_disjoint_charts hK (infinityDiffeomorph a)
    (infinityDiffeomorph_positive a)
    (fun i j hij => by simpa only [infinityDiffeomorph_target] using infinityBranch_disjoint a hij)
    (fun ε => curveEndAnnulus a ε r R) (curveEndAnnulus_compact a hr hR) hSK
    (curveEndAnnulus_subset_target a hr hR) B ρ hρ
    (spatialCutoffDefect_smooth hκ hα) (spatialCutoffDefect_skew _ _)
    (fun x hx => curveCutoffDefect_zero_off_annuli a hc hr hR h1 h0 c hx)
  rw [hd]
  have hi (ε : Fin m → Bool) :
      (∫ y in (infinityDiffeomorph a ε).symm '' curveEndAnnulus a ε r R,
        partialChartCoefficient (infinityDiffeomorph a ε)
          (spatialCutoffDefect (curveEndCutoff a g) (curveFSPrimitive a c)) y)=
        (∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z)-c*Real.pi := by
    rw [curveEndAnnulus_coordinates a hr hR ε]
    calc
      _ = ∫ y in radialAnnulus r R,-cutoffWedge (fun z => g (radiusSq z)) (β ε) y+c*deriv g (radiusSq y) := by
        apply setIntegral_congr_fun (radialAnnulus_compact r R).measurableSet
        intro y hy
        exact curveCutoffDefect_end_coefficient a hg hc ε c (radialAnnulus_in_end a hr hR ε hy)
          (regular_extension_germ a (he ε) hy.2)
      _ = _ := integral_planar_residue_annulus hg hc hr h1 h0 (hβ ε) c
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,infinity_end_count,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 def partitionOnSubset {I : Type*} {K D : Set M}
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (hDK : D⊆K) :
    SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M D where
  toFun := ρ.toFun
  locallyFinite' := ρ.locallyFinite
  nonneg' := ρ.nonneg
  sum_eq_one' := fun _ hx => ρ.sum_eq_one (hDK hx)
  sum_le_one' := ρ.sum_le_one

omit [T2Space M] in
theorem partitionFormMass_independent_support {I J : Type*} [Fintype I] [Fintype J]
    {K D L : Set M} (hor : PositivePlaneTransitions M) (hL : IsCompact L)
    (hLK : L⊆K) (hLD : L⊆D)
    (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M D)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉L→Ω x=0) :
    partitionFormMass B ρ Ω=partitionFormMass C ν Ω :=
  partitionFormMass_independent hor hL B C (partitionOnSubset ρ hLK)
    (partitionOnSubset ν hLD) hρ hν hΩ ha hz

variable [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

theorem compactSurfaceFormIntegral_eq_larger_partition {I : Type*} [Fintype I]
    {K D : Set M} (hD : IsCompact D) (hor : PositivePlaneTransitions M) (hDK : D⊆K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) :
    compactSurfaceFormIntegral hD Ω=restrictedPartitionFormMass B ρ D Ω :=
  compactSurfaceFormIntegral_eq hD hor B (partitionOnSubset ρ hDK) hρ hΩ ha

theorem compactSurfaceFormIntegral_eq_setIntegral {I : Type*} [Fintype I]
    {K D : Set M} (hD : IsCompact D) (hor : PositivePlaneTransitions M) (hDK : D⊆K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0≤chartTwoForm Ω c y (1,0) (0,1)) :
    compactSurfaceFormIntegral hD Ω=∫ _ in D,(1:ℝ) ∂partitionAreaMeasure B ρ Ω := by
  rw [compactSurfaceFormIntegral_eq_larger_partition hD hor hDK B ρ hρ hΩ ha,
    integral_partitionAreaMeasure_restrict B ρ hρ hΩ hp hD.measurableSet contMDiff_const]
  congr 1
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω x u v=(1:ℝ)*Ω x u v
  ring

def surfaceCutoffMass {κ : M → ℝ} (hκc : HasCompactSupport κ)
    (Ω : ManifoldTwoForm Plane M) : ℝ :=
  partitionFormMass (fun b : compactSurfaceBoxes hκc => b.1)
    (compactSurfacePartition hκc) (fun x => κ x • Ω x)

omit [MeasurableSpace M] [BorelSpace M] in
theorem surfaceCutoffMass_eq {I : Type*} [Fintype I] {K : Set M}
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {κ : M → ℝ} (hκc : HasCompactSupport κ) (hκK : tsupport κ⊆K)
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) :
    surfaceCutoffMass hκc Ω=partitionFormMass B ρ (fun x => κ x • Ω x) := by
  apply partitionFormMass_independent_support hor hκc Subset.rfl hκK _ B _ ρ
    (compactSurfacePartition_subordinate hκc) hρ
    (((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul hκ).eval 0)
  · intro x u v
    change κ x*Ω x u v= -(κ x*Ω x v u)
    rw [ha x u v]
    ring
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ)*Ω x u v=0
    exact zero_mul _

theorem surfaceCutoffMass_le_compactIntegral {D : Set M}
    (hor : PositivePlaneTransitions M) (hD : IsCompact D)
    {κ : M → ℝ} (hκc : HasCompactSupport κ) (hκD : tsupport κ⊆D)
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hb : ∀ x,κ x≤1)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0≤chartTwoForm Ω c y (1,0) (0,1)) :
    surfaceCutoffMass hκc Ω≤compactSurfaceFormIntegral hD Ω := by
  let B := fun b : compactSurfaceBoxes hD => b.1
  let ρ := compactSurfacePartition hD
  have hρ := compactSurfacePartition_subordinate hD
  rw [surfaceCutoffMass_eq hor B ρ hρ hκc hκD hκ hΩ ha,
    ← integral_partitionAreaMeasure B ρ hρ hΩ hp hκ,
    compactSurfaceFormIntegral_eq_setIntegral hD hor Subset.rfl B ρ hρ hΩ ha hp,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D) (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun hn => hx (hκD hn)))]
  exact integral_mono_ae
    (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp hκ).integrableOn
    (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp contMDiff_const).integrableOn
    (Filter.Eventually.of_forall hb)

theorem compactIntegral_le_surfaceCutoffMass {D : Set M}
    (hor : PositivePlaneTransitions M) (hD : IsCompact D)
    {κ : M → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ κ) (hn : ∀ x,0≤κ x)
    (h1 : ∀ x∈D,κ x=1)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0≤chartTwoForm Ω c y (1,0) (0,1)) :
    compactSurfaceFormIntegral hD Ω≤ surfaceCutoffMass hκc Ω := by
  have hDK : D⊆tsupport κ := by
    intro x hx
    apply subset_tsupport κ
    change κ x≠0
    rw [h1 x hx]
    exact one_ne_zero
  let B := fun b : compactSurfaceBoxes hκc => b.1
  let ρ := compactSurfacePartition hκc
  have hρ := compactSurfacePartition_subordinate hκc
  rw [compactSurfaceFormIntegral_eq_setIntegral hD hor hDK B ρ hρ hΩ ha hp]
  change (∫ x in D,(1:ℝ) ∂partitionAreaMeasure B ρ Ω)≤partitionFormMass B ρ (fun x => κ x • Ω x)
  rw [← integral_partitionAreaMeasure B ρ hρ hΩ hp hκ]
  calc
    _ = ∫ x in D,κ x ∂partitionAreaMeasure B ρ Ω :=
      setIntegral_congr_fun hD.measurableSet (fun x hx => (h1 x hx).symm)
    _ ≤ _ := setIntegral_le_integral
      (smooth_integrable_partitionAreaMeasure B ρ hρ hΩ hp hκ) (Filter.Eventually.of_forall hn)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance quadricEndResidueMassSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

theorem curveEndCutoff_surface_mass
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκc : HasCompactSupport (curveEndCutoff a g)) (c : ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
    (he : ∀ ε,β ε=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c) :
    surfaceCutoffMass hκc (curveFSForm a c)=
      (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z := by
  let K := tsupport (curveEndCutoff a g)∪⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R
  have hK : IsCompact K := hκc.union (isCompact_iUnion (curveEndAnnulus_compact a hr hR))
  let B := fun b : compactSurfaceBoxes hK => b.1
  let ρ := compactSurfacePartition hK
  have hρ := compactSurfacePartition_subordinate hK
  rw [surfaceCutoffMass_eq (positivePlaneTransitions a) B ρ hρ hκc subset_union_left
    (curveEndCutoff_smooth a hg hc) (curveFSForm_smooth a c) (curveFSForm_skew a c)]
  exact curveEndCutoff_partition_mass a hK B ρ hρ hg hc hr hR h1 h0 subset_union_left
    (fun ε => (subset_iUnion (curveEndAnnulus a · r R) ε).trans subset_union_right) c β hβ he

theorem tendsto_curveEndCutoff_mass
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hRp : 0≤R) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hb : ∀ t,g t∈Icc (0:ℝ) 1) (c : ℝ) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n)
      (curveFSForm a c)) atTop (𝓝 ((2:ℝ)^m*c*Real.pi)) := by
  classical
  choose β hβ hβc he using fun ε : Fin m → Bool => exists_infinityRegularPrimitive_extension a hR ε c
  have hmass (n : ℕ) : surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) (curveFSForm a c)=
      (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,shrinkingCutoff g n (radiusSq z)*planarCurl (β ε) z :=
    curveEndCutoff_surface_mass a (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hc n)
      (div_pos hr (by positivity : 0<(n:ℝ)+1)) hR (shrinkingCutoff_one h1 n)
      (shrinkingCutoff_tsupport hRp h0 n) _ c β hβ he
  simp_rw [hmass]
  have hs := tendsto_finsetSum Finset.univ (fun ε _ => tendsto_shrinking_regular_residue hg hc hb (hβ ε) (hβc ε))
  have hh := (tendsto_const_nhds (x := (2:ℝ)^m*c*Real.pi)).sub hs
  simpa only [Finset.sum_const_zero,sub_zero] using hh

end

variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

namespace NormalChart
variable (e : NormalChart a) (x : locus a)

def realSliceChart : OpenPartialHomeomorph (locus a) RealModel :=
  (e.sliceChart x).trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realSliceChart_source : (e.realSliceChart x).source=(e.sliceChart x).source := by
  simp [realSliceChart]

theorem realSliceChart_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (e.realSliceChart x) :=
  Complex.equivRealProdCLM.contDiff.contMDiff.comp
    (((e.coordinate |> curveCoordinate).restrictScalars ℝ).contDiff.contMDiff.comp
      (real_inclusion_contMDiff a))

theorem realSliceChart_symm_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (e.realSliceChart x).symm
      (e.realSliceChart x).target := by
  intro y hy
  apply real_contMDiffWithinAt_of_ambient
  have hs := (e.sliceChart_inverse_smooth x).restrict_scalars ℝ
  have hc := hs.comp Complex.equivRealProdCLM.symm.contDiff.contDiffOn
    (mapsTo_preimage _ _)
  apply (hc _ hy.2).mono
  intro z hz
  exact hz.2

def realSliceDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    (locus a) RealModel ∞ where
  __ := e.realSliceChart x
  contMDiffOn_toFun := (e.realSliceChart_smooth x).contMDiffOn
  contMDiffOn_invFun := e.realSliceChart_symm_smooth x

end NormalChart

theorem exists_projection_chart (x : locus a) (hx : ∀ j,x.val.2 j≠0) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) (locus a) RealModel ∞,
      x∈e.source ∧ ∀ y,e y=Complex.equivRealProdCLM y.val.1 := by
  obtain ⟨e,he,_hreg,heq,_hf,hg⟩ := exists_normal_straightening a none hx
  let E : NormalChart a := ⟨none,e,heq,hg⟩
  refine ⟨E.realSliceDiffeomorph x,?_,fun y => rfl⟩
  change x∈(E.realSliceChart x).source
  rw [E.realSliceChart_source]
  exact he

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology
open Set Function Manifold

abbrev DiskPlane := ℝ × ℝ

def diskBoundaryMap (R : ℝ) (p q : DiskPlane) : DiskPlane :=
  (p.1*q.2-p.2*q.1,R^2-(q.1^2+q.2^2))

def diskBoundaryDerivative (p q : DiskPlane) : DiskPlane →L[ℝ] DiskPlane :=
  (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ - p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((-2*q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ+(-2*q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem diskBoundaryMap_smooth (R : ℝ) (p : DiskPlane) : ContDiff ℝ ∞ (diskBoundaryMap R p) :=
  ((contDiff_const.mul contDiff_snd).sub (contDiff_const.mul contDiff_fst)).prodMk
    (contDiff_const.sub ((contDiff_fst.pow 2).add (contDiff_snd.pow 2)))

theorem diskBoundaryMap_hasFDerivAt (R : ℝ) (p q : DiskPlane) :
    HasFDerivAt (diskBoundaryMap R p) (diskBoundaryDerivative p q) q := by
  have h1 := ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).const_mul p.1).sub ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).const_mul p.2)
  have h2 := (((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).pow 2).add ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).pow 2)).const_sub (R^2)
  apply (h1.prodMk h2).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext <;> simp [diskBoundaryDerivative]
  ring

theorem diskBoundaryDerivative_bijective {p q : DiskPlane} (h : p.1*q.1+p.2*q.2≠0) :
    Bijective (diskBoundaryDerivative p q) := by
  have h' : q.1*p.1+q.2*p.2≠0 := by simpa only [mul_comm] using h
  constructor
  · intro v w he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change p.1*v.2-p.2*v.1=p.1*w.2-p.2*w.1 at he1
    change (-2*q.1)*v.1+(-2*q.2)*v.2=(-2*q.1)*w.1+(-2*q.2)*w.2 at he2
    apply Prod.ext
    · apply (mul_left_inj' h).mp
      linear_combination -q.2*he1-p.1/2*he2
    · apply (mul_left_inj' h).mp
      linear_combination q.1*he1-p.2/2*he2
  · intro y
    refine ⟨((-2*q.2*y.1-p.1*y.2)/(2*(p.1*q.1+p.2*q.2)),
      (2*q.1*y.1-p.2*y.2)/(2*(p.1*q.1+p.2*q.2))),?_⟩
    apply Prod.ext
    · change p.1*((2*q.1*y.1-p.2*y.2)/(2*(p.1*q.1+p.2*q.2)))-
        p.2*((-2*q.2*y.1-p.1*y.2)/(2*(p.1*q.1+p.2*q.2)))=y.1
      field_simp [h,h']
      ring
    · change (-2*q.1)*((-2*q.2*y.1-p.1*y.2)/(2*(p.1*q.1+p.2*q.2)))+
        (-2*q.2)*((2*q.1*y.1-p.2*y.2)/(2*(p.1*q.1+p.2*q.2)))=y.2
      field_simp [h,h']
      ring

theorem exists_diskBoundaryDiffeomorph (R : ℝ) {p : DiskPlane}
    (hp : 0<p.1^2+p.2^2) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ,DiskPlane) 𝓘(ℝ,DiskPlane) DiskPlane DiskPlane ∞,
      p∈e.source ∧ (e : DiskPlane→DiskPlane)=diskBoundaryMap R p := by
  have h0 : p.1*p.1+p.2*p.2≠0 := by nlinarith
  let D := diskBoundaryDerivative p p
  let L := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr (diskBoundaryDerivative_bijective h0).1)
    (LinearMap.range_eq_top.mpr (diskBoundaryDerivative_bijective h0).2)
  have hd : HasFDerivAt (diskBoundaryMap R p) (L : DiskPlane→L[ℝ]DiskPlane) p :=
    diskBoundaryMap_hasFDerivAt R p p
  let e0 := (diskBoundaryMap_smooth R p).contDiffAt.toOpenPartialHomeomorph
    (diskBoundaryMap R p) hd (by simp)
  let U : Set DiskPlane := {q | p.1*q.1+p.2*q.2≠0}
  have hU : IsOpen U := isOpen_ne_fun (by fun_prop) continuous_const
  let e := e0.restrOpen U hU
  have he : (e : DiskPlane→DiskPlane)=diskBoundaryMap R p := rfl
  have hi : ContDiffOn ℝ ∞ e.symm e.target := by
    intro y hy
    have hq : p.1*(e.symm y).1+p.2*(e.symm y).2≠0 := (e.map_target hy).2
    let B := diskBoundaryDerivative p (e.symm y)
    let K := ContinuousLinearEquiv.ofBijective B
      (LinearMap.ker_eq_bot.mpr (diskBoundaryDerivative_bijective hq).1)
      (LinearMap.range_eq_top.mpr (diskBoundaryDerivative_bijective hq).2)
    exact (e.contDiffAt_symm (𝕜 := ℝ) (f₀' := K) hy
      (diskBoundaryMap_hasFDerivAt R p (e.symm y))
      (diskBoundaryMap_smooth R p).contDiffAt).contDiffWithinAt
  let E : PartialDiffeomorph 𝓘(ℝ,DiskPlane) 𝓘(ℝ,DiskPlane) DiskPlane DiskPlane ∞ := {
    __ := e
    contMDiffOn_toFun := (diskBoundaryMap_smooth R p).contMDiff.contMDiffOn
    contMDiffOn_invFun := hi.contMDiffOn }
  exact ⟨E,
    ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hd (by simp),h0⟩,he⟩

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology ENNReal NNReal
open Set Function Manifold MeasureTheory
section

 theorem planar_curve_image_null {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ × ℝ}
    (hf : ContDiffOn ℝ 1 f s) : volume (f '' s)=0 := by
  have hd : dimH (f '' s)≤dimH s := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro x hx
    obtain ⟨C,t,ht,hC⟩ := ((hf x hx).contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
    exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩
  have hb : dimH s≤1 := by
    calc
      dimH s≤dimH (Set.univ : Set ℝ) := dimH_mono (subset_univ _)
      _=1 := by simp only [Real.dimH_univ_eq_finrank,Module.finrank_self,Nat.cast_one]
  have hz := hausdorffMeasure_of_dimH_lt (d := (2:ℝ≥0)) ((hd.trans hb).trans_lt (by norm_num))
  simpa only [NNReal.coe_ofNat,hausdorffMeasure_prod_real] using hz

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M]

 theorem smooth_curve_chart_null (c : M) {s : Set ℝ} (hs : IsOpen s) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ γ s) :
    volume ((extChartAt 𝓘(ℝ,ℝ × ℝ) c).target ∩
      (extChartAt 𝓘(ℝ,ℝ × ℝ) c).symm ⁻¹' (γ '' s))=0 := by
  let U := s ∩ γ ⁻¹' (extChartAt 𝓘(ℝ,ℝ × ℝ) c).source
  have hU : IsOpen U := hγ.continuousOn.isOpen_inter_preimage hs (isOpen_extChartAt_source c)
  have hf : ContDiffOn ℝ 1 (extChartAt 𝓘(ℝ,ℝ × ℝ) c ∘ γ) U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    have hc : ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ (extChartAt 𝓘(ℝ,ℝ × ℝ) c) (γ x) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source,mem_preimage] using hx.2)
    exact (hc.comp x ((hγ x hx.1).contMDiffAt (hs.mem_nhds hx.1))).contDiffAt.of_le (by simp)
  apply measure_mono_null _ (planar_curve_image_null hU hf)
  rintro y ⟨hy,t,ht,he⟩
  refine ⟨t,⟨ht,?_⟩,?_⟩
  · change γ t∈(extChartAt 𝓘(ℝ,ℝ × ℝ) c).source
    rw [he]
    exact (extChartAt 𝓘(ℝ,ℝ × ℝ) c).map_target hy
  · change extChartAt 𝓘(ℝ,ℝ × ℝ) c (γ t)=y
    rw [he,(extChartAt 𝓘(ℝ,ℝ × ℝ) c).right_inv hy]

 theorem countable_smooth_curve_cover_chart_null {J : Type*} [Countable J]
    (c : M) (s : J → Set ℝ) (γ : J → ℝ → M) (hs : ∀ i,IsOpen (s i))
    (hγ : ∀ i,ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ (γ i) (s i))
    {C : Set M} (hC : C⊆⋃ i,γ i '' s i) :
    volume ((extChartAt 𝓘(ℝ,ℝ × ℝ) c).target ∩
      (extChartAt 𝓘(ℝ,ℝ × ℝ) c).symm ⁻¹' C)=0 := by
  apply measure_mono_null _ (measure_iUnion_null (fun i => smooth_curve_chart_null c (hs i) (hγ i)))
  intro y hy
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hC hy.2)
  exact mem_iUnion.mpr ⟨i,hy.1,hi⟩

 theorem one_dimensional_image_chart_null
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ,ℝ) ∞ N] [SigmaCompactSpace N]
    (c : M) {f : N → M} (hf : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ f) :
    volume ((extChartAt 𝓘(ℝ,ℝ × ℝ) c).target ∩
      (extChartAt 𝓘(ℝ,ℝ × ℝ) c).symm ⁻¹' range f)=0 := by
  obtain ⟨a,ha,hcover⟩ := countable_cover_nhds_of_sigmaCompact
    (fun x : N => chart_source_mem_nhds ℝ x)
  let : Countable a := ha.to_subtype
  apply countable_smooth_curve_cover_chart_null c
    (fun x : a => (extChartAt 𝓘(ℝ,ℝ) x.1).target)
    (fun x : a => f ∘ (extChartAt 𝓘(ℝ,ℝ) x.1).symm)
    (fun x => isOpen_extChartAt_target x.1)
    (fun x => (hf.contMDiffOn (s := univ)).comp (contMDiffOn_extChartAt_symm x.1) (fun _ _ => mem_univ _))
  rintro y ⟨z,rfl⟩
  have hz : z∈⋃ x∈a,(chartAt ℝ x).source := by rw [hcover]; exact mem_univ _
  obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp hz
  have hzs : z∈(extChartAt 𝓘(ℝ,ℝ) x).source := by simpa only [extChartAt_source] using hzx
  refine mem_iUnion.mpr ⟨⟨x,hx⟩,extChartAt 𝓘(ℝ,ℝ) x z,
    (extChartAt 𝓘(ℝ,ℝ) x).map_source hzs,?_⟩
  simp only [comp_apply,(extChartAt 𝓘(ℝ,ℝ) x).left_inv hzs]

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M]

 def HasSmoothSurfaceBoundary (D : Set M) : Prop :=
  ∀ x∈frontier D,∃ e : PartialDiffeomorph 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ × ℝ) M (ℝ × ℝ) ∞,
    x∈e.source ∧ ∀ y∈e.source,(y∈D ↔ 0≤(e y).2)

 omit [IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M] in
 theorem smooth_boundary_coordinate_zero {D : Set M} (hD : IsClosed D)
    (e : PartialDiffeomorph 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℝ × ℝ) M (ℝ × ℝ) ∞)
    (he : ∀ y∈e.source,(y∈D ↔ 0≤(e y).2)) {x : M}
    (hx : x∈frontier D) (hxe : x∈e.source) : (e x).2=0 := by
  have hge := (he x hxe).mp (hD.frontier_subset hx)
  have hle : (e x).2≤0 := by
    by_contra! hp
    have hu : IsOpen (e.source ∩ e ⁻¹' {z : ℝ × ℝ | 0<z.2}) :=
      e.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_source
        (isOpen_lt continuous_const continuous_snd)
    have hsub : e.source ∩ e ⁻¹' {z : ℝ × ℝ | 0<z.2}⊆D :=
      fun y hy => (he y hy.1).mpr hy.2.le
    exact hx.2 (interior_maximal hsub hu ⟨hxe,hp⟩)
  exact le_antisymm hle hge

 theorem smooth_surface_boundary_chart_null [T2Space M] {D : Set M}
    (hD : IsCompact D) (hb : HasSmoothSurfaceBoundary D) (c : M) :
    volume ((extChartAt 𝓘(ℝ,ℝ × ℝ) c).target ∩
      (extChartAt 𝓘(ℝ,ℝ × ℝ) c).symm ⁻¹' frontier D)=0 := by
  classical
  choose e he hm using (fun x : frontier D => hb x.1 x.2)
  obtain ⟨a,ha⟩ := (hD.of_isClosed_subset isClosed_frontier hD.isClosed.frontier_subset).elim_finite_subcover (fun x : frontier D => (e x).source)
    (fun x => (e x).open_source) (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,he ⟨x,hx⟩⟩)
  let s : a → Set ℝ := fun x => (fun t : ℝ => (t,0)) ⁻¹' (e x.1).target
  let γ : a → ℝ → M := fun x t => (e x.1).symm (t,0)
  have hs (x : a) : IsOpen (s x) := (e x.1).open_target.preimage (continuous_id.prodMk continuous_const)
  have hg (x : a) : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ × ℝ) ∞ (γ x) (s x) :=
    (e x.1).symm.contMDiffOn.comp ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn)
      (fun _ ht => ht)
  apply countable_smooth_curve_cover_chart_null c s γ hs hg
  intro y hy
  obtain ⟨x,hxa,hyx⟩ := mem_iUnion₂.mp (ha hy)
  have heq := smooth_boundary_coordinate_zero hD.isClosed (e x) (hm x) hy hyx
  have hepair : e x y=((e x y).1,0) := Prod.ext rfl heq
  refine mem_iUnion.mpr ⟨⟨x,hxa⟩,(e x y).1,?_,?_⟩
  · change ((e x y).1,0)∈(e x).target
    rw [← hepair]
    exact (e x).map_source hyx
  · change (e x).symm ((e x y).1,0)=y
    rw [← hepair]
    exact (e x).left_inv hyx

end PackingSufficiencySupport.Hamiltonian
end

end OAI
