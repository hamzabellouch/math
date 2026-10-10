import Mathlib
import OAI.Geometry.BallPacking.Projective.CubicEndCoordinates
import OAI.Geometry.BallPacking.Toric.CubicCoefficientDifferential

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 theorem exists_radialPrimitive_smooth_extension {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ)
    {P : Set Radial.Plane} (hP : IsCompact P) (hPS : P⊆Radial.lowerTrapezoid A B)
    {C : Set BaseCurve} (hC : IsCompact C) :
    ∃ Γ : Radial.Plane → ManifoldOneForm RealModel BaseCurve,
      SmoothOneFormFamily Γ ∧ ∀ᶠ q in 𝓝ˢ (P ×ˢ C),q.1∈Radial.lowerTrapezoid A B →
        Γ q.1 q.2=radialPrimitive Radial.latticeIndex D m c q.1 q.2 := by
  let a : BaseCurve → TrapezoidWeight A B → ℝ := fun x i => coefficientNorm (D i) (m i) x
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → ℝ) ∞ a :=
    contMDiff_pi_space.mpr (fun i => coefficientNorm_smooth _ _)
  let F : Radial.Plane × BaseCurve → (TrapezoidWeight A B → ℝ) × Radial.Plane :=
    fun q => (a q.2,q.1)
  have hF : Continuous F := (ha.continuous.comp continuous_snd).prodMk continuous_fst
  obtain ⟨g,hg,U,hU,hKU,he⟩ := Radial.trapezoid_selected_compact_extension hA hAB
    ((hP.prod hC).image hF) (by
      rintro q ⟨z,hz,rfl⟩
      exact ⟨fun i => coefficientNorm_pos _ _ _,hPS hz.1⟩)
  let Γ : Radial.Plane → ManifoldOneForm RealModel BaseCurve :=
    fun p x => ∑ i,g (a x,p) i • weightedFSPrimitive (D i) (m i) c x
  have hterm (i : TrapezoidWeight A B) : SmoothOneFormFamily
      (fun p : Radial.Plane => fun x => g (a x,p) i • weightedFSPrimitive (D i) (m i) c x) := by
    intro b q hq
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,RealModel)) (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hq.2)
    have hac : ContDiffAt ℝ ∞ (fun z : Radial.Plane × RealModel =>
        a ((extChartAt 𝓘(ℝ,RealModel) b).symm z.2)) q :=
      (ha.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
    have hgc := ((contDiff_apply ℝ ℝ i).comp hg).contDiffAt.comp q
      (hac.prodMk contDiffAt_fst)
    have hw : SmoothOneFormFamily (fun _ : Radial.Plane => weightedFSPrimitive (D i) (m i) c) :=
      (weightedFSPrimitive_smooth (D i) (m i) c).comp (contDiff_const (c := (0:ℝ)))
    have hwc := (hw b).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target b)).mem_nhds hq)
    simpa only [chartOneForm_spatial_smul,Function.comp_apply,Pi.smul_def'] using (hgc.smul hwc).contDiffWithinAt
  refine ⟨Γ,?_,?_⟩
  · convert SmoothOneFormFamily.sum Finset.univ (fun i _ => hterm i) using 1
    funext p x
    simp only [Γ,Finset.sum_apply]
  · have hPU : P ×ˢ C⊆F ⁻¹' U := fun q hq => hKU (mem_image_of_mem F hq)
    filter_upwards [(hU.preimage hF).mem_nhdsSet.mpr hPU] with q hq hqp
    have hge := he (F q) hq (fun i => coefficientNorm_pos _ _ _) hqp
    change (∑ i,g (F q) i • weightedFSPrimitive (D i) (m i) c q.2)=_
    rw [hge]
    rfl

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

omit [Fintype I] in
theorem partitionChartDensity_family_continuous (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω) (i : I) :
    ∃ L : Set Plane,IsCompact L ∧
      Continuous (fun q : P × Plane => partitionChartDensity B ρ (Ω q.1) i q.2) ∧
      ∀ p y,y∉L → partitionChartDensity B ρ (Ω p) i y=0 := by
  let C := tsupport (ρ i)
  have hC : IsCompact C := (B i).isCompact_compactCarrier.of_isClosed_subset
    (isClosed_tsupport _) ((hρ i).trans (B i).carrier_subset_compactCarrier)
  have hCc : C⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source := fun _ hx => (hρ i hx).1
  have hs : SmoothTwoFormFamily (fun p : P => fun x => ρ i x • Ω p x) :=
    hΩ.spatial_smul (ρ i).contMDiff
  have hz : ∀ p x,x∉C→ρ i x • Ω p x=0 := by
    intro _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0 : ℝ) * _ = 0
    exact zero_mul _
  refine ⟨(extChartAt 𝓘(ℝ,Plane) (B i).center) '' C,
    hC.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) (B i).center).mono hCc),?_,?_⟩
  · have hfull := extendedChartCoefficient_smooth (Ω := fun p : P => fun x => ρ i x • Ω p x)
      (c := (B i).center) (hs (B i).center) hC hCc hz
    exact hfull.continuous
  · intro p y hy
    exact extendedChartCoefficient_zero hz p hy

theorem restrictedPartitionFormMass_family_continuous (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (C : Set M)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω) :
    Continuous (fun p => restrictedPartitionFormMass B ρ C (Ω p)) := by
  apply continuous_finsetSum
  intro i _
  obtain ⟨L,hL,hf,hz⟩ := partitionChartDensity_family_continuous B ρ hρ hΩ i
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support hL hf.continuousOn (fun p y _ hy => hz p y hy)

theorem compactSurfaceFormIntegral_family_continuous [T2Space M] [SigmaCompactSpace M]
    {C : Set M} (hC : IsCompact C) {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : SmoothTwoFormFamily Ω) :
    Continuous (fun p => compactSurfaceFormIntegral hC (Ω p)) :=
  restrictedPartitionFormMass_family_continuous _ _ (compactSurfacePartition_subordinate hC) C hΩ

end

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
 theorem manifoldExteriorOneForm_congr_germ {α β : ManifoldOneForm E M} {x : M}
    (h : α =ᶠ[𝓝 x] β) : manifoldExteriorOneForm α x=manifoldExteriorOneForm β x := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have ht := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target x).mem_nhds ht)).continuousAt
  change Filter.Tendsto _ _ (𝓝 ((extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))) at hi
  rw [(extChartAt 𝓘(ℝ,E) x).left_inv hx] at hi
  have he : chartOneForm α x =ᶠ[𝓝 (extChartAt 𝓘(ℝ,E) x x)] chartOneForm β x := by
    filter_upwards [hi.eventually h] with y hy
    exact congrArg (fun L : E →L[ℝ] ℝ => L.comp
      (chartDifferential x ((extChartAt 𝓘(ℝ,E) x).symm y)).inverse) hy
  simp only [manifoldExteriorOneForm,euclideanExteriorOneForm,he.fderiv_eq]

 theorem globalHorizontalCoupling_congr_germ (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ Γ' : V → ManifoldOneForm E M} {z : M × V}
    (h : ∀ᶠ x in 𝓝 z.1,∀ v,Γ v x=Γ' v x) :
    globalHorizontalCoupling Ω Γ z=globalHorizontalCoupling Ω Γ' z := by
  have he : productHorizontalLift Γ =ᶠ[𝓝 z] productHorizontalLift Γ' := by
    filter_upwards [continuousAt_fst.eventually h] with y hy
    exact congrArg (fun L : E →L[ℝ] ℝ => L.comp (ContinuousLinearMap.fst ℝ E V)) (hy y.2)
  exact congrArg (fun B => Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V)
    (ContinuousLinearMap.snd ℝ E V)+B) (manifoldExteriorOneForm_congr_germ he)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

local instance radialFamilySigmaCompact : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

 theorem radial_compact_area_continuousOn {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ)
    {P : Set Radial.Plane} (hP : IsCompact P) (hPS : P⊆Radial.lowerTrapezoid A B)
    {C : Set BaseCurve} (hC : IsCompact C) :
    ContinuousOn (fun p => compactSurfaceFormIntegral hC
      (radialForm Radial.latticeIndex D m c p)) P := by
  obtain ⟨Γ,hΓ,he⟩ := exists_radialPrimitive_smooth_extension hA hAB D m c hP hPS hC
  have hd p (hp : p∈P) x (hx : x∈C) :
      manifoldExteriorOneForm (Γ p) x=radialForm Radial.latticeIndex D m c p x := by
    apply manifoldExteriorOneForm_congr_germ
    have hn := mem_nhdsSet_iff_forall.mp he (p,x) ⟨hp,hx⟩
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hn] with y hy
    exact hy (hPS hp)
  have heq : EqOn (fun p => compactSurfaceFormIntegral hC (manifoldExteriorOneForm (Γ p)))
      (fun p => compactSurfaceFormIntegral hC (radialForm Radial.latticeIndex D m c p)) P :=
    fun p hp => compactSurfaceFormIntegral_congr hC (fun x hx => hd p hp x hx)
  exact (compactSurfaceFormIntegral_family_continuous hC
    (manifoldExteriorOneForm_family_smooth hΓ)).continuousOn.congr heq.symm

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold Filter
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partialChartCoefficient_exterior
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {α : ManifoldOneForm Plane M} (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {y : Plane} (hy : y∈e.source) :
    partialChartCoefficient e (manifoldExteriorOneForm α) y=
      planarCurl (fun z => euclideanPullbackOneForm (fun _ => α) e (0,z)) y := by
  have hs := euclidean_manifold_pullback_exterior_at
    (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hy))
    (by
      have hv := (hα (e y)).contDiffAt
        ((isOpen_univ.prod (isOpen_extChartAt_target (e y))).mem_nhds
          (show (0,extChartAt 𝓘(ℝ,Plane) (e y) (e y))∈(univ : Set ℝ)×ˢ(extChartAt 𝓘(ℝ,Plane) (e y)).target from
            ⟨mem_univ _,mem_extChartAt_target (e y)⟩))
      exact hv.comp _ (contDiffAt_const.prodMk contDiffAt_id))
  change ((manifoldExteriorOneForm α (e y)).bilinearComp
    (manifoldMapDifferential (E := Plane) (F := Plane) e y)
    (manifoldMapDifferential (E := Plane) (F := Plane) e y)) (1,0) (0,1)=_
  exact congrArg (fun L : Plane →L[ℝ] Plane →L[ℝ] ℝ => L (1,0) (0,1)) hs.symm

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem euclideanPullbackOneForm_spatial_smul (ρ : M → ℝ)
    (α : ManifoldOneForm Plane M) (e : Plane → M) (y : Plane) :
    euclideanPullbackOneForm (fun _ => fun x => ρ x • α x) e (0,y)=
      ρ (e y) • euclideanPullbackOneForm (fun _ => α) e (0,y) := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partialChartCoefficient_sub
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (Ω Λ : ManifoldTwoForm Plane M) (y : Plane) :
    partialChartCoefficient e (Ω-Λ) y=partialChartCoefficient e Ω y-partialChartCoefficient e Λ y := rfl

end

def radialAnnulus (r R : ℝ) : Set Plane := {z | r≤radiusSq z ∧ radiusSq z≤R}

theorem radialAnnulus_compact (r R : ℝ) : IsCompact (radialAnnulus r R) := by
  have hc : IsClosed (radialAnnulus r R) :=
    (isClosed_le continuous_const radiusSq_smooth.continuous).inter
      (isClosed_le radiusSq_smooth.continuous continuous_const)
  apply ((isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1))).prod
    (isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1)))).of_isClosed_subset hc
  intro z hz
  have hb : z.1^2+z.2^2≤|R| := hz.2.trans (le_abs_self R)
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2,abs_nonneg R]

theorem radialAnnulus_ne_zero {r R : ℝ} (hr : 0<r) {z : Plane}
    (hz : z∈radialAnnulus r R) : z≠0 := by
  intro h
  subst z
  have : r≤0 := by simpa [radiusSq] using hz.1
  linarith

theorem radialAnnulus_radius_ne_zero {r R : ℝ} (hr : 0<r) {z : Plane}
    (hz : z∈radialAnnulus r R) : radiusSq z≠0 := ne_of_gt (lt_of_lt_of_le hr hz.1)

theorem radiusSq_complex (z : Plane) : Complex.normSq (Complex.equivRealProdCLM.symm z)=radiusSq z := by
  change z.1*z.1+z.2*z.2=z.1^2+z.2^2
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

 def reducedEndProbability (w : ι → MomentPlane) (D m : ι → ℕ) (p : MomentPlane)
    (ε : EndIndex) (y : Plane) (i : ι) : ℝ :=
  reducedProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i

 def reducedEndRegularPrimitive (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ) (p : MomentPlane)
    (ε : EndIndex) (y : Plane) : Plane →L[ℝ] ℝ :=
  ∑ i,reducedEndProbability w D m p ε y i • weightedRegularEndPrimitive (D i) (m i) ε c y

 def reducedEndResidue (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ) (p : MomentPlane)
    (ε : EndIndex) (y : Plane) : ℝ :=
  ∑ i,reducedEndProbability w D m p ε y i*weightedEndResidue (D i) (m i) ε c

 theorem reducedPrimitive_infinity (w : ι → MomentPlane) {D m : ι → ℕ}
    (hm : ∀ i,m i≤D i) (h2 : ∀ i,m i≤2*(D i-m i)) (c : ℝ) (p : MomentPlane)
    (ε : EndIndex) {y : Plane} (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    euclideanPullbackOneForm (fun _ => reducedPrimitive w D m c p)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      reducedEndRegularPrimitive w D m c p ε y-(reducedEndResidue w D m c p ε y/2) • angularOneForm y := by
  have he : euclideanPullbackOneForm (fun _ => reducedPrimitive w D m c p)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      ∑ i,reducedEndProbability w D m p ε y i •
        euclideanPullbackOneForm (fun _ => weightedFSPrimitive (D i) (m i) c)
          (infinityDiffeomorph (parameters 0) ε) (0,y) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sum_apply, smul_apply, smul_eq_mul, reducedEndProbability]
    let A : Plane →L[ℝ] RealModel :=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,RealModel) (infinityDiffeomorph (parameters 0) ε) y
    let z : RealModel := A v
    change (∑ i,reducedProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i •
        weightedFSPrimitive (D i) (m i) c (infinityDiffeomorph (parameters 0) ε y)) z =
      ∑ i,reducedProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i *
        weightedFSPrimitive (D i) (m i) c (infinityDiffeomorph (parameters 0) ε y) z
    simp only [sum_apply,smul_apply,smul_eq_mul]
  rw [he]
  simp_rw [weightedFSPrimitive_infinity (hm _) (h2 _) ε c hy hR]
  apply ContinuousLinearMap.ext
  intro v
  simp only [reducedEndRegularPrimitive,reducedEndResidue,sum_apply,
    sub_apply,smul_apply,smul_eq_mul,Finset.sum_mul,Finset.sum_div,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 def regularCoefficientNorm (D m : ℕ) (ε : EndIndex) (y : Plane) : ℝ :=
  phaseSq (weightedRegularEndPhase D m ε y)

 theorem regularCoefficientNorm_pos (D m : ℕ) (ε : EndIndex) (y : Plane) :
    0<regularCoefficientNorm D m ε y := phaseSq_pos (weightedEndRegular_cartesian_ne_zero D m ε _)

 theorem regularCoefficientNorm_contDiffAt (D m : ℕ) (ε : EndIndex) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (regularCoefficientNorm D m ε) y :=
  phaseSq_smooth.contDiffAt.comp y (weightedRegularEndPhase_contDiffAt D m ε hy)

 theorem coefficientNorm_regularization {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) {y : Plane} (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    regularCoefficientNorm D m ε y=(radiusSq y)^(weightedEndOrder D m ε)*
      coefficientNorm D m (infinityDiffeomorph (parameters 0) ε y) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  dsimp [regularCoefficientNorm,weightedRegularEndPhase]
  rw [weightedEndRegular_scale hm h2 ε hD.1 hR,complexCartesian_complex_smul_sq,map_pow,
    complexAffineLift_sq,radiusSq_complex]
  congr 2
  exact congrArg phaseSq (weighted_infinityPhase_germ D m ε hy).eq_of_nhds.symm

 theorem coefficientNorm_eq_regular_div {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) {y : Plane} (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    coefficientNorm D m (infinityDiffeomorph (parameters 0) ε y)=
      regularCoefficientNorm D m ε y/(radiusSq y)^(weightedEndOrder D m ε) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hz : radiusSq y≠0 := by
    rw [←radiusSq_complex]
    exact (Complex.normSq_pos.mpr hD.1).ne'
  rw [coefficientNorm_regularization hm h2 ε hy hR,mul_div_cancel_left₀ _ (pow_ne_zero _ hz)]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Set

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem selected_div_power {w : ι → E} {a m : ι → ℝ} {n : ι → ℕ}
    (ha : ∀ i,0<a i) {t : ℝ} (ht : 0<t) {D : ℝ} {h : E}
    (hn : ∀ i,(n i:ℝ)=D-inner ℝ (w i) h-m i) {p : E} (hp : Surrounds w p) (i : ι) :
    selected w (fun j => a j/t^(n j)) p i=
      selected w (fun j => a j*Real.exp (Real.log t*m j)) p i := by
  have he : (fun j => a j/t^(n j))=(fun j => Real.exp (-D*Real.log t)*
      (a j*Real.exp (Real.log t*m j))*Real.exp (inner ℝ (w j) (Real.log t • h))) := by
    funext j
    rw [inner_smul_right]
    have hpow : t^(n j)=Real.exp ((n j:ℝ)*Real.log t) := by
      rw [Real.exp_nat_mul,Real.exp_log ht]
    rw [hpow,div_eq_mul_inv,←Real.exp_neg]
    have he : a j*Real.exp (-((n j:ℝ)*Real.log t))=
        a j*Real.exp ((-D*Real.log t)+(Real.log t*m j)+Real.log t*inner ℝ (w j) h) := by
      rw [hn j]
      congr 2
      ring
    rw [he,Real.exp_add,Real.exp_add]
    ring
  rw [he]
  exact selected_gauge (fun j => mul_pos (ha j) (Real.exp_pos _)) (Real.exp_pos _) hp _ i

 theorem selected_marked_error {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A≤B) (hSB : S≤B) {a : TrapezoidWeight A B → ℝ} {n : TrapezoidWeight A B → ℕ}
    {M t D C : ℝ} (ha : ∀ k,0<a k) (hloga : ∀ k,|Real.log (a k)|≤M)
    (ht : 0<t) (ht1 : t<1)
    (hn : ∀ k,(n k:ℝ)=D-C*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
      markedHeight S (trapezoidWeight A B k)) {p : MomentPlane} (hp : p∈openTrapezoid A B) :
    |(∑ k,selected (trapezoidWeight A B) (fun j => a j/t^(n j)) p k*(n k:ℝ))-
      (D-C*(p 0+p 1)-markedHeight S p)|≤
      (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log t) := by
  have hs := trapezoidWeight_surrounds hAB hp
  have hg (k : TrapezoidWeight A B) :
      selected (trapezoidWeight A B) (fun j => a j/t^(n j)) p k=
      selected (trapezoidWeight A B)
        (fun j => a j*Real.exp (Real.log t*markedHeight S (trapezoidWeight A B j))) p k := by
    apply selected_div_power ha ht (D := D) (h := planeVector C C) _ hs
    intro j
    rw [hn j]
    congr 1
    simp [PiLp.inner_apply,Fin.sum_univ_succ,planeVector]
    ring
  let b := fun j => a j*Real.exp (Real.log t*markedHeight S (trapezoidWeight A B j))
  have hb (j : TrapezoidWeight A B) : 0<b j := mul_pos (ha j) (Real.exp_pos _)
  have hbound := marked_gibbs_error hA hS hAB hSB ha hloga (Real.log_neg ht ht1)
    (inverse (trapezoidWeight A B) b p)
    (show p∈closedTrapezoid A B from ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩)
    (inverse_spec hb hs)
  simp_rw [hg,hn]
  rw [probability_affine_height (selected_sum hb p) (selected_mean hb hs)]
  have he : D-C*(p 0+p 1)-(∑ i,selected (trapezoidWeight A B) b p i*
      markedHeight S (trapezoidWeight A B i))-(D-C*(p 0+p 1)-markedHeight S p)=
      -((∑ i,selected (trapezoidWeight A B) b p i*markedHeight S (trapezoidWeight A B i))-
      markedHeight S p) := by ring
  change |D-C*(p 0+p 1)-(∑ i,selected (trapezoidWeight A B) b p i*
      markedHeight S (trapezoidWeight A B i))-(D-C*(p 0+p 1)-markedHeight S p)|≤_
  rw [he,abs_neg]
  change |(∑ i,gibbs (trapezoidWeight A B) b (inverse (trapezoidWeight A B) b p) i*
      markedHeight S (trapezoidWeight A B i))-markedHeight S p|≤_
  rw [abs_of_nonneg hbound.1]
  exact hbound.2

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

 def totalWeight {A B : ℕ} (k : TrapezoidWeight A B) : ℕ := k.val.1.val+k.val.2.val
 def cubicDegree {A B : ℕ} (D : ℕ) (k : TrapezoidWeight A B) : ℕ := D-3*totalWeight k
 def cubicMarkedOrder {A B : ℕ} (S : ℕ) (k : TrapezoidWeight A B) : ℕ := S-totalWeight k

 theorem totalWeight_le {A B : ℕ} (k : TrapezoidWeight A B) : totalWeight k≤B := k.property.2

 theorem cubicMarked_lt_degree {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (k : TrapezoidWeight A B) : cubicMarkedOrder S k<cubicDegree D k := by
  have hk := totalWeight_le k
  dsimp [cubicMarkedOrder,cubicDegree]
  omega

 theorem cubicMarked_twice_complement {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (k : TrapezoidWeight A B) : cubicMarkedOrder S k≤2*(cubicDegree D k-cubicMarkedOrder S k) := by
  have hk := totalWeight_le k
  dsimp [cubicMarkedOrder,cubicDegree]
  omega

 theorem totalWeight_cast {A B : ℕ} (k : TrapezoidWeight A B) :
    (totalWeight k:ℝ)=(trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1 := by
  simp [totalWeight,trapezoidWeight,planeVector]

 theorem cubicDegree_cast {A B D : ℕ} (hB : 3*B≤D) (k : TrapezoidWeight A B) :
    (cubicDegree D k:ℝ)=(D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1) := by
  rw [cubicDegree,Nat.cast_sub (by have hk := totalWeight_le k; omega),Nat.cast_mul,Nat.cast_ofNat,totalWeight_cast]

 theorem cubicMarkedOrder_cast {A B : ℕ} (S : ℕ) (k : TrapezoidWeight A B) :
    (cubicMarkedOrder S k:ℝ)=markedHeight S (trapezoidWeight A B k) := by
  unfold cubicMarkedOrder markedHeight
  by_cases hk : totalWeight k≤S
  · rw [Nat.cast_sub hk,totalWeight_cast]
    have hh : (totalWeight k:ℝ)≤S := by exact_mod_cast hk
    rw [totalWeight_cast] at hh
    rw [max_eq_left (by linarith)]
    ring
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hk),Nat.cast_zero,max_eq_right]
    have hh : (S:ℝ)≤totalWeight k := by exact_mod_cast (le_of_not_ge hk)
    rw [totalWeight_cast] at hh
    linarith

 theorem cubicEndOrder_cast {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (ε : EndIndex) (k : TrapezoidWeight A B) :
    (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)=
      if ε 0 then (if ε 1 then (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)
        else (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
          markedHeight S (trapezoidWeight A B k))
      else (if ε 1 then (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
          markedHeight S (trapezoidWeight A B k) else 0) := by
  cases h0 : ε 0 <;> cases h1 : ε 1 <;>
    simp only [weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,Nat.cast_zero,
      Nat.cast_sub (cubicMarked_lt_degree hB hS k).le,cubicDegree_cast hB.le,cubicMarkedOrder_cast]

variable {ι : Type*} [Fintype ι]

 def radialEndProbability (w : ι → ℕ × ℕ) (D m : ι → ℕ) (p : Radial.Plane)
    (ε : EndIndex) (y : Plane) (i : ι) : ℝ :=
  radialProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i

 def radialEndRegularPrimitive (w : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane)
    (ε : EndIndex) (y : Plane) : Plane →L[ℝ] ℝ :=
  ∑ i,radialEndProbability w D m p ε y i • weightedRegularEndPrimitive (D i) (m i) ε c y

 def radialEndResidue (w : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane)
    (ε : EndIndex) (y : Plane) : ℝ :=
  ∑ i,radialEndProbability w D m p ε y i*weightedEndResidue (D i) (m i) ε c

 theorem radialPrimitive_infinity (w : ι → ℕ × ℕ) {D m : ι → ℕ}
    (hm : ∀ i,m i≤D i) (h2 : ∀ i,m i≤2*(D i-m i)) (c : ℝ) (p : Radial.Plane)
    (ε : EndIndex) {y : Plane} (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    euclideanPullbackOneForm (fun _ => radialPrimitive w D m c p)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      radialEndRegularPrimitive w D m c p ε y-(radialEndResidue w D m c p ε y/2) • angularOneForm y := by
  have he : euclideanPullbackOneForm (fun _ => radialPrimitive w D m c p)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      ∑ i,radialEndProbability w D m p ε y i •
        euclideanPullbackOneForm (fun _ => weightedFSPrimitive (D i) (m i) c)
          (infinityDiffeomorph (parameters 0) ε) (0,y) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sum_apply, smul_apply, smul_eq_mul, radialEndProbability]
    let A : Plane →L[ℝ] RealModel :=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,RealModel) (infinityDiffeomorph (parameters 0) ε) y
    let z : RealModel := A v
    change (∑ i,radialProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i •
        weightedFSPrimitive (D i) (m i) c (infinityDiffeomorph (parameters 0) ε y)) z =
      ∑ i,radialProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i *
        weightedFSPrimitive (D i) (m i) c (infinityDiffeomorph (parameters 0) ε y) z
    simp only [sum_apply,smul_apply,smul_eq_mul]
  rw [he]
  simp_rw [weightedFSPrimitive_infinity (hm _) (h2 _) ε c hy hR]
  apply ContinuousLinearMap.ext
  intro v
  simp only [radialEndRegularPrimitive,radialEndResidue,sum_apply,
    sub_apply,smul_apply,smul_eq_mul,Finset.sum_mul,Finset.sum_div,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PackingSufficiencySupport.CubicModel
end

end OAI
