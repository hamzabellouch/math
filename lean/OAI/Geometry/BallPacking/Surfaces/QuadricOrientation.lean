import Mathlib
import OAI.Geometry.BallPacking.Surfaces.QuadricCurveManifold
import OAI.Geometry.BallPacking.Forms.ChartSupportedDensity

namespace OAI

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold
namespace PackingSufficiencySupport.DiagonalQuadrics
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

theorem real_transition_positive (b c : locus a) {y : RealModel}
    (hy : y∈((realChart a b).symm.trans (realChart a c)).source) :
    0<(fderiv ℝ ((realChart a b).symm.trans (realChart a c)) y).det := by
  let e := ((normalChartAt a b).sliceChart b).symm.trans ((normalChartAt a c).sliceChart c)
  have hye : Complex.equivRealProdCLM.symm y∈e.source := ⟨hy.1.2,hy.2.1⟩
  have hf := ((normalChartAt a b).transition_smooth b (normalChartAt a c) c).contDiffAt
    (e.open_source.mem_nhds hye)
  have hg := ((normalChartAt a c).transition_smooth c (normalChartAt a b) b).contDiffAt
    (e.symm.open_source.mem_nhds (e.map_source hye))
  exact holomorphic_partialHomeomorph_orientation e hye
    (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))

theorem positivePlaneTransitions : Hamiltonian.PositivePlaneTransitions (locus a) := by
  intro b c y hy hc
  have hbchart : chartAt Hamiltonian.Plane b=realChart a b := rfl
  have hcchart : chartAt Hamiltonian.Plane c=realChart a c := rfl
  have hb : y∈(realChart a b).target := by simpa only [mfld_simps,hbchart] using hy
  have hc' : (realChart a b).symm y∈(realChart a c).source := by simpa only [mfld_simps,hbchart,hcchart] using hc
  have h := real_transition_positive a b c ⟨hb,hc'⟩
  simpa only [mfld_simps,hbchart,hcchart] using h

end PackingSufficiencySupport.DiagonalQuadrics

end

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def partialChartCoefficient
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (Ω : ManifoldTwoForm Plane M) (y : Plane) : ℝ :=
  euclideanPullbackTwoForm (fun _ => Ω) e (0,y) (1,0) (0,1)

theorem partialChartCoefficient_contDiffOn
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) :
    ContDiffOn ℝ ∞ (partialChartCoefficient e Ω) e.source := by
  intro y hy
  have hs := euclideanPullbackTwoForm_contDiffAt (E := Plane) (F := Plane) (M := M)
    (Ω := fun _ : ℝ => Ω) (g := e) (p := ((0:ℝ),y))
    (SmoothTwoFormFamily.const (P := ℝ) hΩ)
    (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hy))
  exact (((hs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

theorem partialChartCoefficient_change
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : ∀ x u v,Ω x u v= -Ω x v u)
    {c : M} {y : Plane} (hy : y∈e.source)
    (hc : e y∈(extChartAt 𝓘(ℝ,Plane) c).source) :
    partialChartCoefficient e Ω y=
      (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det *
        chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c (e y)) (1,0) (0,1) := by
  unfold partialChartCoefficient
  rw [euclideanPullbackTwoForm_chart (e.mdifferentiableAt (by simp) hy) hc,
    ContinuousLinearMap.bilinearComp_apply,
    planar_skew_coefficient _ (chartTwoForm_skew hΩ _ _),← planar_det,mul_comm]

theorem partialChart_area_integral_change
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : ∀ x u v,Ω x u v= -Ω x v u)
    {c : M} {K : Set M} (hK : IsCompact K) (hKe : K⊆e.target)
    (hKc : K⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    (hpos : ∀ y∈e.symm '' K,
      0<(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det) :
    (∫ y in e.symm '' K,partialChartCoefficient e Ω y)=
      ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K,chartTwoForm Ω c y (1,0) (0,1) := by
  let g : Plane → Plane := extChartAt 𝓘(ℝ,Plane) c ∘ e
  have hys {y : Plane} (hy : y∈e.symm '' K) : y∈e.source := by
    obtain ⟨x,hx,rfl⟩ := hy
    exact e.map_target (hKe hx)
  have hyK {y : Plane} (hy : y∈e.symm '' K) : e y∈K := by
    obtain ⟨x,hx,rfl⟩ := hy
    have heq : e (e.symm x)=x := e.right_inv (hKe hx)
    rwa [heq]
  have hgs : ∀ y∈e.symm '' K,ContDiffAt ℝ ∞ g y := by
    intro y hy
    have hi := e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hys hy))
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hKc (hyK hy))
    exact (ho.comp y hi).contDiffAt
  have hgi : InjOn g (e.symm '' K) := by
    intro y hy z hz heq
    exact e.injOn (hys hy) (hys hz)
      ((extChartAt 𝓘(ℝ,Plane) c).injOn (hKc (hyK hy)) (hKc (hyK hz)) heq)
  have him : g '' (e.symm '' K)=extChartAt 𝓘(ℝ,Plane) c '' K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨e z,hyK hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨e.symm x,⟨x,hx,rfl⟩,congrArg (extChartAt 𝓘(ℝ,Plane) c) (e.right_inv (hKe hx))⟩
  have hmeas : MeasurableSet (e.symm '' K) :=
    (hK.image_of_continuousOn (e.symm.contMDiffOn.continuousOn.mono hKe)).measurableSet
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume hmeas
    (f' := fderiv ℝ g)
    (fun y hy => ((hgs y hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    hgi (fun y => chartTwoForm Ω c y (1,0) (0,1))
  rw [him] at hi
  rw [hi]
  apply setIntegral_congr_fun hmeas
  intro y hy
  change partialChartCoefficient e Ω y=|(fderiv ℝ g y).det| •
    chartTwoForm Ω c (g y) (1,0) (0,1)
  rw [partialChartCoefficient_change e hΩ (hys hy) (hKc (hyK hy)),
    abs_of_pos (hpos y hy)]
  rfl

theorem chartMass_eq_partialChart_integral
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    {Ω : ManifoldTwoForm Plane M} (hΩ : ∀ x u v,Ω x u v= -Ω x v u)
    {c : M} {K : Set M} (hK : IsCompact K) (hKe : K⊆e.target)
    (hKc : K⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x,x∉K→Ω x=0)
    (hpos : ∀ y∈e.symm '' K,
      0<(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det) :
    chartMass c Ω=∫ y in e.symm '' K,partialChartCoefficient e Ω y := by
  rw [chartMass_eq_setIntegral hK hKc hz]
  exact (partialChart_area_integral_change e hΩ hK hKe hKc hpos).symm

end PackingSufficiencySupport.Hamiltonian


namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

theorem surface_box_primitive {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : SmoothTwoFormFamily Ω) (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u)
    (B : SurfaceCoordinateBox M) {K : Set M} (hK : IsCompact K)
    (hKB : K ⊆ B.carrier) (hz : ∀ p x, x ∉ K → Ω p x=0)
    (hmass : ∀ p, chartMass B.center (Ω p)=0) : HasCompactPrimitiveFamily Ω := by
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
  obtain ⟨α,hα,hα0,hαd,_⟩ := chart_supported_area_primitive B.radius_pos B.point B.center
    B.closed_subset hf hzero hmass
  refine ⟨B.compactCarrier,B.isCompact_compactCarrier,α,hα,hα0,?_⟩
  intro p c y hy
  rw [hαd p c y hy]
  have he := chartSupported_extendedCoefficient hskew hKc hz p
  change chartTwoForm (chartSupportedTwoForm B.center (fun z => extendedChartCoefficient B.center Ω (p,z) • planarArea)) c y = _
  rw [he]

end PackingSufficiencySupport.Hamiltonian

end

section

open Set
namespace PackingSufficiencySupport.Hamiltonian

theorem connected_cover_overlap_chain {X I : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {U : I → Set X} (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {i j : I}
    (hi : (U i).Nonempty) (hj : (U j).Nonempty) :
    Relation.ReflTransGen (fun a b => (U a ∩ U b).Nonempty) i j := by
  let R : I → Prop := fun b =>
    Relation.ReflTransGen (fun a b => (U a ∩ U b).Nonempty) i b
  let S : Set X := ⋃ b, ⋃ (_ : R b), U b
  have hS : IsOpen S := isOpen_iUnion fun b => isOpen_iUnion fun _ => hU b
  have hd : Sᶜ = ⋃ b, ⋃ (_ : ¬R b), U b := by
    ext x
    constructor
    · intro hx
      obtain ⟨b,hb⟩ := hcover x
      have hr : ¬R b := by
        intro hr
        exact hx (mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hr,hb⟩⟩)
      exact mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hr,hb⟩⟩
    · intro hx hy
      obtain ⟨b,hb,hxb⟩ := mem_iUnion₂.mp hx
      obtain ⟨c,hc,hxc⟩ := mem_iUnion₂.mp hy
      exact hb (hc.tail ⟨x,hxc,hxb⟩)
  have hSc : IsOpen Sᶜ := by rw [hd]; exact isOpen_iUnion fun b => isOpen_iUnion fun _ => hU b
  have hne : S.Nonempty := by
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,mem_iUnion₂.mpr ⟨i,Relation.ReflTransGen.refl,hx⟩⟩
  have hall : S = univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hSc,hS⟩).eq_univ hne
  obtain ⟨x,hx⟩ := hj
  have hxS : x ∈ S := by rw [hall]; exact mem_univ _
  obtain ⟨b,hb,hxb⟩ := mem_iUnion₂.mp hxS
  exact hb.tail ⟨x,hxb,hx⟩

end PackingSufficiencySupport.Hamiltonian

end

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem SmoothTwoForm.coefficient_integrable {Ω : ManifoldTwoForm Plane M}
    (hΩ : SmoothTwoForm Ω) (c : M) {K : Set M} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0) :
    Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)) :=
  chartCoefficient_integrable (P := ℝ) (M := M) (c := c) (Ω := fun _ : ℝ => Ω)
    (SmoothTwoFormFamily.const (P := ℝ) (M := M) hΩ c) (K := K) hK hKc
    (fun _ x hx => hz x hx) 0

theorem surface_box_difference (B : SurfaceCoordinateBox M)
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hsΩ : ∀ x u v, Ω x u v = -Ω x v u) (hsΛ : ∀ x u v, Λ x u v = -Λ x v u)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKB : K ⊆ B.carrier) (hLB : L ⊆ B.carrier)
    (hzΩ : ∀ x, x ∉ K → Ω x=0) (hzΛ : ∀ x, x ∉ L → Λ x=0)
    (hm : chartMass B.center Ω=chartMass B.center Λ) :
    HasCompactPrimitiveFamily (fun _ : P => Ω-Λ) := by
  apply surface_box_primitive
    ((SmoothTwoFormFamily.const hΩ).sub (SmoothTwoFormFamily.const hΛ))
    (fun _ x u v => by
      change Ω x u v - Λ x u v = -(Ω x v u - Λ x v u)
      rw [hsΩ x u v,hsΛ x u v]; ring)
    B (hK.union hL) (union_subset hKB hLB)
  · intro _ x hx
    change Ω x-Λ x=0
    rw [hzΩ x (fun hk => hx (Or.inl hk)),hzΛ x (fun hl => hx (Or.inr hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ)-0=0
    exact sub_self 0
  · intro _
    change chartMass B.center (Ω-Λ)=0
    rw [chartMass_sub (hΩ.coefficient_integrable B.center hK (fun x hx => (hKB hx).1) hzΩ)
      (hΛ.coefficient_integrable B.center hL (fun x hx => (hLB hx).1) hzΛ),hm,sub_self]

theorem surface_overlap_bump_difference (hpos : PositivePlaneTransitions M)
    {B C : SurfaceCoordinateBox M} (β : BoxUnitBump B) (γ : BoxUnitBump C)
    (hBC : (B.carrier ∩ C.carrier).Nonempty) :
    HasCompactPrimitiveFamily (fun _ : P => β.form-γ.form) := by
  obtain ⟨x,hx⟩ := hBC
  obtain ⟨D,_,hD⟩ := SurfaceCoordinateBox.exists_compactCarrier_subset
    (B.isOpen_carrier.inter C.isOpen_carrier) hx
  obtain ⟨δ⟩ := D.exists_unit_bump
  have hδB : δ.supportSet ⊆ B.carrier :=
    δ.support_subset.trans (D.carrier_subset_compactCarrier.trans (hD.trans inter_subset_left))
  have hδC : δ.supportSet ⊆ C.carrier :=
    δ.support_subset.trans (D.carrier_subset_compactCarrier.trans (hD.trans inter_subset_right))
  have h1 : HasCompactPrimitiveFamily (fun _ : P => β.form-δ.form) :=
    surface_box_difference B β.smooth δ.smooth β.skew δ.skew β.compact_supportSet
      δ.compact_supportSet β.support_subset hδB β.zero_off δ.zero_off
      (β.unit_mass.trans (δ.mass_in_chart hpos B.center (fun z hz => (hδB hz).1)).symm)
  have h2 : HasCompactPrimitiveFamily (fun _ : P => δ.form-γ.form) :=
    surface_box_difference C δ.smooth γ.smooth δ.skew γ.skew δ.compact_supportSet
      γ.compact_supportSet hδC γ.support_subset δ.zero_off γ.zero_off
      ((δ.mass_in_chart hpos C.center (fun z hz => (hδC hz).1)).trans γ.unit_mass.symm)
  have he : (fun _ : P => β.form-δ.form)+(fun _ : P => δ.form-γ.form) =
      (fun _ : P => β.form-γ.form) := by
    funext p; simp only [Pi.add_apply]; abel
  exact he ▸ h1.add h2

theorem surface_bump_difference [PreconnectedSpace M] (hpos : PositivePlaneTransitions M)
    {B C : SurfaceCoordinateBox M} (β : BoxUnitBump B) (γ : BoxUnitBump C) :
    HasCompactPrimitiveFamily (fun _ : P => β.form-γ.form) := by
  have hc := connected_cover_overlap_chain SurfaceCoordinateBox.isOpen_carrier
    SurfaceCoordinateBox.exists_mem B.nonempty_carrier C.nonempty_carrier
  revert γ
  induction hc with
  | refl =>
    intro γ
    exact surface_box_difference B β.smooth γ.smooth β.skew γ.skew β.compact_supportSet
      γ.compact_supportSet β.support_subset γ.support_subset β.zero_off γ.zero_off
      (β.unit_mass.trans γ.unit_mass.symm)
  | @tail C D hc hCD ih =>
    intro γ
    obtain ⟨δ⟩ := C.exists_unit_bump
    have h1 := ih δ
    have h2 : HasCompactPrimitiveFamily (fun _ : P => δ.form-γ.form) :=
      surface_overlap_bump_difference hpos δ γ hCD
    have he : (fun _ : P => β.form-δ.form)+(fun _ : P => δ.form-γ.form) =
        (fun _ : P => β.form-γ.form) := by
      funext p; simp only [Pi.add_apply]; abel
    exact he ▸ h1.add h2

end PackingSufficiencySupport.Hamiltonian



namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

def partitionTwoForm (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Ω : P → ManifoldTwoForm Plane M) (i : I) (p : P) : ManifoldTwoForm Plane M :=
  fun x => ρ i x • Ω p x

omit [Fintype I] in
theorem partitionTwoForm_smooth (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω) (i : I) :
    SmoothTwoFormFamily (partitionTwoForm ρ Ω i) :=
  hΩ.spatial_smul (ρ i).contMDiff

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] [Fintype I] in
theorem partitionTwoForm_skew (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : ∀ p x u v, Ω p x u v = -Ω p x v u)
    (i : I) (p : P) (x : M) (u v : Plane) :
    partitionTwoForm ρ Ω i p x u v = -partitionTwoForm ρ Ω i p x v u := by
  change ρ i x * Ω p x u v = -(ρ i x * Ω p x v u)
  rw [hΩ p x u v,mul_neg]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] [Fintype I] in
theorem partitionTwoForm_zero (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hz : ∀ p x, x ∉ K → Ω p x=0)
    (i : I) (p : P) (x : M) (hx : x ∉ K ∩ tsupport (ρ i)) :
    partitionTwoForm ρ Ω i p x=0 := by
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  by_cases hk : x ∈ K
  · have hρ : ρ i x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hx ⟨hk,ht⟩)
    change ρ i x • Ω p x=0
    rw [hρ,zero_smul]
  · change ρ i x • Ω p x=0
    rw [hz p x hk,MulActionWithZero.smul_zero]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partitionTwoForm_sum (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hz : ∀ p x, x ∉ K → Ω p x=0) :
    ∑ i, partitionTwoForm ρ Ω i = Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  funext p x
  simp only [Finset.sum_apply,partitionTwoForm]
  rw [← Finset.sum_smul]
  by_cases hx : x ∈ K
  · have hs : (∑ i, ρ i x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    rw [hs,one_smul]
  · rw [hz p x hx,MulActionWithZero.smul_zero]

end PackingSufficiencySupport.Hamiltonian



namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  {I : Type*} [Fintype I] {K : Set M}

def partitionFormMass (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (Ω : ManifoldTwoForm Plane M) : ℝ :=
  ∑ i, chartMass (B i).center (fun x => ρ i x • Ω x)

theorem surface_partition_primitive (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u)
    (hz : ∀ p x, x ∉ K → Ω p x=0)
    (hmass : ∀ p, partitionFormMass B ρ (Ω p)=0)
    (B₀ : SurfaceCoordinateBox M) : HasCompactPrimitiveFamily Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let β (i : I) : BoxUnitBump (B i) := Classical.choice (B i).exists_unit_bump
  obtain ⟨β₀⟩ := B₀.exists_unit_bump
  let Ωi := partitionTwoForm ρ Ω
  let Ki : I → Set M := fun i => K ∩ tsupport (ρ i)
  have hKi (i : I) : IsCompact (Ki i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hKiB (i : I) : Ki i ⊆ (B i).carrier := fun _ hx => hρ i hx.2
  have hΩi (i : I) : SmoothTwoFormFamily (Ωi i) := partitionTwoForm_smooth ρ hΩ i
  have hzΩi (i : I) : ∀ p x, x ∉ Ki i → Ωi i p x=0 := partitionTwoForm_zero ρ hz i
  have hsΩi (i : I) : ∀ p x u v, Ωi i p x u v = -Ωi i p x v u :=
    partitionTwoForm_skew ρ hskew i
  let m : I → P → ℝ := fun i p => chartMass (B i).center (Ωi i p)
  have hm (i : I) : ContDiff ℝ ∞ (m i) :=
    chartMass_smooth (hΩi i (B i).center) (hKi i) (fun x hx => (hKiB i hx).1) (hzΩi i)
  have hlocal (i : I) : HasCompactPrimitiveFamily (fun p => Ωi i p-m i p • (β i).form) := by
    have hscaled : SmoothTwoFormFamily (fun p => m i p • (β i).form) :=
      (SmoothTwoFormFamily.const (β i).smooth).smul (hm i)
    have hdif : SmoothTwoFormFamily (fun p => Ωi i p-m i p • (β i).form) :=
      (hΩi i).sub hscaled
    apply surface_box_primitive hdif (fun p x u v => by
      change Ωi i p x u v - m i p * (β i).form x u v =
        -(Ωi i p x v u - m i p * (β i).form x v u)
      rw [hsΩi i p x u v,(β i).skew x u v]; ring)
      (B i) ((hKi i).union (β i).compact_supportSet)
      (union_subset (hKiB i) (β i).support_subset)
    · intro p x hx
      change Ωi i p x - m i p • (β i).form x=0
      rw [hzΩi i p x (fun hk => hx (Or.inl hk)),
        (β i).zero_off x (fun hk => hx (Or.inr hk)),MulActionWithZero.smul_zero]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change (0:ℝ)-0=0
      exact sub_self 0
    · intro p
      have h1 := (hΩi i).eval p |>.coefficient_integrable (B i).center (hKi i)
        (fun x hx => (hKiB i hx).1) (hzΩi i p)
      have h2 := hscaled.eval p |>.coefficient_integrable (B i).center (β i).compact_supportSet
        (fun x hx => ((β i).support_subset hx).1)
        (fun x hx => by change m i p • (β i).form x=0; rw [(β i).zero_off x hx,MulActionWithZero.smul_zero])
      rw [chartMass_sub h1 h2,chartMass_smul,(β i).unit_mass,mul_one]
      exact sub_self _
  have hcommon (i : I) : HasCompactPrimitiveFamily (fun p => Ωi i p-m i p • β₀.form) := by
    have ht := (surface_bump_difference (P := P) hpos (β i) β₀).smul (hm i)
    have he : (fun p => Ωi i p-m i p • (β i).form)+
        (fun p => m i p • ((β i).form-β₀.form)) =
          (fun p => Ωi i p-m i p • β₀.form) := by
      funext p x
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change Ωi i p x u v - m i p * (β i).form x u v +
        m i p * ((β i).form x u v - β₀.form x u v) =
          Ωi i p x u v - m i p * β₀.form x u v
      ring
    exact he ▸ (hlocal i).add ht
  have hall := HasCompactPrimitiveFamily.sum Finset.univ (fun i _ => hcommon i)
  have he : (∑ i, fun p => Ωi i p-m i p • β₀.form)=Ω := by
    funext p x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [Finset.sum_apply,sum_apply,Pi.sub_apply,Pi.smul_apply,
      sub_apply,smul_apply,smul_eq_mul]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul]
    have hm0 : (∑ i, m i p)=0 := hmass p
    rw [hm0,zero_mul,sub_zero]
    have hh := congrArg (fun F : P → ManifoldTwoForm Plane M => F p x u v)
      (partitionTwoForm_sum ρ hz)
    simpa only [Finset.sum_apply,sum_apply] using hh
  exact he ▸ hall

end PackingSufficiencySupport.Hamiltonian



namespace PackingSufficiencySupport.Hamiltonian
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def PositivePartialChart
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞) : Prop :=
  ∀ c y,y∈e.source→e y∈(extChartAt 𝓘(ℝ,Plane) c).source→
    0<(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ e) y).det

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
@[simp] theorem partialChartCoefficient_smul
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (f : M → ℝ) (Ω : ManifoldTwoForm Plane M) (y : Plane) :
    partialChartCoefficient e (fun x => f x • Ω x) y=f (e y)*partialChartCoefficient e Ω y := rfl

theorem partitionFormMass_eq_partialChart_integral
    {I : Type*} [Fintype I] {K : Set M}
    (e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞)
    (hpos : PositivePartialChart e) (hK : IsCompact K) (hKe : K⊆e.target)
    (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉K→Ω x=0) :
    partitionFormMass B ρ Ω=∫ y in e.symm '' K,partialChartCoefficient e Ω y := by
  classical
  let D : I → ManifoldTwoForm Plane M := fun i x => ρ i x • Ω x
  let L : I → Set M := fun i => K∩tsupport (ρ i)
  have hL (i : I) : IsCompact (L i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hLB (i : I) : L i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hLe (i : I) : L i⊆e.target := fun _ hx => hKe hx.1
  have hDs (i : I) : SmoothTwoForm (D i) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0
  have hDa (i : I) (x : M) (u v : Plane) : D i x u v= -D i x v u := by
    change ρ i x * Ω x u v= -(ρ i x * Ω x v u)
    rw [ha x u v,mul_neg]
  have hDz (i : I) (x : M) (hx : x∉L i) : D i x=0 := by
    by_cases hk : x∈K
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
  have hS : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.symm.contMDiffOn.continuousOn.mono hKe)
  have hse : e.symm '' K⊆e.source := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_target (hKe hx)
  have hI (i : I) : IntegrableOn (partialChartCoefficient e (D i)) (e.symm '' K) :=
    ((partialChartCoefficient_contDiffOn e (hDs i)).continuousOn.mono hse).integrableOn_compact hS
  have hmass (i : I) : chartMass (B i).center (D i)=
      ∫ y in e.symm '' K,partialChartCoefficient e (D i) y := by
    rw [chartMass_eq_partialChart_integral e (hDa i) (hL i) (hLe i) (hLB i) (hDz i)
      (by
        rintro y ⟨x,hx,rfl⟩
        apply hpos (B i).center _ (e.map_target (hLe i hx))
        have heq : e (e.symm x)=x := e.right_inv (hLe i hx)
        exact heq.symm ▸ hLB i hx)]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS.measurableSet
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
  apply setIntegral_congr_fun hS.measurableSet
  intro y hy
  have hey : e y∈K := by
    obtain ⟨x,hx,rfl⟩ := hy
    have heq : e (e.symm x)=x := e.right_inv (hKe hx)
    rwa [heq]
  have hs : (∑ i,ρ i (e y))=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hey
  simp only [D,partialChartCoefficient_smul,← Finset.sum_mul,hs,one_mul]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
