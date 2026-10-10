import Mathlib
import OAI.Geometry.BallPacking.Projective.AnnularChartHelpers
import OAI.Geometry.BallPacking.SurfaceArea.SurfaceIntegralIndependence

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  {I J : Type*} [Fintype I] [Fintype J] {K : Set M}

 theorem restrictedPartitionFormMass_independent (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (hskew : ∀ x u v,Ω x u v= -Ω x v u) :
    restrictedPartitionFormMass B ρ K Ω=restrictedPartitionFormMass C ν K Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let L : I → J → Set M := fun i j => tsupport (ρ i) ∩ tsupport (ν j)
  have hL (i : I) (j : J) : IsCompact (L i j) :=
    ((B i).isCompact_compactCarrier.of_isClosed_subset (isClosed_tsupport _)
      ((hρ i).trans (B i).carrier_subset_compactCarrier)).inter_right (isClosed_tsupport _)
  have hLB (i : I) (j : J) : L i j⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.1).1
  have hLC (i : I) (j : J) : L i j⊆(extChartAt 𝓘(ℝ,Plane) (C j).center).source :=
    fun _ hx => (hν j hx.2).1
  have hint (i : I) (j : J) (c : M) (hc : L i j⊆(extChartAt 𝓘(ℝ,Plane) c).source) :
      Integrable (fun y => extendedChartCoefficient c
        (fun _ : ℝ => fun x => ρ i x • (ν j x • K.indicator Ω x)) (0,y)) := by
    let D : ManifoldTwoForm Plane M := fun x => ρ i x • (ν j x • Ω x)
    have hDs : SmoothTwoForm D :=
      (((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ν j).contMDiff).spatial_smul
        (ρ i).contMDiff).eval 0
    have hDz : ∀ x,x∉L i j → D x=0 := by
      intro x hx
      by_cases hi : x∈tsupport (ρ i)
      · have hj : x∉tsupport (ν j) := fun hj => hx ⟨hi,hj⟩
        simp only [D,image_eq_zero_of_notMem_tsupport hj,zero_smul,smul_zero]
      · simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    have he : (fun x => ρ i x • (ν j x • K.indicator Ω x))=K.indicator D := by
      funext x
      by_cases hx : x∈K <;> simp only [Set.indicator,hx,↓reduceIte,D,smul_zero]
    rw [he]
    exact extendedChartCoefficient_indicator_integrable c hK.measurableSet
      (hDs.coefficient_integrable c (hL i j) hc hDz)
  rw [restrictedPartitionFormMass_eq_indicator B ρ hK.measurableSet,
    restrictedPartitionFormMass_eq_indicator C ν hK.measurableSet]
  apply partitionFormMass_independent_integrable hpos hK B C ρ ν hρ hν
  · intro x u v
    by_cases hx : x∈K
    · simpa only [Set.indicator_of_mem hx] using hskew x u v
    · simp only [Set.indicator_of_notMem hx,zero_apply,neg_zero]
  · exact fun x hx => Set.indicator_of_notMem hx Ω
  · exact fun i j => hint i j (B i).center (hLB i j)
  · exact fun i j => hint i j (C j).center (hLC i j)

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]

 def compactSurfaceBoxes {D : Set M} (hD : IsCompact D) : Finset (SurfaceCoordinateBox M) :=
  Classical.choose (SurfaceCoordinateBox.finite_partition hD)

 def compactSurfacePartition {D : Set M} (hD : IsCompact D) :
    SmoothPartitionOfUnity (compactSurfaceBoxes hD) 𝓘(ℝ,Plane) M D :=
  Classical.choose (Classical.choose_spec (SurfaceCoordinateBox.finite_partition hD))

 theorem compactSurfacePartition_subordinate {D : Set M} (hD : IsCompact D) :
    (compactSurfacePartition hD).IsSubordinate
      (fun B : compactSurfaceBoxes hD => B.1.carrier) :=
  Classical.choose_spec (Classical.choose_spec (SurfaceCoordinateBox.finite_partition hD))

 def compactSurfaceFormIntegral {D : Set M} (hD : IsCompact D)
    (Ω : ManifoldTwoForm Plane M) : ℝ :=
  restrictedPartitionFormMass (fun B : compactSurfaceBoxes hD => B.1)
    (compactSurfacePartition hD) D Ω

 variable [MeasurableSpace M] [BorelSpace M]
 theorem compactSurfaceFormIntegral_eq {I : Type*} [Fintype I] {D : Set M}
    (hD : IsCompact D) (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M D)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (hskew : ∀ x u v,Ω x u v= -Ω x v u) :
    compactSurfaceFormIntegral hD Ω=restrictedPartitionFormMass B ρ D Ω :=
  restrictedPartitionFormMass_independent hor hD _ B _ ρ
    (compactSurfacePartition_subordinate hD) hρ hΩ hskew

 theorem compactSurfaceFormIntegral_congr {D : Set M} (hD : IsCompact D)
    {Ω Λ : ManifoldTwoForm Plane M} (h : EqOn Ω Λ D) :
    compactSurfaceFormIntegral hD Ω=compactSurfaceFormIntegral hD Λ := by
  unfold compactSurfaceFormIntegral
  rw [restrictedPartitionFormMass_eq_indicator _ _ hD.isClosed.measurableSet,
    restrictedPartitionFormMass_eq_indicator _ _ hD.isClosed.measurableSet]
  congr 1
  exact Set.indicator_congr h

end
section

section FormOperations
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem SmoothOneFormFamily.zero :
    SmoothOneFormFamily (fun _ : P => (0 : ManifoldOneForm E M)) := by
  intro c
  simpa only [chartOneForm_zero] using
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P × E => (0 : E →L[ℝ] ℝ)) _)

theorem SmoothOneFormFamily.sum {I : Type*} (s : Finset I)
    {α : I → P → ManifoldOneForm E M} (hα : ∀ i ∈ s, SmoothOneFormFamily (α i)) :
    SmoothOneFormFamily (fun p => ∑ i ∈ s, α i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using SmoothOneFormFamily.zero (P := P)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hα j (Finset.mem_insert_of_mem hj)))

theorem manifoldExteriorOneForm_sum {I : Type*} (s : Finset I)
    {α : I → P → ManifoldOneForm E M} (hα : ∀ i ∈ s, SmoothOneFormFamily (α i))
    (p : P) (x : M) :
    manifoldExteriorOneForm (∑ i ∈ s,α i p) x =
      ∑ i ∈ s,manifoldExteriorOneForm (α i p) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,manifoldExteriorOneForm_zero]
  | @insert i s hi ih =>
    have hx : extChartAt 𝓘(ℝ,E) x x ∈ (extChartAt 𝓘(ℝ,E) x).target :=
      (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
    have hs := fun j hj => hα j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    rw [manifoldExteriorOneForm_add_at
      ((hα i (Finset.mem_insert_self i s)).spatial_smooth p x hx)
      ((SmoothOneFormFamily.sum s hs).spatial_smooth p x hx), ih hs]

end FormOperations

section Integral
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem restrictedPartitionFormMass_smul {I : Type*} [Fintype I] {K : Set M}
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (D : Set M) (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    restrictedPartitionFormMass B ρ D (a • Ω) = a * restrictedPartitionFormMass B ρ D Ω := by
  unfold restrictedPartitionFormMass
  simp_rw [show a • Ω = fun x => a • Ω x from rfl,
    partitionChartDensity_spatial_smul B ρ Ω (fun _ => a)]
  simp_rw [integral_mul_const]
  rw [← Finset.sum_mul, mul_comm]

variable [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem compactSurfaceFormIntegral_smul {D : Set M} (hD : IsCompact D)
    (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    compactSurfaceFormIntegral hD (a • Ω)=a * compactSurfaceFormIntegral hD Ω :=
  restrictedPartitionFormMass_smul _ _ _ _ _

end Integral

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormalSpace M] [SigmaCompactSpace M]

def equalNormalCoefficient (m : ℕ) (b : ℝ) (p : Fin m → ℝ) : ℝ :=
  1-b*∑ j,p j

theorem equalNormalCoefficient_smooth (m : ℕ) (b : ℝ) :
    ContDiff ℝ ∞ (equalNormalCoefficient m b) := by
  unfold equalNormalCoefficient
  exact contDiff_const.sub (contDiff_const.mul (ContDiff.sum (fun j _ => contDiff_apply ℝ ℝ j)))

theorem exists_base_primitive_near_compact {K : Set M} (hK : IsCompact K)
    (hproper : Kᶜ.Nonempty) (hor : PositivePlaneTransitions M)
    {σ : ManifoldTwoForm Plane M} (hσ : SmoothTwoForm σ)
    (hskew : ∀ x u v,σ x u v= -σ x v u) :
    ∃ (γ : ManifoldOneForm Plane M) (L : Set M), IsCompact L ∧
      SmoothOneFormFamily (fun _ : ℝ => γ) ∧
      (∀ x,x∉L → γ x=0) ∧
      ∀ᶠ x in 𝓝ˢ K,manifoldExteriorOneForm γ x=σ x := by
  obtain ⟨α,L,hL,hα,hαz,hdα⟩ := exists_primitive_near_proper_compact hK hproper hor
    (SmoothTwoFormFamily.const (P := ℝ) hσ) (fun _ x u v => hskew x u v)
  refine ⟨α 0,L,hL,?_,hαz 0,hdα.mono (fun _ hx => hx 0)⟩
  exact hα.comp (f := fun _ : ℝ => (0 : ℝ)) contDiff_const

def equalNormalPrimitive {m : ℕ} (γ : ManifoldOneForm Plane M)
    (A : Fin m → ManifoldOneForm Plane M) (p : Fin m → ℝ) : ManifoldOneForm Plane M :=
  γ+∑ j,p j • A j

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormalSpace M] [SigmaCompactSpace M] in
theorem equalNormalPrimitive_smooth {m : ℕ} {γ : ManifoldOneForm Plane M}
    {A : Fin m → ManifoldOneForm Plane M}
    (hγ : SmoothOneFormFamily (fun _ : ℝ => γ))
    (hA : ∀ j,SmoothOneFormFamily (fun _ : ℝ => A j)) :
    SmoothOneFormFamily (equalNormalPrimitive γ A) := by
  apply (hγ.comp (f := fun _ : Fin m → ℝ => (0 : ℝ)) contDiff_const).add
  exact SmoothOneFormFamily.sum Finset.univ (fun j _ =>
    ((hA j).comp (f := fun _ : Fin m → ℝ => (0 : ℝ)) contDiff_const).smul
      (contDiff_apply ℝ ℝ j))

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormalSpace M] [SigmaCompactSpace M] in
theorem equalNormalPrimitive_exterior {m : ℕ} {γ : ManifoldOneForm Plane M}
    {A : Fin m → ManifoldOneForm Plane M}
    (hγ : SmoothOneFormFamily (fun _ : ℝ => γ))
    (hA : ∀ j,SmoothOneFormFamily (fun _ : ℝ => A j))
    (b : ℝ) (σ : ManifoldTwoForm Plane M) {x : M}
    (hdγ : manifoldExteriorOneForm γ x=σ x)
    (hdA : ∀ j,manifoldExteriorOneForm (A j) x=(-b) • σ x)
    (p : Fin m → ℝ) :
    manifoldExteriorOneForm (equalNormalPrimitive γ A p) x =
      equalNormalCoefficient m b p • σ x := by
  have hx : extChartAt 𝓘(ℝ,Plane) x x ∈ (extChartAt 𝓘(ℝ,Plane) x).target :=
    (extChartAt 𝓘(ℝ,Plane) x).map_source (mem_extChartAt_source x)
  have hs j : SmoothOneFormFamily (fun _ : ℝ => p j • A j) :=
    (hA j).smul contDiff_const
  unfold equalNormalPrimitive
  rw [manifoldExteriorOneForm_add_at (hγ.spatial_smooth 0 x hx)
    ((SmoothOneFormFamily.sum Finset.univ (fun j _ => hs j)).spatial_smooth 0 x hx),hdγ,
    manifoldExteriorOneForm_sum Finset.univ (fun j _ => hs j) 0 x]
  simp_rw [manifoldExteriorOneForm_smul_at (α := A _) _ ((hA _).spatial_smooth 0 x hx),hdA,
    smul_smul]
  rw [← Finset.sum_smul]
  calc
    σ x+(∑ j,p j * -b) • σ x = (1+∑ j,p j * -b) • σ x := by
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change σ x u v+(∑ j,p j * -b)*σ x u v = (1+∑ j,p j * -b)*σ x u v
      ring
    _ = equalNormalCoefficient m b p • σ x := ?_
  congr 1
  unfold equalNormalCoefficient
  rw [← Finset.sum_mul]
  ring

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def familySpatialExterior (Γ : P × E → E →L[ℝ] ℝ) (p : P × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ P E) -
    ((fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ P E)).flip

 theorem familySpatialExterior_smoothAt {Γ : P × E → E →L[ℝ] ℝ}
    {p : P × E} (hΓ : ContDiffAt ℝ ∞ Γ p) : ContDiffAt ℝ ∞ (familySpatialExterior Γ) p := by
  have hd : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ Γ q).comp (ContinuousLinearMap.inr ℝ P E)) p :=
    (hΓ.fderiv_right (by simp)).clm_comp contDiffAt_const
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  exact hd.sub (hflip.contDiffAt.comp p hd)

 theorem familySpatialExterior_eq_slice {Γ : P × E → E →L[ℝ] ℝ}
    {p : P × E} (hΓ : DifferentiableAt ℝ Γ p) :
    familySpatialExterior Γ p=euclideanExteriorOneForm (fun x => Γ (p.1,x)) p.2 := by
  have hi : HasFDerivAt (fun y : E => (p.1,y))
      ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hh : HasFDerivAt Γ (fderiv ℝ Γ p) (p.1,p.2) := hΓ.hasFDerivAt
  have hs := (hh.comp p.2 hi).fderiv
  change fderiv ℝ (fun y => Γ (p.1,y)) p.2 = _ at hs
  unfold familySpatialExterior euclideanExteriorOneForm
  rw [hs]
  rfl

 theorem manifoldExteriorOneForm_family_smooth {Γ : P → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothTwoFormFamily (fun p => manifoldExteriorOneForm (Γ p)) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((familySpatialExterior_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  rw [manifoldExteriorOneForm_chart (fun b y hy => (hΓ.spatial_smooth q.1 b hy).contDiffWithinAt) hq.2]
  exact (familySpatialExterior_eq_slice (((hΓ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)).differentiableAt (by simp))).symm

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

 omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem chartOneForm_spatial_smul (ρ : M → ℝ) (α : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (fun x => ρ x • α x) c y=
      ρ ((extChartAt 𝓘(ℝ,E) c).symm y) • chartOneForm α c y := by
  ext u
  rfl

 theorem SmoothOneFormFamily.spatial_smul [IsManifold 𝓘(ℝ,E) ∞ M]
    {α : P → ManifoldOneForm E M} (hα : SmoothOneFormFamily α) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ρ) :
    SmoothOneFormFamily (fun p x => ρ x • α p x) := by
  intro c q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hrs := (hρ.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
  have hfs := (hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)
  simpa only [chartOneForm_spatial_smul,Pi.smul_def',Function.comp_apply] using (hrs.smul hfs).contDiffWithinAt

 omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem manifoldExteriorOneForm_zero_off [IsManifold 𝓘(ℝ,E) ∞ M]
    {L : Set M} (hL : IsClosed L) {α : ManifoldOneForm E M}
    (hz : ∀ x,x∉L→α x=0) {x : M} (hx : x∉L) : manifoldExteriorOneForm α x=0 := by
  have he : α =ᶠ[𝓝 x] (0 : ManifoldOneForm E M) := by
    filter_upwards [hL.isOpen_compl.mem_nhds hx] with y hy
    exact hz y hy
  rw [manifoldExteriorOneForm_congr_of_eventuallyEq he,manifoldExteriorOneForm_zero]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifoldExteriorOneForm_path_closed {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (c : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) (u v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,w) u v=0 := by
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ _,hy⟩)
  have he : (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) =ᶠ[𝓝 (t,y)]
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldExteriorOneForm_path_chart hΓ hq.2
  rw [he.fderiv_eq]
  exact exact_path_closedAt ((hΓ c).contDiffAt hn) u v w

theorem manifoldExteriorOneForm_path_time {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (c : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) (v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) (t,y) (0,w) v := by
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ _,hy⟩)
  have he : (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) =ᶠ[𝓝 (t,y)]
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldExteriorOneForm_path_chart hΓ hq.2
  have ha : (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) =ᶠ[𝓝 (t,y)]
      pathTimePrimitive (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldTimePrimitive_chart hΓ hq.2
  rw [he.fderiv_eq,ha.fderiv_eq]
  exact exact_path_time_equationAt ((hΓ c).contDiffAt hn) v w

theorem SmoothOneFormFamily.time_contDiffAt {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (x : M) : ContDiffAt ℝ ∞ (fun s => Γ s x) t := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hcam := ((hΓ x).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      (show (t,extChartAt 𝓘(ℝ,E) x x) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) x).target from ⟨mem_univ t,hxt⟩))).comp t (contDiffAt_id.prodMk contDiffAt_const)
  have hsm := hcam.clm_comp (contDiffAt_const (c := chartDifferential x x))
  apply hsm.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [(extChartAt 𝓘(ℝ,E) x).left_inv hx,Function.comp_def,id_eq] using (chartOneForm_reconstruct_target
      (α := Γ s) hxt).symm)

theorem manifoldTimePrimitive_annihilates {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {x : M} {Z : E} (hz : ∀ t, Γ t x Z=0) (t : ℝ) :
    manifoldTimePrimitive Γ t x Z=0 := by
  have hd := (((hΓ.time_contDiffAt t x).differentiableAt (by simp)).hasDerivAt).clm_apply
    (hasDerivAt_const t Z)
  have he : (fun s => Γ s x Z) = fun _ : ℝ => (0:ℝ) := funext hz
  change HasDerivAt (fun s => Γ s x Z) _ t at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const t (0:ℝ))
  simpa only [manifoldTimePrimitive,ContinuousLinearMap.map_zero,add_zero] using hh

theorem manifoldTimePrimitive_eval_constant {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {x : M} {Z : E}
    (hz : ∀ t, Γ t x Z=Γ 0 x Z) (t : ℝ) : manifoldTimePrimitive Γ t x Z=0 := by
  have hd := (((hΓ.time_contDiffAt t x).differentiableAt (by simp)).hasDerivAt).clm_apply
    (hasDerivAt_const t Z)
  have he : (fun s => Γ s x Z) = fun _ : ℝ => Γ 0 x Z := funext hz
  change HasDerivAt (fun s => Γ s x Z) _ t at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const t (Γ 0 x Z))
  simpa only [manifoldTimePrimitive,ContinuousLinearMap.map_zero,add_zero] using hh

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifoldTimePrimitive_stationary {Γ : ℝ → ManifoldOneForm E M}
    {x : M} (hz : ∀ t, Γ t x=Γ 0 x) (t : ℝ) : manifoldTimePrimitive Γ t x=0 := by
  unfold manifoldTimePrimitive
  rw [show (fun s => Γ s x)=fun _ : ℝ => Γ 0 x from funext hz]
  exact deriv_const t (Γ 0 x)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_skew (α : ManifoldOneForm E M) (x : M) (v w : E) :
    manifoldExteriorOneForm α x v w = -manifoldExteriorOneForm α x w v := by
  change fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) = -_
  change _ = -(fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w))
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 def coefficientNorm (D m : ℕ) (x : BaseCurve) : ℝ :=
  1+phaseSq (weightedPhaseInclusion D m x)

 theorem coefficientNorm_pos (D m : ℕ) (x : BaseCurve) : 0<coefficientNorm D m x := by
  dsimp [coefficientNorm]
  linarith [phaseSq_nonneg (weightedPhaseInclusion D m x)]

 theorem coefficientNorm_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (coefficientNorm D m) :=
  contMDiff_const.add (phaseSq_smooth.contMDiff.comp (weightedPhaseInclusion_smooth D m))

 def reducedProbability (w : ι → MomentPlane) (D m : ι → ℕ) (p : MomentPlane)
    (x : BaseCurve) (i : ι) : ℝ := selected w (fun j => coefficientNorm (D j) (m j) x) p i

 theorem reducedProbability_pos (w : ι → MomentPlane) (D m : ι → ℕ) (p : MomentPlane)
    (x : BaseCurve) (i : ι) : 0<reducedProbability w D m p x i :=
  selected_pos (fun j => coefficientNorm_pos (D j) (m j) x) _ _

 theorem reducedProbability_sum (w : ι → MomentPlane) (D m : ι → ℕ) (p : MomentPlane)
    (x : BaseCurve) : ∑ i,reducedProbability w D m p x i=1 :=
  selected_sum (fun j => coefficientNorm_pos (D j) (m j) x) _

 theorem reducedProbability_mean {w : ι → MomentPlane} (D m : ι → ℕ) {p : MomentPlane}
    (hp : Surrounds w p) (x : BaseCurve) : ∑ i,reducedProbability w D m p x i • w i=p :=
  selected_mean (fun j => coefficientNorm_pos (D j) (m j) x) hp

 theorem reducedProbability_smooth {w : ι → MomentPlane} (D m : ι → ℕ) {p : MomentPlane}
    (hp : Surrounds w p) (i : ι) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (fun x => reducedProbability w D m p x i) := by
  have ha : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ι → ℝ) ∞
      (fun x : BaseCurve => fun j => coefficientNorm (D j) (m j) x) :=
    contMDiff_pi_space.mpr (fun j => coefficientNorm_smooth _ _)
  intro x
  exact (selected_contDiffAt (fun j => coefficientNorm_pos (D j) (m j) x) hp i).contMDiffAt.comp x
    ((ha.prodMk_space contMDiff_const).contMDiffAt)

 def reducedPrimitive (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ) (p : MomentPlane) :
    ManifoldOneForm RealModel BaseCurve :=
  fun x => ∑ i,reducedProbability w D m p x i • weightedFSPrimitive (D i) (m i) c x

 def reducedForm (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ) (p : MomentPlane) :
    ManifoldTwoForm RealModel BaseCurve := manifoldExteriorOneForm (reducedPrimitive w D m c p)

 theorem reducedPrimitive_smooth {w : ι → MomentPlane} (D m : ι → ℕ) (c : ℝ) {p : MomentPlane}
    (hp : Surrounds w p) : SmoothOneFormFamily (fun _ : ℝ => reducedPrimitive w D m c p) := by
  have hs := SmoothOneFormFamily.sum Finset.univ (fun i _ =>
    (weightedFSPrimitive_smooth (D i) (m i) c).spatial_smul (reducedProbability_smooth D m hp i))
  convert hs using 1
  funext t x
  simp only [reducedPrimitive,Finset.sum_apply]

 theorem reducedForm_smooth {w : ι → MomentPlane} (D m : ι → ℕ) (c : ℝ) {p : MomentPlane}
    (hp : Surrounds w p) : SmoothTwoForm (reducedForm w D m c p) :=
  (manifoldExteriorOneForm_family_smooth (reducedPrimitive_smooth D m c hp)).eval 0

 omit [Nonempty ι] in
 theorem reducedForm_skew (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ) (p : MomentPlane)
    (x : BaseCurve) (v u : RealModel) : reducedForm w D m c p x v u= -reducedForm w D m c p x u v :=
  manifoldExteriorOneForm_skew _ _ _ _

end PackingSufficiencySupport.CubicModel
end

end OAI
