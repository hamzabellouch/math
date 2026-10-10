import Mathlib
import OAI.Geometry.BallPacking.Annuli.AnnularHandleCurvature

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

@[simp] theorem handleAnnularCover_eq_densityChart
    (D : AnnularHandleData Plane M)
     : D.handleAnnularCover = D.densityChart := rfl

theorem handleAnnularCover_rectangle_domain
    (D : AnnularHandleData Plane M)
    {U : Set Plane} (hU : U ⊆ Ioo (-D.width) D.width ×ˢ Ioo (0:ℝ) 1) :
    U ⊆ D.annularCoverDomain := by
  intro q hq
  change cylinderCover q ∈ D.chart.source
  rw [D.source_eq]
  exact ⟨(hU hq).1,mem_univ _⟩

theorem annularPackingChart_smoothOn
    (D : AnnularHandleData Plane M)
     {U : Set (Plane × V)} (hU : ∀ p ∈ U, p.1 ∈ D.annularCoverDomain) :
    ContMDiffOn 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) ∞
      (flatProductMap (D.handleAnnularCover)) U := by
  intro p hp
  exact (flatProductMap_smoothAt (D.handleAnnularCover_smoothAt (hU p hp))).contMDiffWithinAt

omit [NormedSpace ℝ V] in
theorem annularPackingChart_isEmbedding
    (D : AnnularHandleData Plane M)
    {U : Set (Plane × V)} (hU : ∀ p ∈ U, p.1 ∈ Ioo (-D.width) D.width ×ˢ Ioo (0:ℝ) 1) :
    Topology.IsEmbedding (fun p : U => flatProductMap (D.handleAnnularCover) p.val) := by
  let c := D.densityChart.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl V)
  have hsub : U ⊆ c.source := by
    intro p hp
    change p.1 ∈ D.densityChart.source ∧ p.2 ∈ (univ : Set V)
    rw [D.densityChart_source]
    exact ⟨hU p hp,mem_univ _⟩
  exact c.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hsub)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def handleDensityCore (b : ℝ) (f : Circle → ℝ) : Set HandleTorus :=
  (circleTurn '' Icc (-b) b) ×ˢ tsupport f

theorem handleDensityCore_compact (b : ℝ) (f : Circle → ℝ) :
    IsCompact (handleDensityCore b f) :=
  circleBand_compact.prod isClosed_closure.isCompact

theorem handleDensityCore_subset_band (b : ℝ) (f : Circle → ℝ) :
    handleDensityCore b f⊆compactHandleBand b := by
  rintro z ⟨⟨s,hs,he⟩,_⟩
  exact ⟨(s,z.2),⟨hs,mem_univ _⟩,Prod.ext he rfl⟩

theorem globalHandleDensity_inside
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (b : ℝ) (f : Circle → ℝ) {x : M} (hx : x∈e.target) (v w : E) :
    globalHandleDensity e b f x v w=
      torusAnnularDensity b f (e.symm x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TorusModel) e.symm x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TorusModel) e.symm x w) := by
  simp only [globalHandleDensity,globalHandleRadialForm,globalHandleForm,
    handlePushforwardOneForm,extendManifoldOneForm_inside hx,manifoldPullbackOneForm,
    manifoldMapDifferential,manifoldWedge_apply,
    torusAnnularDensity]
  rfl

theorem globalHandleDensity_core_zero
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {b : ℝ} (hb : 0<b) (f : Circle → ℝ) {x : M}
    (hx : x∉e '' handleDensityCore b f) : globalHandleDensity e b f x=0 := by
  by_cases ht : x∈e.target
  · have hn : e.symm x∉handleDensityCore b f := by
      intro hn
      exact hx ⟨e.symm x,hn,e.right_inv ht⟩
    have hz : torusAnnularDensity b f (e.symm x)=0 :=
      image_eq_zero_of_notMem_tsupport (fun hs => hn (torusAnnularDensity_tsupport hb f hs))
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change globalHandleDensity e b f x v w=0
    rw [globalHandleDensity_inside e b f ht,hz]
    rfl
  · have hz : globalHandleRadialForm e b x=0 := extendManifoldOneForm_outside ht
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change globalHandleDensity e b f x v w=0
    simp only [globalHandleDensity,manifoldWedge_apply,hz,zero_apply,zero_mul,mul_zero,sub_self]

theorem globalHandleDensity_core_support [T2Space M]
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {b : ℝ} (hb : 0<b) (he : compactHandleBand b⊆e.source) (f : Circle → ℝ) :
    tsupport (globalHandleDensity e b f)⊆e '' handleDensityCore b f := by
  apply closure_minimal _ ((handleDensityCore_compact b f).image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono ((handleDensityCore_subset_band b f).trans he))).isClosed
  intro x hx
  by_contra hn
  exact hx (globalHandleDensity_core_zero e hb f hn)

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def handleDensityChart
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞ :=
  restrictHandleDiffeomorph (torusRectangle.trans e) (Ioo (-a) a ×ˢ Ioo (0:ℝ) 1)
    (isOpen_Ioo.prod isOpen_Ioo)

@[simp] theorem handleDensityChart_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) (y : Plane) : handleDensityChart e a y=e (torusTurns y) := rfl

theorem handleDensityChart_source
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a : ℝ} (ha : a<1/2) (he : compactHandleBand a⊆e.source) :
    (handleDensityChart e a).source=Ioo (-a) a ×ˢ Ioo (0:ℝ) 1 := by
  apply inter_eq_right.mpr
  intro y hy
  refine ⟨?_,he ?_⟩
  · exact ⟨⟨by linarith [hy.1.1],by linarith [hy.1.2]⟩,hy.2⟩
  · exact ⟨(y.1,circleTurn y.2),⟨⟨hy.1.1.le,hy.1.2.le⟩,mem_univ _⟩,rfl⟩

theorem handleDensityChart_contains
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a b : ℝ} (ha : a<1/2) (hab : b<a) (he : compactHandleBand a⊆e.source)
    {f : Circle → ℝ} (hf : tsupport f⊆({1}ᶜ : Set Circle)) :
    e '' handleDensityCore b f⊆(handleDensityChart e a).target := by
  rintro x ⟨z,⟨⟨s,hs,heq⟩,hz⟩,rfl⟩
  have ht : z.2∈positiveCircleCoordinate.target := by
    rw [positiveCircleCoordinate_target]
    exact hf hz
  obtain ⟨t,ht,heq'⟩ := ht
  have hy : (s,t)∈(handleDensityChart e a).source := by
    rw [handleDensityChart_source e ha he]
    exact ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,ht⟩
  have hi := (handleDensityChart e a).map_source hy
  have hev : handleDensityChart e a (s,t)=e z := congrArg e (Prod.ext heq heq')
  exact hev ▸ hi

theorem handleDensityChart_coefficient
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) {y : Plane} (hy : y∈(handleDensityChart e a).source) :
    partialChartCoefficient (handleDensityChart e a) (globalHandleDensity e b f) y=
      circleClockDensity b (circleTurn y.1)*f (circleTurn y.2) := by
  have hh := globalHandleDensity_turns e b f hy.1.2 (1,0) (0,1)
  unfold partialChartCoefficient euclideanPullbackTwoForm
  have heq : (handleDensityChart e a : Plane → M)=e ∘ torusTurns := rfl
  rw [heq]
  simpa only [mul_one, mul_zero, sub_zero] using! hh

end
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def handleFirstCorrection
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (p : ℝ × V) : ManifoldOneForm E M := fun x =>
  surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
      (p,((handleAnnularChart e a).symm x).1) • globalHandleRadialForm e b x +
  surfaceFirstCorrectionCoefficient Φ (intervalClock (-b) b) H
      (p,((handleAnnularChart e a).symm x).1) • globalHandleForm e f x

def globalSurfaceFirstPrimitive
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) : ManifoldOneForm E M :=
  Γ p.2 + extendManifoldOneForm (handleAnnularChart e a).target
    (handleFirstCorrection e a b f Φ H p)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem handleAnnularChart_off_band
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) {x : M} (hx : x∈(handleAnnularChart e a).target)
    (hn : x∉e '' compactHandleBand b) :
    ((handleAnnularChart e a).symm x).1∉Icc (-b) b := by
  intro hs
  apply hn
  exact ⟨torusAnnulusMap ((handleAnnularChart e a).symm x),
    ⟨(handleAnnularChart e a).symm x,⟨hs,mem_univ _⟩,rfl⟩,
    (handleAnnularChart e a).right_inv hx⟩

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem handleFirstCorrection_off_band
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {b : ℝ} (hb : 0<b) (f : Circle → ℝ)
    (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ) (p : ℝ × V) {x : M}
    (hx : x∈(handleAnnularChart e a).target) (hn : x∉e '' compactHandleBand b) :
    handleFirstCorrection e a b f Φ H p x=0 := by
  have hr : globalHandleRadialForm e b x=0 :=
    handlePushforwardOneForm_zero e (fun _ hy => torusFirstForm_clock_zero hb hy) hn
  have ht : intervalClock (-b) b ((handleAnnularChart e a).symm x).1=0 ∨
      intervalClock (-b) b ((handleAnnularChart e a).symm x).1=1 := by
    have hs := handleAnnularChart_off_band e a b hx hn
    simp only [mem_Icc,not_and_or,not_le] at hs
    rcases hs with hs|hs
    · exact Or.inl (intervalClock_zero (by linarith) hs.le)
    · exact Or.inr (intervalClock_one (by linarith) hs.le)
  simp only [handleFirstCorrection,hr,smul_zero,
    surfaceFirstCorrectionCoefficient_tails Φ _ H p _ ht,zero_smul,add_zero]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem globalSurfaceFirstPrimitive_off_band
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {b : ℝ} (hb : 0<b) (f : Circle → ℝ)
    (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ) (Γ : V → ManifoldOneForm E M)
    (p : ℝ × V) {x : M} (hn : x∉e '' compactHandleBand b) :
    globalSurfaceFirstPrimitive e a b f Φ H Γ p x=Γ p.2 x := by
  by_cases hx : x∈(handleAnnularChart e a).target
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_inside hx,
      handleFirstCorrection_off_band e a hb f Φ H p hx hn]
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_outside hx]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem globalSurfaceFirstPrimitive_zero
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (v : V) :
    globalSurfaceFirstPrimitive e a b f Φ H Γ (0,v)=Γ v := by
  funext x
  by_cases hx : x∈(handleAnnularChart e a).target
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_inside hx,handleFirstCorrection]
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_outside hx]

theorem globalSurfaceFirstPrimitive_smooth [T2Space M]
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {a b : ℝ} (ha : a<1/2) (hb : 0<b) (hab : b<a) (he : compactHandleBand a⊆e.source)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfs : tsupport (torusHandleForm f)⊆e.source)
    (Φ : CompactHamiltonianIsotopy Ω) {H : V → ℝ} (hH : ContDiff ℝ ∞ H)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (globalSurfaceFirstPrimitive e a b f Φ H Γ) := by
  have hbe : compactHandleBand b⊆e.source := by
    rintro z ⟨w,hw,rfl⟩
    exact he ⟨w,⟨⟨by linarith [hw.1.1],by linarith [hw.1.2]⟩,mem_univ _⟩,rfl⟩
  have hr := handlePushforwardOneForm_smooth e (compactHandleBand_isCompact b) hbe
    (torusFirstForm_smooth (circleClockDensity_smooth hb (lt_trans hab ha)))
    (fun _ hx => torusFirstForm_clock_zero hb hx)
  have hβ := (globalHandleForm_properties e hf hfs).1
  have hα := extendManifoldOneForm_smooth (handleAnnularChart e a).open_target
    ((handleAnnularChart_compact e hab he).isClosed)
    (handleAnnularChart_compact_subset e ha hab he)
    (α := handleFirstCorrection e a b f Φ H)
    (fun c => by
      have h1 := annular_coefficient_smooth_on (handleAnnularChart e a).open_target
        (annular_inverse_fst_smooth (handleAnnularChart e a))
        (surfaceSuspensionCoefficient_smooth Φ (intervalClock_smooth (-b) b))
        (α := globalHandleRadialForm e b) (fun c => (hr c).comp
          (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
          (fun _ hy => ⟨mem_univ _,hy⟩)) c
      have h2 := annular_coefficient_smooth_on (handleAnnularChart e a).open_target
        (annular_inverse_fst_smooth (handleAnnularChart e a))
        (surfaceFirstCorrectionCoefficient_smooth Φ (intervalClock_smooth (-b) b) hH)
        (α := globalHandleForm e f) (fun c => (hβ c).comp
          (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
          (fun _ hy => ⟨mem_univ _,hy⟩)) c
      simpa only [handleFirstCorrection,chartOneForm,ContinuousLinearMap.add_comp] using h1.add h2)
    (fun p x hx hn => handleFirstCorrection_off_band e a hb f Φ H p hx hn)
  intro c
  have hmap : ContDiffOn ℝ ∞ (fun q : (ℝ × V) × E => (q.1.2,q.2))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
  have hbg := (hΓ c).comp hmap (fun _ hq => ⟨mem_univ _,hq.2⟩)
  simpa only [globalSurfaceFirstPrimitive,chartOneForm_add,Function.comp_apply] using hbg.add (hα c)

end
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

def handleSecondExtra
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : ℝ × V) : ManifoldOneForm E M := fun x =>
  surfaceSecondExtraCoefficient Φ (intervalClock (-b) b) K H h ρ ρ₀
    (p,((handleAnnularChart e a).symm x).1) • globalHandleForm e f x

def globalSurfaceSecondPrimitive
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) : ManifoldOneForm E M :=
  globalSurfaceFirstPrimitive e a b f Φ H Γ (1,p.2) +
    (p.1*(K p.2-H p.2)) • globalHandleForm e f +
    extendManifoldOneForm (handleAnnularChart e a).target
      (handleSecondExtra e a b f Φ K H h ρ ρ₀ p)

@[simp] theorem globalSurfaceSecondPrimitive_zero
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (v : V) :
    globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ (0,v)=
      globalSurfaceFirstPrimitive e a b f Φ H Γ (1,v) := by
  funext x
  by_cases hx : x∈(handleAnnularChart e a).target
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_inside hx,handleSecondExtra]
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_outside hx]

theorem handleSecondExtra_off_band
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {b : ℝ} (hb : 0<b) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (p : ℝ × V) {x : M} (hx : x∈(handleAnnularChart e a).target)
    (hn : x∉e '' compactHandleBand b) : handleSecondExtra e a b f Φ K H h ρ ρ₀ p x=0 := by
  have hs := handleAnnularChart_off_band e a b hx hn
  simp only [mem_Icc,not_and_or,not_le] at hs
  have ht : (intervalClock (-b) b ((handleAnnularChart e a).symm x).1=0 ∧
      (∀ i,ρ i ((handleAnnularChart e a).symm x).1=0) ∧
      ρ₀ ((handleAnnularChart e a).symm x).1=0) ∨
    (intervalClock (-b) b ((handleAnnularChart e a).symm x).1=1 ∧
      (∀ i,ρ i ((handleAnnularChart e a).symm x).1=1) ∧
      ρ₀ ((handleAnnularChart e a).symm x).1=1) := by
    rcases hs with hs|hs
    · exact Or.inl ⟨intervalClock_zero (by linarith) hs.le,hlo _ hs.le⟩
    · exact Or.inr ⟨intervalClock_one (by linarith) hs.le,hhi _ hs.le⟩
  simp only [handleSecondExtra,surfaceSecondExtraCoefficient_tails Φ _ K H h ρ ρ₀ p _ ht,zero_smul]

theorem globalSurfaceSecondPrimitive_off_band
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {b : ℝ} (hb : 0<b) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) {x : M}
    (hn : x∉e '' compactHandleBand b) :
    globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ p x=
      Γ p.2 x+(p.1*(K p.2-H p.2)) • globalHandleForm e f x := by
  by_cases hx : x∈(handleAnnularChart e a).target
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_inside hx,
      handleSecondExtra_off_band e a hb f Φ K H h ρ ρ₀ hlo hhi p hx hn,
      globalSurfaceFirstPrimitive_off_band e a hb f Φ H Γ (1,p.2) hn]
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_outside hx,
      globalSurfaceFirstPrimitive_off_band e a hb f Φ H Γ (1,p.2) hn]

variable [IsManifold 𝓘(ℝ,E) ∞ M]
theorem globalSurfaceSecondPrimitive_smooth [T2Space M]
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {a b : ℝ} (ha : a<1/2) (hb : 0<b) (hab : b<a) (he : compactHandleBand a⊆e.source)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfs : tsupport (torusHandleForm f)⊆e.source)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ} (hK : ContDiff ℝ ∞ K)
    (hH : ContDiff ℝ ∞ H) {h : ι → V → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : ι → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ) := by
  have hβ := (globalHandleForm_properties e hf hfs).1
  have hα := extendManifoldOneForm_smooth (handleAnnularChart e a).open_target
    (handleAnnularChart_compact e hab he).isClosed
    (handleAnnularChart_compact_subset e ha hab he)
    (α := handleSecondExtra e a b f Φ K H h ρ ρ₀)
    (fun c => annular_coefficient_smooth_on (handleAnnularChart e a).open_target
      (annular_inverse_fst_smooth (handleAnnularChart e a))
      (surfaceSecondExtraCoefficient_smooth Φ (intervalClock_smooth (-b) b) hK hH hh hρ hρ₀)
      (α := globalHandleForm e f) (fun c => (hβ c).comp
        (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨mem_univ _,hy⟩)) c)
    (fun p x hx hn => handleSecondExtra_off_band e a hb f Φ K H h ρ ρ₀ hlo hhi p hx hn)
  have hfirst := (globalSurfaceFirstPrimitive_smooth e ha hb hab he hf hfs Φ hH hΓ).comp
    (f := fun p : ℝ × V => (1,p.2)) (contDiff_const.prodMk (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × V → V)))
  have hj := (hβ.comp (f := fun _ : ℝ × V => (0:ℝ)) contDiff_const).smul
    (contDiff_fst.mul ((hK.sub hH).comp contDiff_snd))
  exact (hfirst.add hj).add hα

end
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem globalSurfaceFirstPrimitive_normal
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) (p : ℝ × V)
    {x : M} (hx : x∈(handleAnnularChart e a).target)
    (hN : Γ p.2 x=γ x+
      (intervalClock (-b) b ((handleAnnularChart e a).symm x).1*H p.2) • globalHandleForm e f x) :
    globalSurfaceFirstPrimitive e a b f Φ H Γ p x=
      γ x+surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
        (p,((handleAnnularChart e a).symm x).1) • globalHandleRadialForm e b x+
      (intervalClock (-b) b ((handleAnnularChart e a).symm x).1*
        H ((Φ.map p.1).symm (Φ.map (p.1*intervalClock (-b) b
          ((handleAnnularChart e a).symm x).1) p.2))) • globalHandleForm e f x := by
  simp only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_inside hx,hN,
    handleFirstCorrection,surfaceFirstCorrectionCoefficient]
  ext v
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem globalSurfaceSecondPrimitive_normal {ι : Type*} [Fintype ι]
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) (p : ℝ × V)
    {x : M} (hx : x∈(handleAnnularChart e a).target)
    (hN : Γ p.2 x=γ x+
      (intervalClock (-b) b ((handleAnnularChart e a).symm x).1*H p.2) • globalHandleForm e f x) :
    globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ p x=
      γ x+surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
        ((1,p.2),((handleAnnularChart e a).symm x).1) • globalHandleRadialForm e b x+
      surfaceInterpolatedLayer (intervalClock (-b) b) K H h (Φ.map 1).symm ρ ρ₀ p.1
        (((handleAnnularChart e a).symm x).1,
          Φ.map (intervalClock (-b) b ((handleAnnularChart e a).symm x).1) p.2) •
        globalHandleForm e f x := by
  simp only [globalSurfaceSecondPrimitive,globalSurfaceFirstPrimitive,Pi.add_apply,Pi.smul_apply,
    extendManifoldOneForm_inside hx,hN,handleFirstCorrection,handleSecondExtra,
    surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient,
    surfaceFirstCorrectionCoefficient,one_mul]
  ext v
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

def annularCoverA
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) (γ : ManifoldOneForm E M) (q : Plane) : ℝ :=
  euclideanPullbackOneForm (fun _ => γ) (handleAnnularCover e a) (0,q) (1,0)

def annularCoverB
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) (γ : ManifoldOneForm E M) (q : Plane) : ℝ :=
  euclideanPullbackOneForm (fun _ => γ) (handleAnnularCover e a) (0,q) (0,1)

theorem annularCover_form_rep
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) (γ : ManifoldOneForm E M) (q v : Plane) :
    γ (handleAnnularCover e a q) (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q v)=
      annularCoverA e a γ q*v.1+annularCoverB e a γ q*v.2 := by
  let L := euclideanPullbackOneForm (fun _ => γ) (handleAnnularCover e a) (0,q)
  change L v=L (1,0)*v.1+L (0,1)*v.2
  have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  rw [show L v=L (v.1 • (1,0)+v.2 • (0,1)) from congrArg L hv]
  simp only [map_add,map_smul,smul_eq_mul]
  ring

theorem globalSurfaceFirstPrimitive_cover
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M)
    (ℓ : ℝ) (p : Plane × V) (hp : cylinderCover p.1∈(handleAnnularChart e a).source)
    (hN : Γ p.2 (handleAnnularCover e a p.1)=γ (handleAnnularCover e a p.1)+
      (intervalClock (-b) b p.1.1*H p.2) • globalHandleForm e f (handleAnnularCover e a p.1)) :
    euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceFirstPrimitive e a b f Φ H Γ (ℓ,v)))
      (flatProductMap (handleAnnularCover e a)) (0,p)=
      surfaceFirstPrimitive Φ (intervalClock (-b) b) H
        (annularCoverA e a γ) (annularCoverB e a γ) (fun q => f (circleTurn q.2)) (ℓ,p) := by
  have hn := globalSurfaceFirstPrimitive_normal e a b f Φ H Γ γ (ℓ,p.2) (x := handleAnnularCover e a p.1)
    ((handleAnnularChart e a).map_source hp)
  have hi := handleAnnularCover_inverse e a hp
  have hN' : Γ p.2 (handleAnnularCover e a p.1)=γ (handleAnnularCover e a p.1)+
      (intervalClock (-b) b ((handleAnnularChart e a).symm (handleAnnularCover e a p.1)).1*H p.2) •
        globalHandleForm e f (handleAnnularCover e a p.1) := by
    simpa only [hi,cylinderCover] using hN
  have he := hn hN'
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) p.1
  have hd (u : Plane) : globalHandleForm e f (handleAnnularCover e a p.1) (A u) =
      f (circleTurn p.1.2) * u.2 := globalHandleForm_cover e a f hp u
  have hr (u : Plane) : globalHandleRadialForm e b (handleAnnularCover e a p.1) (A u) =
      deriv (intervalClock (-b) b) p.1.1 * u.1 := globalHandleRadialForm_cover e a b hp u
  have hg (u : Plane) : γ (handleAnnularCover e a p.1) (A u) =
      annularCoverA e a γ p.1 * u.1 + annularCoverB e a γ p.1 * u.2 :=
    annularCover_form_rep e a γ p.1 u
  apply ContinuousLinearMap.ext
  intro v
  rw [productHorizontalLift_pullback_apply _ (handleAnnularCover_smoothAt e a hp)]
  change (globalSurfaceFirstPrimitive e a b f Φ H Γ (ℓ,p.2) (handleAnnularCover e a p.1))
    (A v.1)=_
  erw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,hi,cylinderCover,
    hd, hr, hg,
    surfaceSuspensionCoefficient,surfaceFirstPrimitive,horizontalOneForm_apply]
  ring

theorem globalSurfaceSecondPrimitive_cover {ι : Type*} [Fintype ι]
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M)
    (τ : ℝ) (p : Plane × V) (hp : cylinderCover p.1∈(handleAnnularChart e a).source)
    (hN : Γ p.2 (handleAnnularCover e a p.1)=γ (handleAnnularCover e a p.1)+
      (intervalClock (-b) b p.1.1*H p.2) • globalHandleForm e f (handleAnnularCover e a p.1)) :
    euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ (τ,v)))
      (flatProductMap (handleAnnularCover e a)) (0,p)=
      surfaceSecondPrimitive Φ (intervalClock (-b) b) K H h ρ ρ₀
        (annularCoverA e a γ) (annularCoverB e a γ) (fun q => f (circleTurn q.2)) (τ,p) := by
  have hn := globalSurfaceSecondPrimitive_normal e a b f Φ K H h ρ ρ₀ Γ γ (τ,p.2) (x := handleAnnularCover e a p.1)
    ((handleAnnularChart e a).map_source hp)
  have hi := handleAnnularCover_inverse e a hp
  have hN' : Γ p.2 (handleAnnularCover e a p.1)=γ (handleAnnularCover e a p.1)+
      (intervalClock (-b) b ((handleAnnularChart e a).symm (handleAnnularCover e a p.1)).1*H p.2) •
        globalHandleForm e f (handleAnnularCover e a p.1) := by
    simpa only [hi,cylinderCover] using hN
  have he := hn hN'
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) p.1
  have hd (u : Plane) : globalHandleForm e f (handleAnnularCover e a p.1) (A u) =
      f (circleTurn p.1.2) * u.2 := globalHandleForm_cover e a f hp u
  have hr (u : Plane) : globalHandleRadialForm e b (handleAnnularCover e a p.1) (A u) =
      deriv (intervalClock (-b) b) p.1.1 * u.1 := globalHandleRadialForm_cover e a b hp u
  have hg (u : Plane) : γ (handleAnnularCover e a p.1) (A u) =
      annularCoverA e a γ p.1 * u.1 + annularCoverB e a γ p.1 * u.2 :=
    annularCover_form_rep e a γ p.1 u
  apply ContinuousLinearMap.ext
  intro v
  rw [productHorizontalLift_pullback_apply _ (handleAnnularCover_smoothAt e a hp)]
  change (globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ (τ,p.2) (handleAnnularCover e a p.1))
    (A v.1)=_
  erw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,hi,cylinderCover,
    hd, hr, hg,
    surfaceSuspensionCoefficient,surfaceSecondPrimitive,horizontalOneForm_apply,one_mul]
  ring

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def annularCoverDomain
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞) (a : ℝ) : Set Plane :=
  cylinderCover ⁻¹' (handleAnnularChart e a).source

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem annularCoverDomain_open
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞) (a : ℝ) :
    IsOpen (annularCoverDomain e a) :=
  (handleAnnularChart e a).open_source.preimage cylinderCover_smooth.continuous

theorem annularCover_pullback_smoothAt
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞) (a : ℝ)
    {γ : ManifoldOneForm E M} {q : Plane} (hq : q∈annularCoverDomain e a)
    (hγ : ContDiffAt ℝ ∞ (chartOneForm γ (handleAnnularCover e a q))
      (extChartAt 𝓘(ℝ,E) (handleAnnularCover e a q) (handleAnnularCover e a q))) :
    ContDiffAt ℝ ∞ (fun y => euclideanPullbackOneForm (fun _ => γ) (handleAnnularCover e a) (0,y)) q := by
  have hf := hγ.comp ((0:ℝ),extChartAt 𝓘(ℝ,E) (handleAnnularCover e a q)
    (handleAnnularCover e a q)) contDiffAt_snd
  have hs := parameterEuclideanPullbackOneForm_contDiffAt (α := fun _ : ℝ => γ)
    (p := (0,q)) hf (handleAnnularCover_smoothAt e a hq)
  exact hs.comp q (contDiffAt_const.prodMk contDiffAt_id)

theorem annularCover_coefficients_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞) (a : ℝ)
    {γ : ManifoldOneForm E M}
    (hγ : ∀ x∈(handleAnnularChart e a).target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x)) :
    ContDiffOn ℝ ∞ (annularCoverA e a γ) (annularCoverDomain e a) ∧
    ContDiffOn ℝ ∞ (annularCoverB e a γ) (annularCoverDomain e a) := by
  constructor <;> intro q hq
  · exact ((annularCover_pullback_smoothAt e a hq
      (hγ _ ((handleAnnularChart e a).map_source hq))).clm_apply contDiffAt_const).contDiffWithinAt
  · exact ((annularCover_pullback_smoothAt e a hq
      (hγ _ ((handleAnnularChart e a).map_source hq))).clm_apply contDiffAt_const).contDiffWithinAt

theorem annularCover_curl
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞) (a : ℝ)
    {γ : ManifoldOneForm E M} {q : Plane} (hq : q∈annularCoverDomain e a)
    (hγ : ContDiffAt ℝ ∞ (chartOneForm γ (handleAnnularCover e a q))
      (extChartAt 𝓘(ℝ,E) (handleAnnularCover e a q) (handleAnnularCover e a q))) :
    fderiv ℝ (annularCoverB e a γ) q (1,0)-fderiv ℝ (annularCoverA e a γ) q (0,1)=
      manifoldExteriorOneForm γ (handleAnnularCover e a q)
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q (1,0))
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q (0,1)) := by
  have hs := annularCover_pullback_smoothAt e a hq hγ
  have he : (fun y => euclideanPullbackOneForm (fun _ => γ) (handleAnnularCover e a) (0,y))=
      (fun y => planarCovector (annularCoverA e a γ y) (annularCoverB e a γ y)) := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    exact annularCover_form_rep e a γ y v
  have hd := euclidean_manifold_pullback_exterior_at (handleAnnularCover_smoothAt e a hq) hγ
  have hA : ContDiffAt ℝ ∞ (annularCoverA e a γ) q := hs.clm_apply contDiffAt_const
  have hB : ContDiffAt ℝ ∞ (annularCoverB e a γ) q := hs.clm_apply contDiffAt_const
  rw [he,planarCovector_exterior_at hA hB] at hd
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ => Ω (1,0) (0,1)) hd
  simp only [smul_apply,smul_eq_mul,planarArea_apply,mul_one,mul_zero,sub_zero,
    manifoldMapDifferential] at hv
  exact hv

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

@[simp] theorem handleAnnularCover_eq_densityChart
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) : handleAnnularCover e a = handleDensityChart e a := rfl

theorem handleAnnularCover_rectangle_domain
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a : ℝ} (ha : a < 1/2) (he : compactHandleBand a ⊆ e.source)
    {U : Set Plane} (hU : U ⊆ Ioo (-a) a ×ˢ Ioo (0:ℝ) 1) :
    U ⊆ annularCoverDomain e a := by
  intro q hq
  change cylinderCover q ∈ (handleAnnularChart e a).source
  rw [handleAnnularChart_source e ha he]
  exact ⟨(hU hq).1,mem_univ _⟩

theorem annularPackingChart_smoothOn
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) {U : Set (Plane × V)} (hU : ∀ p ∈ U, p.1 ∈ annularCoverDomain e a) :
    ContMDiffOn 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) ∞
      (flatProductMap (handleAnnularCover e a)) U := by
  intro p hp
  exact (flatProductMap_smoothAt (handleAnnularCover_smoothAt e a (hU p hp))).contMDiffWithinAt

omit [NormedSpace ℝ V] in
theorem annularPackingChart_isEmbedding
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a : ℝ} (ha : a < 1/2) (he : compactHandleBand a ⊆ e.source)
    {U : Set (Plane × V)} (hU : ∀ p ∈ U, p.1 ∈ Ioo (-a) a ×ˢ Ioo (0:ℝ) 1) :
    Topology.IsEmbedding (fun p : U => flatProductMap (handleAnnularCover e a) p.val) := by
  let c := (handleDensityChart e a).toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl V)
  have hsub : U ⊆ c.source := by
    intro p hp
    change p.1 ∈ (handleDensityChart e a).source ∧ p.2 ∈ (univ : Set V)
    rw [handleDensityChart_source e ha he]
    exact ⟨hU p hp,mem_univ _⟩
  exact c.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hsub)

variable {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def annularUnshearMap
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) : Plane × V → M × V :=
  flatProductMap (handleAnnularCover e a) ∘
    (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)).symm

@[simp] theorem annularUnshearMap_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (p : Plane × V) :
    annularUnshearMap e a b Φ p =
      (handleAnnularCover e a p.1,(Φ.map (intervalClock (-b) b p.1.1)).symm p.2) := rfl

theorem annularUnshearMap_smoothOn
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) {U : Set Plane}
    (hU : U ⊆ annularCoverDomain e a) :
    ContMDiffOn 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) ∞
      (annularUnshearMap e a b Φ) (U ×ˢ (univ : Set V)) := by
  intro p hp
  exact ((flatProductMap_smoothAt (x := (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)).symm p)
    (handleAnnularCover_smoothAt e a (hU hp.1))).comp p
    (hamiltonianBaseShear_inverse_smooth Φ (intervalClock_smooth (-b) b)).contMDiff.contMDiffAt).contMDiffWithinAt

theorem annularUnshearMap_isEmbedding
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a : ℝ} (ha : a < 1/2) (he : compactHandleBand a ⊆ e.source)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) {U : Set Plane}
    (hU : U ⊆ Ioo (-a) a ×ˢ Ioo (0:ℝ) 1) :
    Topology.IsEmbedding (fun p : U ×ˢ (univ : Set V) => annularUnshearMap e a b Φ p.val) := by
  let D := hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)
  have hd : Topology.IsEmbedding (fun p : U ×ˢ (univ : Set V) => D.symm p.val) :=
    D.symm.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hm : ∀ p : U ×ˢ (univ : Set V),D.symm p.val ∈ U ×ˢ (univ : Set V) :=
    fun p => ⟨p.property.1,mem_univ _⟩
  have hc := annularPackingChart_isEmbedding e ha he (V := V)
    (U := U ×ˢ univ) (fun _ h => hU h.1)
  exact hc.comp (hd.codRestrict (U ×ˢ univ) hm)

theorem smoothHomeomorph_inverse_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₜ E) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) (p v : E) :
    fderiv ℝ e (e.symm p) (fderiv ℝ e.symm p v) = v := by
  have hd := fderiv_comp p (he.differentiable (by simp) _) (hi.differentiable (by simp) p)
  have hh : (e : E → E) ∘ e.symm = id := by funext x; exact e.apply_symm_apply x
  rw [hh,fderiv_id] at hd
  exact congrArg (fun L : E →L[ℝ] E => L v) hd.symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def annularUnshearMap
    (D : AnnularHandleData Plane M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) : Plane × V → M × V :=
  flatProductMap (D.handleAnnularCover) ∘
    (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)).symm

@[simp] theorem annularUnshearMap_apply
    (D : AnnularHandleData Plane M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (p : Plane × V) :
    annularUnshearMap D b Φ p =
      (D.handleAnnularCover p.1,(Φ.map (intervalClock (-b) b p.1.1)).symm p.2) := rfl

theorem annularUnshearMap_smoothOn
    (D : AnnularHandleData Plane M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) {U : Set Plane}
    (hU : U ⊆ D.annularCoverDomain) :
    ContMDiffOn 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) ∞
      (annularUnshearMap D b Φ) (U ×ˢ (univ : Set V)) := by
  intro p hp
  exact ((flatProductMap_smoothAt (x := (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)).symm p)
    (D.handleAnnularCover_smoothAt (hU hp.1))).comp p
    (hamiltonianBaseShear_inverse_smooth Φ (intervalClock_smooth (-b) b)).contMDiff.contMDiffAt).contMDiffWithinAt

theorem annularUnshearMap_isEmbedding
    (D : AnnularHandleData Plane M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) {U : Set Plane}
    (hU : U ⊆ Ioo (-D.width) D.width ×ˢ Ioo (0:ℝ) 1) :
    Topology.IsEmbedding (fun p : U ×ˢ (univ : Set V) => annularUnshearMap D b Φ p.val) := by
  let L := hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)
  have hd : Topology.IsEmbedding (fun p : U ×ˢ (univ : Set V) => L.symm p.val) :=
    L.symm.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hm : ∀ p : U ×ˢ (univ : Set V),L.symm p.val ∈ U ×ˢ (univ : Set V) :=
    fun p => ⟨p.property.1,mem_univ _⟩
  have hc := D.annularPackingChart_isEmbedding (V := V)
    (U := U ×ˢ univ) (fun _ h => hU h.1)
  exact hc.comp (hd.codRestrict (U ×ˢ univ) hm)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

 theorem homeomorph_mapsTo_interior {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ X) {Y : Set X} (hf : MapsTo e Y Y) (hi : MapsTo e.symm Y Y) :
    MapsTo e (interior Y) (interior Y) := by
  have he : e '' Y = Y := by
    apply Subset.antisymm (image_subset_iff.mpr hf)
    intro x hx
    exact ⟨e.symm x,hi hx,e.apply_symm_apply x⟩
  have hI : e '' interior Y = interior Y := by rw [e.image_interior,he]
  intro x hx
  rw [←hI]
  exact ⟨x,hx,rfl⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

 theorem handleAnnularCover_mem_band
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) {p : Plane} (hp : p.1 ∈ Icc (-b) b) :
    handleAnnularCover e a p ∈ e '' compactHandleBand b := by
  exact ⟨torusAnnulusMap (cylinderCover p),⟨cylinderCover p,⟨hp,mem_univ _⟩,rfl⟩,rfl⟩

 theorem annularUnshearMap_mem_interior
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) {Y : Set V} {D : Set M}
    (hbase : e '' compactHandleBand b ⊆ interior D)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) Y Y ∧ MapsTo (Φ.map t).symm Y Y)
    {p : Plane × V} (hp : p.1.1 ∈ Icc (-b) b) (hv : p.2 ∈ interior Y) :
    annularUnshearMap e a b Φ p ∈ interior (D ×ˢ Y) := by
  rw [interior_prod_eq]
  refine ⟨hbase (handleAnnularCover_mem_band e a b hp),?_⟩
  have ht : intervalClock (-b) b p.1.1 ∈ Icc (0:ℝ) 1 :=
    intervalClock_bounds _ _ _
  exact homeomorph_mapsTo_interior (Φ.map _).symm (hΦ _ ht).2 (hΦ _ ht).1 hv

end PackingSufficiencySupport.Hamiltonian
end

end OAI
