import Mathlib
import OAI.Geometry.BallPacking.Models.DisjointClocks

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators Pointwise
open Set Function MeasureTheory
open Hamiltonian Comparison

theorem compact_positive_lower {X : Type*} [TopologicalSpace X]
    {D : Set X} (hc : IsCompact D) (hne : D.Nonempty) {f : X → ℝ}
    (hf : ContinuousOn f D) (hp : ∀ x ∈ D,0<f x) :
    ∃ g>0, ∀ x ∈ D,g ≤ f x := by
  obtain ⟨x,hx,hm⟩ := hc.exists_isMinOn hne hf
  exact ⟨f x,hp x hx,hm⟩

theorem inverse_comparison_gap {m N : ℕ}
    (b : Fin N → Moments m) (c : Fin N → ℝ) (hc : ∀ ν,0 ≤ c ν)
    (hcomp : IsCompact (region b c))
    (K P : Moments m → ℝ) (hK : Continuous K) (hP : ContinuousOn P (region b c))
    (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _))
    (hmem : ∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c)
    (hgap : ∀ z ∈ planeRegion b c,
      K (planeMoments (Φ.map 1 z))-P (planeMoments (Φ.map 1 z)) < K (planeMoments z)) :
    ∃ g>0, ∀ v ∈ planeRegion b c,
      g ≤ K (planeMoments ((Φ.map 1).symm v))-K (planeMoments v)+P (planeMoments v) := by
  apply compact_positive_lower (planeRegion_isCompact b c hcomp) (planeRegion_nonempty b c hc)
  · exact ((hK.comp (planeMoments_smooth.continuous.comp (Φ.map 1).symm.continuous)).continuousOn.sub
      (hK.comp planeMoments_smooth.continuous).continuousOn).add
      (hP.comp planeMoments_smooth.continuous.continuousOn (fun _ hv => hv))
  · intro v hv
    have hg := hgap ((Φ.map 1).symm v) ((hmem 1 _).1 (by simpa using hv))
    simp only [Homeomorph.apply_symm_apply] at hg
    linarith

theorem finite_surface_comparison {m N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j,0 ≤ b ν j) (hc : ∀ ν,0<c ν) (hcomp : IsCompact (region b c))
    (H : Moments m → ℝ) (hH : ContinuousOn H (region b c))
    (hHpos : ∀ p ∈ region b c,0<H p) (r : ι → ℝ)
    (hconc : ConcaveOn ℝ (region b c) (fun p => H p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0 < ∫ p in region b c,H p-∑ i,max (r i-∑ j,p j) 0)
    {τ a : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (ha : 0<a)
    (houter : ∀ p ∈ region b c,p ∉ τ • region b c → a ≤ H p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _))
      (g ε : ℝ) (h : ι → Moments m → ℝ),
      ContDiff ℝ ∞ K ∧ 0<g ∧ 0<ε ∧ 8*ε<g ∧
      (∀ p ∈ region b c,8*ε<H p) ∧
      (∀ i,ContDiff ℝ ∞ (h i)) ∧
      (∀ i p,max (r i-∑ j,p j) 0<h i p) ∧
      (∀ p,0<(∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0) ∧
        (∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0)<ε) ∧
      (∀ t z,Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ ν,∃ ρ>0,∀ t z,c ν-weightedMoment (b ν) z<ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0) ∧
      (∀ Hstar : Moments m → ℝ,(∀ p ∈ region b c,|Hstar p-H p|<2*ε) →
        (∀ p ∈ region b c,0<Hstar p) ∧
        ∀ v ∈ planeRegion b c,g/2 < surfaceRemainder (K ∘ planeMoments)
          (Hstar ∘ planeMoments) (fun i => h i ∘ planeMoments) (Φ.map 1).symm v) := by
  have hcap : Continuous (fun p : Moments m => ∑ i,max (r i-∑ j,p j) 0) := by fun_prop
  obtain ⟨K,Φ,hK,hmem,hgap,hface⟩ := positive_hamiltonian_comparison b c hb hc hcomp
    (fun p => H p-∑ i,max (r i-∑ j,p j) 0) (hH.sub hcap.continuousOn)
    hconc hmean hτ hτ1 ha houter
  obtain ⟨g,hg,hgall⟩ := inverse_comparison_gap b c (fun ν => (hc ν).le) hcomp K _
    hK.continuous (hH.sub hcap.continuousOn) Φ hmem hgap
  have hne : (region b c).Nonempty := by
    refine ⟨0,?_,?_⟩
    · intro j; simp
    · intro ν; simpa using (hc ν).le
  obtain ⟨u,hu,huall⟩ := compact_positive_lower hcomp hne hH hHpos
  let ε := min g u/16
  have hε : 0<ε := div_pos (lt_min hg hu) (by norm_num)
  have he1 : 8*ε<g := by dsimp [ε]; have := min_le_left g u; nlinarith [lt_min hg hu]
  have he2 : 8*ε<u := by dsimp [ε]; have := min_le_right g u; nlinarith [lt_min hg hu]
  obtain ⟨h,hhs,hhu,hhe⟩ := exists_smooth_positive_caps (κ := Fin m) r hε
  refine ⟨K,Φ,g,ε,h,hK,hg,hε,he1,(fun p hp => he2.trans_le (huall p hp)),hhs,hhu,hhe,hmem,hface,?_⟩
  intro Hstar hstar
  refine ⟨?_,?_⟩
  · intro p hp
    have hs := (abs_lt.mp (hstar p hp)).1
    have hu' := huall p hp
    linarith
  · intro v hv
    have hg' := hgall v hv
    simp only [Pi.sub_apply] at hg'
    have heq : g ≤ K (planeMoments ((Φ.map 1).symm v))-K (planeMoments v)+
        H (planeMoments v)-(∑ i,max (r i-∑ j,planeMoments v j) 0) := by linarith
    have hr := surfaceRemainder_gap (ψ := (Φ.map 1).symm)
      (K := K ∘ planeMoments) (H := Hstar ∘ planeMoments)
      (H₀ := H ∘ planeMoments) (C := fun v => ∑ i,max (r i-∑ j,planeMoments v j) 0)
      (h := fun i => h i ∘ planeMoments) heq (hstar _ hv) (hhe (planeMoments v)).2
    exact (by linarith : g/2<g-3*ε).trans hr

theorem finite_uniform_area_error {m : ℕ} {D : Set (Moments m)}
    {A : ℕ → Moments m → ℝ} {H : Moments m → ℝ}
    (hA : TendstoUniformlyOn A H Filter.atTop D) {ε : ℝ} (hε : 0<ε) :
    ∃ L : ℕ,∀ ℓ ≥ L,∀ p ∈ D,|A ℓ p-H p|<ε := by
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hA) ε hε)
  refine ⟨L,fun ℓ hℓ p hp => ?_⟩
  simpa only [Real.dist_eq,abs_sub_comm] using hL ℓ hℓ p hp

def strictRegion {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) : Set (Moments m) :=
  {p | (∀ j,0≤p j) ∧ ∀ ν,(∑ j,b ν j*p j)<c ν}

 theorem strictRegion_subset {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) :
    strictRegion b c⊆region b c := fun _ hp => ⟨hp.1,fun ν => (hp.2 ν).le⟩

 theorem strictRegion_phase_open {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) :
    IsOpen (planeMoments ⁻¹' strictRegion b c) := by
  have he : planeMoments ⁻¹' strictRegion b c = ⋂ ν,{z | weightedMoment (b ν) z<c ν} := by
    ext z
    simp only [mem_preimage,strictRegion,mem_ofPred_eq,mem_iInter]
    exact ⟨fun h => h.2,fun h => ⟨planeMoments_nonneg z,h⟩⟩
  rw [he]
  exact isOpen_iInter_of_finite (fun ν => isOpen_lt (weightedMoment_smooth (b ν)).continuous continuous_const)

 theorem planeRegion_outer_constraints {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) :
    planeMoments ⁻¹' region b c = {z | ∀ ν,(fun p => ∑ j,b ν j*p j) (planeMoments z)≤c ν} := by
  ext z
  change ((∀ j,0≤planeMoments z j) ∧ _) ↔ _
  exact ⟨fun h => h.2,fun h => ⟨planeMoments_nonneg z,h⟩⟩

 theorem momentFace_smooth {m : ℕ} (b : Moments m) :
    ContDiff ℝ ∞ (fun p : Moments m => ∑ j,b j*p j) := by fun_prop

 theorem face_collars_of_comparison {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hface : ∀ ν,∃ ρ>0,∀ t z,c ν-weightedMoment (b ν) z<ρ →
      fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0) :
    ∃ α : Fin N → ℝ,(∀ ν,α ν<c ν) ∧ ∀ ν t z,
      α ν<(fun p => ∑ j,b ν j*p j) (planeMoments z) →
      fderiv ℝ ((fun p => ∑ j,b ν j*p j) ∘ planeMoments) z
        (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0 := by
  classical
  choose ρ hρ hzero using hface
  refine ⟨fun ν => c ν-ρ ν,fun ν => sub_lt_self _ (hρ ν),?_⟩
  intro ν t z hz
  apply hzero ν t z
  change c ν-(∑ j,b ν j*planeMoments z j)<ρ ν
  linarith

 theorem comparison_preserves_region {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hmem : ∀ t z,Φ.map t z∈planeRegion b c ↔ z∈planeRegion b c) :
    ∀ t,MapsTo (Φ.map t) (planeMoments ⁻¹' region b c) (planeMoments ⁻¹' region b c) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' region b c) (planeMoments ⁻¹' region b c) := by
  intro t
  refine ⟨fun z hz => (hmem t z).2 hz,?_⟩
  intro z hz
  apply (hmem t ((Φ.map t).symm z)).1
  change planeMoments ((Φ.map t) ((Φ.map t).symm z))∈region b c
  rw [Homeomorph.apply_symm_apply]
  exact hz

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope.Annular
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Manifold MeasureTheory
open Hamiltonian Hamiltonian.AnnularHandleData

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]

 theorem surface_packing_tolerance {m q N : ℕ} [Nonempty (Fin N)]
    (bF : Fin q → Moments m) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0<cF ν) (hcomp : IsCompact (region bF cF))
    (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF))
    (hAp : ∀ p∈region bF cF,0<A p) (r r' : Fin N → ℝ)
    (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => A p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,A p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ ε>0,∀ {I : Type*} [Fintype I],∀ (Kbase : Set M) (_hD : IsCompact Kbase) (_hcD : IsPreconnected (interior Kbase))
      (_hne : (interior Kbase).Nonempty) (_hor : PositivePlaneTransitions M)
      (B : I → SurfaceCoordinateBox M) (π : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M Kbase),
      π.IsSubordinate (fun i => (B i).carrier) →
      (∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
        (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier Kbase)=0) →
      ∀ (D : AnnularHandleData Plane M)
      {b δ : ℝ}, 0<b → b<D.width → 0<δ → δ<1/2 →
      closure D.chart.target⊆interior Kbase → tsupport D.dual⊆interior Kbase →
      PositivePartialChart D.densityChart →
      D.clock=positiveCircleClock δ →
      ∀ {Λ : ManifoldTwoForm Plane M}, SmoothTwoForm Λ →
      (∀ x u v,Λ x u v= -Λ x v u) →
      (∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0<chartTwoForm Λ c y (1,0) (0,1)) →
      ∀ {d : Moments m × M → ℝ},
      ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d →
      (∀ p∈region bF cF,∀ x∈Kbase,0<d (p,x)) →
      ∀ {Γ₀ : Moments m → ManifoldOneForm Plane M}, SmoothOneFormFamily Γ₀ →
      (∀ p x,manifoldExteriorOneForm (Γ₀ p) x=d (p,x) • Λ x) →
      (∀ p∈region bF cF,|restrictedPartitionFormMass B π Kbase (fun x => d (p,x) • Λ x)-A p|<ε) →
      ∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
          (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ planeRegion bF cF))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨K,Φ,g,ε,h,hK,hg,hε,_,hAε,hh,hhcap,_,hmem,hfaceΦ,hres⟩ :=
    finite_surface_comparison bF cF hbF hcF hcomp A hA hAp r hconc hmean hτ hτ1 hd₀ houter
  obtain ⟨α,hαc,hzero⟩ := face_collars_of_comparison bF cF Φ hfaceΦ
  refine ⟨ε,hε,?_⟩
  intro I _ Kbase hD hcD hne hor B π hπ hnull D b δ hb hbw hδ hsmall heD hβD heor hclock
    Λ hΛ hsΛ hpΛ d hd hdp Γ₀ hΓ₀ hdΓ₀ herr
  have hSm : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r' i → p∈strictRegion bF cF := by
    intro i p hp hsum
    have hrp : (∑ j,p j)≤r i := hsum.trans (hrr i).le
    exact ⟨hp,fun ν => lt_of_le_of_ne ((hsimplex i p hp hrp).2 ν) (hface i p hp hrp ν)⟩
  exact exists_surface_initial_packing hD hcD hne hor B π hπ hnull D hb hbw hδ hsmall heD hβD heor hclock
    hΛ hsΛ hpΛ hd hcomp hdp hΓ₀ hdΓ₀ hε (fun p hp => by have := hAε p hp; linarith) herr
    hK Φ (strictRegion_phase_open bF cF) (strictRegion_subset bF cF)
    (fun t _ => comparison_preserves_region bF cF Φ hmem t) h hh
    (fun i p _ => (le_max_right _ _).trans (hhcap i p).le)
    (fun H hH v hv => (by linarith : (0:ℝ)<g/2).le.trans ((hres H hH).2 v hv).le)
    r r' hr' hrr hSm (fun i p _ _ => (le_max_left _ _).trans (hhcap i p).le)
    (fun ν p => ∑ j,bF ν j*p j) (fun ν => momentFace_smooth (bF ν)) α cF hαc
    (planeRegion_outer_constraints bF cF) (planeRegion_isCompact bF cF hcomp) hzero

 theorem intrinsic_surface_packing_tolerance {m q N : ℕ} [Nonempty (Fin N)]
    (bF : Fin q → Moments m) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0<cF ν) (hcomp : IsCompact (region bF cF))
    (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF))
    (hAp : ∀ p∈region bF cF,0<A p) (r r' : Fin N → ℝ)
    (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => A p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,A p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ ε>0,∀ (Kbase : Set M) (hD : IsCompact Kbase) (_hcD : IsPreconnected (interior Kbase))
      (_hne : (interior Kbase).Nonempty) (_hor : PositivePlaneTransitions M)
      (_hb : HasSmoothSurfaceBoundary Kbase),
      ∀ (D : AnnularHandleData Plane M)
      {b δ : ℝ}, 0<b → b<D.width → 0<δ → δ<1/2 →
      closure D.chart.target⊆interior Kbase → tsupport D.dual⊆interior Kbase →
      PositivePartialChart D.densityChart →
      D.clock=positiveCircleClock δ →
      ∀ {Λ : ManifoldTwoForm Plane M}, SmoothTwoForm Λ →
      (∀ x u v,Λ x u v= -Λ x v u) →
      (∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0<chartTwoForm Λ c y (1,0) (0,1)) →
      ∀ {d : Moments m × M → ℝ},
      ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d →
      (∀ p∈region bF cF,∀ x∈Kbase,0<d (p,x)) →
      ∀ {Γ₀ : Moments m → ManifoldOneForm Plane M}, SmoothOneFormFamily Γ₀ →
      (∀ p x,manifoldExteriorOneForm (Γ₀ p) x=d (p,x) • Λ x) →
      (∀ p∈region bF cF,|compactSurfaceFormIntegral hD (fun x => d (p,x) • Λ x)-A p|<ε) →
      ∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
          (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ planeRegion bF cF))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨ε,hε,hpack⟩ := surface_packing_tolerance (M := M) bF cF hbF hcF hcomp A hA hAp r r' hr' hrr
    hsimplex hface hconc hmean hτ hτ1 hd₀ houter
  refine ⟨ε,hε,?_⟩
  intro Kbase hD hcD hne hor hb D b δ hbp hbw hδ hsmall heD hβD heor hclock
    Λ hΛ hsΛ hpΛ d hd hdp Γ₀ hΓ₀ hdΓ₀ herr
  exact hpack Kbase hD hcD hne hor
    (fun B : compactSurfaceBoxes hD => B.1) (compactSurfacePartition hD)
    (compactSurfacePartition_subordinate hD)
    (fun B => smooth_surface_boundary_chart_null hD hb B.1.center)
    D hbp hbw hδ hsmall heD hβD heor hclock
    hΛ hsΛ hpΛ hd hdp hΓ₀ hdΓ₀ herr

 theorem exhausted_surface_packing {m q N : ℕ} [Nonempty (Fin N)]
    (bF : Fin q → Moments m) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0<cF ν) (hcomp : IsCompact (region bF cF))
    (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF))
    (hAp : ∀ p∈region bF cF,0<A p) (r r' : Fin N → ℝ)
    (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => A p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,A p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0)
    (Kbase : ℕ → Set M) (hD : ∀ ℓ,IsCompact (Kbase ℓ))
    (hmono : ∀ ℓ,Kbase ℓ⊆interior (Kbase (ℓ+1))) (hcover : (⋃ ℓ,Kbase ℓ)=univ)
    (hcD : ∀ ℓ,IsPreconnected (interior (Kbase ℓ))) (hne : ∀ ℓ,(interior (Kbase ℓ)).Nonempty)
    (hb : ∀ ℓ,HasSmoothSurfaceBoundary (Kbase ℓ)) (hor : PositivePlaneTransitions M)
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hbp : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (heor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0<chartTwoForm Λ c y (1,0) (0,1))
    (d : ℕ → Moments m × M → ℝ)
    (hd : ∀ ℓ,ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (d ℓ))
    (hdp : ∀ ℓ,∀ p∈region bF cF,∀ x∈Kbase ℓ,0<d ℓ (p,x))
    (Γ : ℕ → Moments m → ManifoldOneForm Plane M) (hΓ : ∀ ℓ,SmoothOneFormFamily (Γ ℓ))
    (hdΓ : ∀ ℓ p x,manifoldExteriorOneForm (Γ ℓ p) x=d ℓ (p,x) • Λ x)
    (hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (fun x => d ℓ (p,x) • Λ x)) A Filter.atTop (region bF cF)) :
    ∃ ℓ,∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ℓ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ℓ ×ˢ planeRegion bF cF))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨ε,hε,hpack⟩ := intrinsic_surface_packing_tolerance (M := M) bF cF hbF hcF hcomp
    A hA hAp r r' hr' hrr hsimplex hface hconc hmean hτ hτ1 hd₀ houter
  obtain ⟨L,hL⟩ := finite_uniform_area_error hlim hε
  have hmo : Monotone Kbase := monotone_nat_of_le_succ (fun ℓ => (hmono ℓ).trans interior_subset)
  have hco : (closure D.chart.target ∪ tsupport D.dual)⊆⋃ ℓ,interior (Kbase ℓ) := by
    intro x _
    obtain ⟨ℓ,hx⟩ := mem_iUnion.mp (show x∈⋃ ℓ,Kbase ℓ by rw [hcover]; trivial)
    exact mem_iUnion.mpr ⟨ℓ+1,hmono ℓ hx⟩
  obtain ⟨J,hJ⟩ := (D.compact_target.union D.dual_compact).elim_directed_cover (fun ℓ => interior (Kbase ℓ)) (fun _ => isOpen_interior)
    hco (fun i j => ⟨max i j,interior_mono (hmo (le_max_left i j)),
      interior_mono (hmo (le_max_right i j))⟩)
  refine ⟨max L J,?_⟩
  exact hpack (Kbase (max L J)) (hD _) (hcD _) (hne _) hor (hb _) D hbp hbw hδ hsmall
    ((subset_union_left).trans (hJ.trans (interior_mono (hmo (le_max_right L J)))))
    ((subset_union_right).trans (hJ.trans (interior_mono (hmo (le_max_right L J))))) heor hclock
    hΛ hsΛ hpΛ (hd _) (hdp _) (hΓ _) (hdΓ _) (hL _ (le_max_left L J))

end PackingSufficiencySupport.MomentPolytope.Annular

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def surfaceFormRatio (Λ Ω : ManifoldTwoForm Plane M) (x : M) : ℝ :=
  chartTwoForm Ω x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) /
    chartTwoForm Λ x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)

 theorem surface_form_scalar_in_chart {Λ Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v,Ω x u v= -Ω x v u) (hΛ : ∀ x u v,Λ x u v= -Λ x v u)
    {c x : M} (hx : x∈(extChartAt 𝓘(ℝ,Plane) c).source)
    (hpos : chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1)≠0) :
    Ω x=(chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) /
      chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1)) • Λ x := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω x u v=_*Λ x u v
  rw [← chartTwoForm_apply_chart hx u v (Ω := Ω),← chartTwoForm_apply_chart hx u v (Ω := Λ)]
  change chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (chartDifferential c x u) (chartDifferential c x v) =
    (chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) /
      chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1)) *
        chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (chartDifferential c x u) (chartDifferential c x v)
  rw [planar_skew_coefficient _ (chartTwoForm_skew hΩ _ _) (chartDifferential c x u) (chartDifferential c x v),
    planar_skew_coefficient _ (chartTwoForm_skew hΛ _ _) (chartDifferential c x u) (chartDifferential c x v)]
  field_simp [hpos]

 theorem surface_form_scalar {Λ Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v,Ω x u v= -Ω x v u) (hΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      0<chartTwoForm Λ c y (1,0) (0,1)) (x : M) :
    Ω x=surfaceFormRatio Λ Ω x • Λ x :=
  surface_form_scalar_in_chart hΩ hΛ (mem_extChartAt_source x)
    (ne_of_gt (hpos x _ (mem_extChartAt_target x)))

 theorem surfaceFormRatio_eq_chart {Λ Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v,Ω x u v= -Ω x v u) (hΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      0<chartTwoForm Λ c y (1,0) (0,1)) {c x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Plane) c).source) :
    surfaceFormRatio Λ Ω x=chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) /
      chartTwoForm Λ c (extChartAt 𝓘(ℝ,Plane) c x) (1,0) (0,1) := by
  have he : Ω=fun z => surfaceFormRatio Λ Ω z • Λ z :=
    funext (surface_form_scalar hΩ hΛ hpos)
  conv_rhs => rw [he,chartTwoForm_spatial_smul]
  simp only [smul_apply,smul_eq_mul,(extChartAt 𝓘(ℝ,Plane) c).left_inv hx]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (hpos c _ ((extChartAt 𝓘(ℝ,Plane) c).map_source hx)))).symm

 variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
 theorem surfaceFormRatio_smooth {Λ : ManifoldTwoForm Plane M}
    (hΛ : SmoothTwoForm Λ) (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0<chartTwoForm Λ c y (1,0) (0,1))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hsΩ : ∀ p x u v,Ω p x u v= -Ω p x v u) :
    ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × M => surfaceFormRatio Λ (Ω q.1) q.2) := by
  intro q
  let c := q.2
  let y := extChartAt 𝓘(ℝ,Plane) c c
  have hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target := mem_extChartAt_target c
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) c)).mem_nhds
    (show (q.1,y)∈univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target from ⟨mem_univ _,hy⟩)
  have hnum : ContDiffAt ℝ ∞ (fun z : P × Plane => chartTwoForm (Ω z.1) c z.2 (1,0) (0,1)) (q.1,y) :=
    (((hΩ c).contDiffAt hn).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hden : ContDiffAt ℝ ∞ (fun z : P × Plane => chartTwoForm Λ c z.2 (1,0) (0,1)) (q.1,y) :=
    ((((SmoothTwoFormFamily.const (P := P) hΛ) c).contDiffAt hn).clm_apply
      contDiffAt_const).clm_apply contDiffAt_const
  have hrat : ContDiffAt ℝ ∞ (fun z : P × Plane =>
      chartTwoForm (Ω z.1) c z.2 (1,0) (0,1)/chartTwoForm Λ c z.2 (1,0) (0,1)) (q.1,y) :=
    hnum.div hden (ne_of_gt (hpΛ c y hy))
  have hc : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (extChartAt 𝓘(ℝ,Plane) c) c :=
    contMDiffAt_extChartAt
  have hin : ContMDiffAt (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,P × Plane) ∞
      (fun z : P × M => (z.1,extChartAt 𝓘(ℝ,Plane) c z.2)) q :=
    contMDiffAt_fst.prodMk_space (hc.comp q contMDiffAt_snd)
  have hlocal := hrat.contMDiffAt.comp q hin
  apply hlocal.congr_of_eventuallyEq
  have hnsource : ∀ᶠ z : P × M in 𝓝 q,z.2∈(extChartAt 𝓘(ℝ,Plane) c).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds c)
  filter_upwards [hnsource] with z hz
  exact surfaceFormRatio_eq_chart (hsΩ z.1) hsΛ hpΛ hz

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope.Annular
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Manifold MeasureTheory
open Hamiltonian

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]

 theorem exhausted_curvature_surface_packing {m q N : ℕ} [Nonempty (Fin N)]
    (bF : Fin q → Moments m) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0<cF ν) (hcomp : IsCompact (region bF cF))
    (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF))
    (hAp : ∀ p∈region bF cF,0<A p) (r r' : Fin N → ℝ)
    (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j)≤r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => A p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,A p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0)
    (D : ℕ → Set M) (hD : ∀ ℓ,IsCompact (D ℓ))
    (hmono : ∀ ℓ,D ℓ⊆interior (D (ℓ+1))) (hcover : (⋃ ℓ,D ℓ)=univ)
    (hcD : ∀ ℓ,IsPreconnected (interior (D ℓ))) (hne : ∀ ℓ,(interior (D ℓ)).Nonempty)
    (hb : ∀ ℓ,HasSmoothSurfaceBoundary (D ℓ)) (hor : PositivePlaneTransitions M)
    (H : AnnularHandleData Plane M)
    {b δ : ℝ} (hbp : 0<b) (hbw : b<H.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (heor : PositivePartialChart H.densityChart)
    (hclock : H.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0<chartTwoForm Λ c y (1,0) (0,1))
    (Γ : ℕ → Moments m → ManifoldOneForm Plane M) (hΓ : ∀ ℓ,SmoothOneFormFamily (Γ ℓ))
    (hpos : ∀ ℓ,∀ p∈region bF cF,∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      (extChartAt 𝓘(ℝ,Plane) c).symm y∈D ℓ →
      0<chartTwoForm (manifoldExteriorOneForm (Γ ℓ p)) c y (1,0) (0,1))
    (hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (manifoldExteriorOneForm (Γ ℓ p))) A Filter.atTop (region bF cF)) :
    ∃ ℓ,∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ℓ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (D ℓ ×ˢ planeRegion bF cF))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  let κ : ℕ → Moments m → ManifoldTwoForm Plane M := fun ℓ p => manifoldExteriorOneForm (Γ ℓ p)
  have hκ ℓ : SmoothTwoFormFamily (κ ℓ) := manifoldExteriorOneForm_family_smooth (hΓ ℓ)
  have hsκ ℓ p x u v : κ ℓ p x u v= -κ ℓ p x v u := manifoldExteriorOneForm_skew _ _ _ _
  let d : ℕ → Moments m × M → ℝ := fun ℓ q => surfaceFormRatio Λ (κ ℓ q.1) q.2
  have hd ℓ : ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (d ℓ) :=
    surfaceFormRatio_smooth hΛ hsΛ hpΛ (hκ ℓ) (hsκ ℓ)
  have heq ℓ p x : κ ℓ p x=d ℓ (p,x) • Λ x := surface_form_scalar (hsκ ℓ p) hsΛ hpΛ x
  have hdp ℓ p (hp : p∈region bF cF) x (hx : x∈D ℓ) : 0<d ℓ (p,x) :=
    div_pos (hpos ℓ p hp x _ (mem_extChartAt_target x) (by simpa using hx))
      (hpΛ x _ (mem_extChartAt_target x))
  have hlim' : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (fun x => d ℓ (p,x) • Λ x)) A Filter.atTop (region bF cF) := by
    convert hlim using 1
    exact funext (fun ℓ => funext (fun p => congrArg (compactSurfaceFormIntegral (hD ℓ))
      (funext (fun x => (heq ℓ p x).symm))))
  exact exhausted_surface_packing bF cF hbF hcF hcomp A hA hAp r r' hr' hrr hsimplex hface
    hconc hmean hτ hτ1 hd₀ houter D hD hmono hcover hcD hne hb hor H hbp hbw hδ hsmall
    heor hclock hΛ hsΛ hpΛ d hd hdp Γ hΓ heq hlim'

end PackingSufficiencySupport.MomentPolytope.Annular
end

end OAI
