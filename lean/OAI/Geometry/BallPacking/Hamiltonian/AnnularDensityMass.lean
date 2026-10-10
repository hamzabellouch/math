import Mathlib
import OAI.Geometry.BallPacking.SurfaceArea.AnnularSecondPositivity
import OAI.Geometry.BallPacking.SurfaceArea.SurfaceRedistribution

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem densityChart_coefficient (H : AnnularHandleData Plane M) (b : ℝ) {y : Plane}
    (hy : y∈H.densityChart.source) :
    partialChartCoefficient H.densityChart (H.density b) y=
      deriv (intervalClock (-b) b) y.1*H.clock (circleTurn y.2) := by
  have hh := H.density_cover b hy.2 (1,0) (0,1)
  unfold partialChartCoefficient euclideanPullbackTwoForm
  have heq : (H.densityChart : Plane → M)=H.chart ∘ cylinderCover := rfl
  rw [heq]
  simpa only [mul_one, mul_zero, sub_zero] using! hh

omit [T2Space M] in
theorem density_nonnegative (H : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b)
    (hbw : b<H.width) (hor : PositivePartialChart H.densityChart) (c : M) {y : Plane}
    (hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    0≤chartTwoForm (H.density b) c y (1,0) (0,1) := by
  let d := H.densityChart
  let x := (extChartAt 𝓘(ℝ,Plane) c).symm y
  have hxc : x∈(extChartAt 𝓘(ℝ,Plane) c).source :=
    (extChartAt 𝓘(ℝ,Plane) c).map_target hy
  have hxy : extChartAt 𝓘(ℝ,Plane) c x=y :=
    (extChartAt 𝓘(ℝ,Plane) c).right_inv hy
  by_cases hx : x∈H.chart '' H.core b
  · have hxd : x∈d.target := H.densityChart_contains hbw hx
    let z := d.symm x
    have hzs : z∈d.source := d.map_target hxd
    have hzx : d z=x := d.right_inv hxd
    have hzc : d z∈(extChartAt 𝓘(ℝ,Plane) c).source := hzx.symm ▸ hxc
    have hdet := hor c z hzs hzc
    have hcoef : 0≤partialChartCoefficient d (H.density b) z := by
      rw [H.densityChart_coefficient b hzs]
      exact mul_nonneg (intervalClock_deriv_nonneg (by linarith) _) (H.clock_nonneg _)
    have hchange := partialChartCoefficient_change d (Ω := H.density b)
      (manifoldWedge_skew _ _) hzs hzc
    have hcy : extChartAt 𝓘(ℝ,Plane) c (d z)=y := (congrArg _ hzx).trans hxy
    rw [hchange,hcy] at hcoef
    exact nonneg_of_mul_nonneg_right hcoef hdet
  · have hz := H.density_core_zero hb hbw hx
    unfold chartTwoForm
    change 0≤((H.density b x).bilinearComp _ _) (1,0) (0,1)
    rw [hz]
    rfl

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem rectangle_integral (H : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<H.width) :
    (∫ y in Ioo (-H.width) H.width ×ˢ Ioo (0:ℝ) 1,
      deriv (intervalClock (-b) b) y.1*H.clock (circleTurn y.2))=1 := by
  have hr : (∫ s in -H.width..H.width,deriv (intervalClock (-b) b) s)=1 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun s _ => (intervalClock_smooth (-b) b).differentiable (by simp) s)
      ((intervalClock_deriv_smooth (-b) b).continuous.intervalIntegrable _ _)]
    rw [intervalClock_one (by linarith : -b<b) hbw.le,
      intervalClock_zero (by linarith : -b<b) (by linarith)]
    norm_num
  rw [Measure.volume_eq_prod,setIntegral_prod_mul
    (fun s => deriv (intervalClock (-b) b) s) (fun t => H.clock (circleTurn t)),
    ← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : -H.width≤H.width),
    hr,one_mul,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  exact H.clock_integral

theorem density_mass (H : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<H.width)
    (hor : PositivePartialChart H.densityChart)
    {I : Type*} [Fintype I] (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M (H.chart '' H.core b))
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) :
    partitionFormMass B ρ (H.density b)=1 := by
  let d := H.densityChart
  let K := H.chart '' H.core b
  let R := Ioo (-H.width) H.width ×ˢ Ioo (0:ℝ) 1
  have hK : IsCompact K := H.image_core_compact hbw
  have hKe : K⊆d.target := H.densityChart_contains hbw
  have hsrc : d.source=R := H.densityChart_source
  have hsub : d.symm '' K⊆R := by
    rintro y ⟨x,hx,rfl⟩
    rw [← hsrc]
    exact d.map_target (hKe hx)
  have heq := partitionFormMass_eq_partialChart_integral d hor hK hKe B ρ hρ
    (H.density_smooth hb hbw) (manifoldWedge_skew _ _) (fun _ hx => H.density_core_zero hb hbw hx)
  rw [heq]
  have hlarge : (∫ y in R,partialChartCoefficient d (H.density b) y)=
      ∫ y in d.symm '' K,partialChartCoefficient d (H.density b) y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_Ioo.prod isOpen_Ioo).measurableSet hsub
    intro y hy
    have hys : y∈d.source := hsrc.symm ▸ hy.1
    have hn : d y∉K := by
      intro hk
      exact hy.2 ⟨d y,hk,d.left_inv hys⟩
    have hz := H.density_core_zero hb hbw hn
    simp only [partialChartCoefficient,euclideanPullbackTwoForm,hz]
    rfl
  rw [← hlarge]
  calc
    _ = ∫ y in R,deriv (intervalClock (-b) b) y.1*H.clock (circleTurn y.2) := by
      apply setIntegral_congr_fun (isOpen_Ioo.prod isOpen_Ioo).measurableSet
      intro y hy
      exact H.densityChart_coefficient b (hsrc.symm ▸ hy)
    _ = 1 := H.rectangle_integral hb hbw

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K : Set M}

theorem exists_surface_step_two
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
    (D : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (heK : closure D.chart.target⊆interior K) (hβK : tsupport D.dual⊆interior K)
    (heor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {c : P × M → ℝ} (hs : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ c)
    {Y : Set P} (hY : IsCompact Y) (hcp : ∀ p∈Y,∀ x∈K,0<c (p,x))
    {Γ₀ : P → ManifoldOneForm Plane M} (hΓ₀ : SmoothOneFormFamily Γ₀)
    (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=c (p,x) • Λ x)
    {A : P → ℝ} {ε : ℝ} (hε : 0<ε) (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-A p|<ε) :
    ∃ (q : ℝ) (s : P × M → ℝ) (H : P → ℝ)
      (Γ₁ : P → ManifoldOneForm Plane M) (γ : ManifoldOneForm Plane M) (L W : Set M),
      0<q ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ s ∧ ContDiff ℝ ∞ H ∧
      (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-
        restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)) ∧
      (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
      SmoothOneFormFamily Γ₁ ∧ IsCompact L ∧ L⊆interior K ∧ IsOpen W ∧
      D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
      (∀ p x,x∉L→Γ₁ p x=Γ₀ p x) ∧
      (∀ p x,x∈K→manifoldExteriorOneForm (Γ₁ p) x=
        s (p,x) • Λ x+H p • D.density b x) ∧
      (∀ p∈Y,∀ z y,y∈(extChartAt 𝓘(ℝ,Plane) z).target→
        (extChartAt 𝓘(ℝ,Plane) z).symm y∈K→
        0<chartTwoForm (manifoldExteriorOneForm (Γ₁ p)) z y (1,0) (0,1)) ∧
      (∀ p x,x∈D.chart.target→s (p,x)=q) ∧
      (∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x)) ∧
      (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
      (∀ p,∀ x∈W,Γ₁ p x=γ x+
        (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) ∧
      (∀ p∈Y,∀ x∈K,0<s (p,x)) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)<ε) ∧
      (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→s (p,x)=c (p,x)) := by
  let Z := closure D.chart.target
  have hdis : Disjoint (frontier K) Z := disjoint_interior_frontier.symm.mono_right heK
  have hAK : D.chart.target⊆interior K := subset_closure.trans heK
  let T := D.chart '' D.core b
  have hT : IsCompact T := D.image_core_compact hbw
  have hTK : T⊆interior K := by
    rintro _ ⟨z,hz,rfl⟩
    exact hAK (D.chart.map_source (D.band_subset_source hbw (D.core_subset_band b hz)))
  have hmass : partitionFormMass B ρ (D.density b)=1 :=
    D.density_mass hb hbw heor B
      (restrictSurfacePartition ρ (hTK.trans interior_subset))
      (restrictSurfacePartition_subordinate ρ _ hρ)
  obtain ⟨q,s,H,Ξ,hq,hs',hH,hΞ,hm,hbound,hform,hpos,hsZ,hprim,hsp,hsarea,hscollar⟩ :=
    exists_surface_area_redistribution hK hc hne hor B ρ hρ hnull isClosed_closure hdis
      hΛ hsΛ hpΛ hs hY hcp
      (D.density_smooth hb hbw)
      (manifoldWedge_skew _ _)
      (fun z y hy => D.density_nonnegative hb hbw heor z hy)
      hT hTK (fun _ hx => D.density_core_zero hb hbw hx) hmass hε hA herr
  have hAZ : D.chart.target⊆Z := subset_closure
  have hNF (p : P) (x : M) (hx : x∈D.chart.target) :
      c (p,x) • Λ x+Ξ p x=q • Λ x+H p • D.density b x := by
    rw [hform p x (interior_subset (hAK hx)),hsZ p x (hAZ hx)]
  obtain ⟨Γ₁,γ,L,W,hΓ₁,hL,hLK,hW,hBW,hWA,haway,hdΓ₁,hγ,hdγ,hN⟩ :=
    D.exists_normalized_surface_primitive hbw hAK hβK
      hΛ hsΛ hH hΓ₀ hdΓ₀ hprim hNF
  refine ⟨q,s,H,Γ₁,γ,L,W,hq,hs',hH,hm,hbound,hΓ₁,hL,hLK,hW,hBW,hWA,haway,
    (fun p x hx => (hdΓ₁ p x).trans (hform p x hx)),?_,
    (fun p x hx => hsZ p x (hAZ hx)),hγ,hdγ,hN,hsp,hsarea,hscollar⟩
  intro p hp z y hy hk
  have heq : manifoldExteriorOneForm (Γ₁ p)=fun x => c (p,x) • Λ x+Ξ p x := funext (hdΓ₁ p)
  rw [heq]
  exact hpos p hp z y hy hk

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

 theorem exists_surface_normal_form_packing {m N : ℕ}
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hb : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (hor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0<chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {ε : ℝ} (hε : 0<ε)
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=ε • Λ x)
    {Γ : (Fin m  →  ℝ)  →  ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {K H : (Fin m  →  ℝ)  →  ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {Y V : Set (Fin m  →  ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M} (heD : D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
    (hΓpos : ∀ p∈Y,∀ x∈Kbase,0<chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W → Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hV : IsOpen (planeMoments ⁻¹' V)) (hVY : V⊆Y)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    (h : Fin N  →  (Fin m  →  ℝ)  →  ℝ) (hh : ∀ i,ContDiff ℝ ∞ (h i))
    (hhp : ∀ i p,p∈Y → 0≤h i p)
    (hres : ∀ v,planeMoments v∈Y → 0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
      (fun j => h j ∘ planeMoments) (Φ.map 1).symm v)
    (r r' : Fin N  →  ℝ) (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → (∑ j,p j)≤r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → p∈V → r i-(∑ j,p j)≤h i p)
    {J : Type*} (F : J  →  (Fin m  →  ℝ)  →  ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J  →  ℝ) (hαc : ∀ j,α j<c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v≤c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
    ∃ φ : Fin N  →  Ambient (m+1)  →  M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ (planeMoments ⁻¹' Y)))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  have hbase : D.chart '' band b⊆interior Kbase :=
    (D.image_band_subset_target hbw).trans heD
  obtain ⟨ρ,hρ,hρpos,hlo,hhi,φ,hφ,him,hdis⟩ := exists_global_surface_final_packing D hb hbw hδ hsmall
    hor hclock hΛ hsΛ hpΛ hε hγ hdγ hΓ hK hH hbase hW hBW hN Φ hV hVY hΦ h hh
    (fun i p hp => hhp i p (hVY hp)) r r' hr' hrr hsimplex hheight
  obtain ⟨ψ₂,hD₂,hI₂,hform₂,_,_⟩ := globalSurfaceSecondPath_moser_endpoint D hb hbw hor
    hΛ hsΛ hpΛ hε hγ hdγ hΓ hK hH hHp heD hβD hΓpos hW hBW hWA hN Φ hΦ
    (fun i => (hh i).comp planeMoments_smooth) (fun i => hρ i.castSucc) (hρ (Fin.last N))
    (fun s hs => ⟨fun i => hlo s hs i.castSucc,hlo s hs _⟩)
    (fun s hs => ⟨fun i => hhi s hs i.castSucc,hhi s hs _⟩)
    (fun i => hρpos i.castSucc) (hρpos (Fin.last N)) (fun v hv i => hhp i _ hv) hres
    F hF α c hαc hYeq hYC hzero (fun j i => toric_collarInvariant (hF j) (hh i) (α j))
  obtain ⟨hφ₁,him₁,hd₁⟩ := transport_form_packing (fun i => closedBall (m+1) (r' i))
    (fun _ => successorStandardForm m) _ _ ψ₂ hform₂ hD₂ hI₂ φ hφ him hdis
  obtain ⟨ψ₁,hD₁,hI₁,hform₁,_,_⟩ := globalSurfaceFirstPath_moser_endpoint D hb hbw hor
    hΛ hsΛ hpΛ hε hγ hdγ hΓ hH hHp heD hΓpos hW hBW hWA hN Φ hΦ F hF α c hαc hYeq hYC hzero
  obtain ⟨hφ₀,him₀,hd₀⟩ := transport_form_packing (fun i => closedBall (m+1) (r' i))
    (fun _ => successorStandardForm m) _ _ ψ₁ hform₁ hD₁ hI₁ (fun i => ψ₂.symm ∘ φ i) hφ₁ him₁ hd₁
  exact ⟨fun i => ψ₁.symm ∘ (ψ₂.symm ∘ φ i),hφ₀,him₀,hd₀⟩

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def toricPrimitiveInterpolation (Γ₀ Γ₁ : P → ManifoldOneForm E M)
    (q : ℝ × P) : ManifoldOneForm E M := (1-q.1) • Γ₀ q.2+q.1 • Γ₁ q.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem toricPrimitiveInterpolation_zero (Γ₀ Γ₁ : P → ManifoldOneForm E M) (p : P) :
    toricPrimitiveInterpolation Γ₀ Γ₁ (0,p)=Γ₀ p := by simp [toricPrimitiveInterpolation]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem toricPrimitiveInterpolation_one (Γ₀ Γ₁ : P → ManifoldOneForm E M) (p : P) :
    toricPrimitiveInterpolation Γ₀ Γ₁ (1,p)=Γ₁ p := by simp [toricPrimitiveInterpolation]

theorem toricPrimitiveInterpolation_smooth {Γ₀ Γ₁ : P → ManifoldOneForm E M}
    (h₀ : SmoothOneFormFamily Γ₀) (h₁ : SmoothOneFormFamily Γ₁) :
    SmoothOneFormFamily (toricPrimitiveInterpolation Γ₀ Γ₁) :=
  ((h₀.comp contDiff_snd).smul (contDiff_const.sub contDiff_fst)).add
    ((h₁.comp contDiff_snd).smul contDiff_fst)

theorem toricPrimitiveInterpolation_exterior [IsManifold 𝓘(ℝ,E) ∞ M]
    {Γ₀ Γ₁ : P → ManifoldOneForm E M} (h₀ : SmoothOneFormFamily Γ₀)
    (h₁ : SmoothOneFormFamily Γ₁) (t : ℝ) (p : P) (x : M) :
    manifoldExteriorOneForm (toricPrimitiveInterpolation Γ₀ Γ₁ (t,p)) x=
      (1-t) • manifoldExteriorOneForm (Γ₀ p) x+t • manifoldExteriorOneForm (Γ₁ p) x := by
  have hx := (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source (I := 𝓘(ℝ,E)) x)
  have hc₀ := h₀.spatial_smooth p x hx
  have hc₁ := h₁.spatial_smooth p x hx
  have hs₀ : ContDiffAt ℝ ∞ (chartOneForm ((1-t) • Γ₀ p) x) (extChartAt 𝓘(ℝ,E) x x) := by
    rw [show chartOneForm ((1-t) • Γ₀ p) x=fun y => (1-t) • chartOneForm (Γ₀ p) x y
      from funext (chartOneForm_smul (1-t) (Γ₀ p) x)]
    exact hc₀.const_smul (1-t)
  have hs₁ : ContDiffAt ℝ ∞ (chartOneForm (t • Γ₁ p) x) (extChartAt 𝓘(ℝ,E) x x) := by
    rw [show chartOneForm (t • Γ₁ p) x=fun y => t • chartOneForm (Γ₁ p) x y
      from funext (chartOneForm_smul t (Γ₁ p) x)]
    exact hc₁.const_smul t
  exact (manifoldExteriorOneForm_add_at hs₀ hs₁).trans
    (congrArg₂ (Add.add (α := E →L[ℝ] E →L[ℝ] ℝ))
      (manifoldExteriorOneForm_smul_at (1-t) hc₀)
      (manifoldExteriorOneForm_smul_at t hc₁))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {N : Type*} [TopologicalSpace N] [ChartedSpace Plane N] [IsManifold 𝓘(ℝ,Plane) ∞ N]

theorem toricPrimitiveInterpolation_isInvertible
    {Γ₀ Γ₁ : (ι → ℝ) → ManifoldOneForm Plane N}
    (h₀ : SmoothOneFormFamily Γ₀) (h₁ : SmoothOneFormFamily Γ₁)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (z : N × PlanePhase ι)
    (hp₀ : 0<chartTwoForm (manifoldExteriorOneForm (Γ₀ (planeMoments z.2)))
      z.1 (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1))
    (hp₁ : 0<chartTwoForm (manifoldExteriorOneForm (Γ₁ (planeMoments z.2)))
      z.1 (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (fun v => toricPrimitiveInterpolation Γ₀ Γ₁ (t,planeMoments v)) z).IsInvertible := by
  apply globalToricCoupling_isInvertible
    ((toricPrimitiveInterpolation_smooth h₀ h₁).comp
      (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun p : ι → ℝ => p))))
  have he : manifoldExteriorOneForm (toricPrimitiveInterpolation Γ₀ Γ₁ (t,planeMoments z.2))=
      (1-t) • manifoldExteriorOneForm (Γ₀ (planeMoments z.2))+
        t • manifoldExteriorOneForm (Γ₁ (planeMoments z.2)) :=
    funext (toricPrimitiveInterpolation_exterior h₀ h₁ t (planeMoments z.2))
  dsimp only [Function.comp_apply,id_eq]
  rw [he,chartTwoForm_add,chartTwoForm_smul,chartTwoForm_smul]
  change 0<(1-t)*_+t*_
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hp₀) (mul_nonneg ht.1 hp₁.le)
  · simpa using hp₁

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem toric_redistribution_moser
    {Γ₀ Γ₁ : (ι → ℝ) → ManifoldOneForm Plane M}
    (h₀ : SmoothOneFormFamily Γ₀) (h₁ : SmoothOneFormFamily Γ₁)
    {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
    (hstation : ∀ x,x∉S→∀ p,Γ₁ p x=Γ₀ p x)
    {Y : Set (ι → ℝ)}
    (hp₀ : ∀ p∈Y,∀ x∈D,0<chartTwoForm (manifoldExteriorOneForm (Γ₀ p))
      x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    (hp₁ : ∀ p∈Y,∀ x∈D,0<chartTwoForm (manifoldExteriorOneForm (Γ₁ p))
      x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j<c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v≤c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y)) :
    ∃ ψ : (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ,Plane × PlanePhase ι),𝓘(ℝ,Plane × PlanePhase ι)⟯ (M × PlanePhase ι),
      ψ '' (D ×ˢ (planeMoments ⁻¹' Y))=D ×ˢ (planeMoments ⁻¹' Y) ∧
      ψ '' interior (D ×ˢ (planeMoments ⁻¹' Y))=interior (D ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn ψ (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments))
        (globalHorizontalCoupling phaseArea (Γ₁ ∘ planeMoments)) (D ×ˢ (planeMoments ⁻¹' Y)) ∧
      (∃ C : Set (M × PlanePhase ι),IsCompact C ∧ ∀ z,z∉C→ψ z=z) ∧
      (∀ z,z.1∉S→ψ z=z) := by
  have hdom : {v | ∀ j,F j (planeMoments v)≤c j}=planeMoments ⁻¹' Y := hYeq.symm
  have hsmooth := toricPrimitiveInterpolation_smooth h₀ h₁
  have hparam : ∀ t x,ContDiff ℝ ∞ (fun p => toricPrimitiveInterpolation Γ₀ Γ₁ (t,p) x) := by
    intro t x
    exact (contDiff_iff_contDiffAt.mpr (fun q => hsmooth.parameter_contDiffAt q x)).comp
      (contDiff_const.prodMk contDiff_id)
  obtain ⟨ψ,hD,hI,hp,hC,hfix⟩ := horizontal_moser_endpoint phaseArea_isInvertible phaseArea_skew
    (hsmooth.comp (contDiff_fst.prodMk (planeMoments_smooth.comp contDiff_snd))) hS hSD
    (fun x hx t v => by
      simp only [Function.comp_apply,toricPrimitiveInterpolation,Pi.add_apply,Pi.smul_apply,
        hstation x hx,←add_smul]
      congr 1; ring)
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => toric_collarInvariant (hF j) (hparam t x) (α j))
    (fun t ht z hz => toricPrimitiveInterpolation_isInvertible h₀ h₁ ht z
      (hp₀ _ (by exact (show z.2∈planeMoments ⁻¹' Y from hYeq.symm ▸ hz.2)) _ hz.1)
      (hp₁ _ (by exact (show z.2∈planeMoments ⁻¹' Y from hYeq.symm ▸ hz.2)) _ hz.1))
  refine ⟨ψ,?_,?_,?_,hC,hfix⟩
  · simpa only [←hYeq] using hD
  · simpa only [←hYeq] using hI
  · simp only [Function.comp_apply,toricPrimitiveInterpolation_zero,
      toricPrimitiveInterpolation_one,hdom] at hp
    convert hp using 1 <;> rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I]

 theorem exists_surface_initial_packing {m N : ℕ} {Kbase : Set M}
    (hD : IsCompact Kbase) (hcD : IsPreconnected (interior Kbase)) (hne : (interior Kbase).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (π : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M Kbase)
    (hπ : π.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier Kbase)=0)
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hb : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (heD : closure D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
    (heor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target →
      0<chartTwoForm Λ c y (1,0) (0,1))
    {d : (Fin m → ℝ) × M → ℝ}
    (hd : ContMDiff (𝓘(ℝ,Fin m → ℝ).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d)
    {Y V : Set (Fin m → ℝ)} (hY : IsCompact Y) (hdp : ∀ p∈Y,∀ x∈Kbase,0<d (p,x))
    {Γ₀ : (Fin m → ℝ) → ManifoldOneForm Plane M} (hΓ₀ : SmoothOneFormFamily Γ₀)
    (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=d (p,x) • Λ x)
    {A : (Fin m → ℝ) → ℝ} {ε : ℝ} (hε : 0<ε) (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B π Kbase (fun x => d (p,x) • Λ x)-A p|<ε)
    {K : (Fin m → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hV : IsOpen (planeMoments ⁻¹' V)) (hVY : V⊆Y)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    (h : Fin N → (Fin m → ℝ) → ℝ) (hh : ∀ i,ContDiff ℝ ∞ (h i))
    (hhp : ∀ i p,p∈Y → 0≤h i p)
    (hres : ∀ H : (Fin m → ℝ) → ℝ,(∀ p∈Y,|H p-A p|<2*ε) →
      ∀ v,planeMoments v∈Y → 0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
        (fun j => h j ∘ planeMoments) (Φ.map 1).symm v)
    (r r' : Fin N → ℝ) (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j)≤r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i-(∑ j,p j)≤h i p)
    {J : Type*} (F : J → (Fin m → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j<c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v≤c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
    ∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ (planeMoments ⁻¹' Y)))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨q,s,H,Γ₁,γ,L,W,hq,_,hH,_,hbound,hΓ₁,hL,hLD,hW,hBW,hWA,haway,_,hpos,_,hγ,hdγ,hN,_⟩ :=
    exists_surface_step_two hD hcD hne hor B π hπ hnull D hb hbw heD hβD heor hΛ hsΛ hpΛ
      hd hY hdp hΓ₀ hdΓ₀ hε hA herr
  have hΓ₁pos : ∀ p∈Y,∀ x∈Kbase,0<chartTwoForm (manifoldExteriorOneForm (Γ₁ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) := by
    intro p hp x hx
    exact hpos p hp x _ (mem_extChartAt_target x) (by simpa using hx)
  obtain ⟨φ,hφ,him,hdis⟩ := exists_surface_normal_form_packing D hb hbw hδ hsmall heor hclock
    hΛ hsΛ hpΛ hq hγ hdγ hΓ₁ hK hH (fun p hp => (hbound p hp).1.le) (subset_closure.trans heD) hβD hΓ₁pos hW hBW hWA hN
    Φ hV hVY hΦ h hh hhp (hres H (fun p hp => (hbound p hp).2)) r r' hr' hrr hsimplex hheight
    F hF α c hαc hYeq hYC hzero
  have hp₀ : ∀ p∈Y,∀ x∈Kbase,0<chartTwoForm (manifoldExteriorOneForm (Γ₀ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) := by
    intro p hp x hx
    have heq : manifoldExteriorOneForm (Γ₀ p)=fun x => d (p,x) • Λ x := funext (hdΓ₀ p)
    rw [heq,chartTwoForm_spatial_smul]
    change 0<d (p,(extChartAt 𝓘(ℝ,Plane) x).symm (extChartAt 𝓘(ℝ,Plane) x x))*
      chartTwoForm Λ x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)
    simpa using mul_pos (hdp p hp x hx) (hpΛ x _ (mem_extChartAt_target x))
  obtain ⟨ψ,hDψ,hIψ,hform,_,_⟩ := toric_redistribution_moser hΓ₀ hΓ₁ hL hLD
    (fun x hx p => haway p x hx) hp₀ hΓ₁pos F hF α c hαc hYeq hYC
  obtain ⟨hφ₀,him₀,hdis₀⟩ := transport_form_packing (fun i => closedBall (m+1) (r' i))
    (fun _ => successorStandardForm m) _ _ ψ hform hDψ hIψ φ hφ him hdis
  exact ⟨fun i => ψ.symm ∘ φ i,hφ₀,him₀,hdis₀⟩

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

structure PlanarHamiltonianMotion (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] where
  hamiltonian : (P × ℝ) × Plane → ℝ
  smooth : ContDiff ℝ ∞ hamiltonian
  compact : HasCompactSupport hamiltonian
  trace : P → ℝ → Plane → Plane
  continuous : Continuous (fun p : (P × ℝ) × Plane => trace p.1.1 p.1.2 p.2)
  zero : ∀ y x, trace y 0 x = x
  flow : ∀ y t x, HasDerivAt (fun s => trace y s x)
    (planarHamiltonianField (fderiv ℝ (fun z => hamiltonian ((y,t),z)) (trace y t x))) t

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def HamiltonianDiskIsotopyFamily.motion {R : ℝ} (Ψ : HamiltonianDiskIsotopyFamily P R) :
    PlanarHamiltonianMotion P where
  hamiltonian := Ψ.hamiltonian
  smooth := Ψ.smooth
  compact := Ψ.compact
  trace := fun y t x => Ψ.isotopy.map y t x
  continuous := Ψ.isotopy.smooth.continuous
  zero := fun y x => by rw [Ψ.isotopy.zero]; rfl
  flow := Ψ.flow

end PackingSufficiencySupport.Hamiltonian
end

end OAI
