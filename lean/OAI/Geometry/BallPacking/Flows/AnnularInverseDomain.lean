import Mathlib
import OAI.Geometry.BallPacking.Annuli.AnnularEmbeddedChart

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

 theorem handleAnnularCover_mem_band
    (D : AnnularHandleData Plane M)
    (b : ℝ) {p : Plane} (hp : p.1 ∈ Icc (-b) b) :
    D.handleAnnularCover p ∈ D.chart '' band b := by
  exact ⟨cylinderCover p,⟨hp,mem_univ _⟩,rfl⟩

 theorem annularUnshearMap_mem_interior
    (D : AnnularHandleData Plane M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) {Y : Set V} {Kbase : Set M}
    (hbase : D.chart '' band b ⊆ interior Kbase)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) Y Y ∧ MapsTo (Φ.map t).symm Y Y)
    {p : Plane × V} (hp : p.1.1 ∈ Icc (-b) b) (hv : p.2 ∈ interior Y) :
    annularUnshearMap D b Φ p ∈ interior (Kbase ×ˢ Y) := by
  rw [interior_prod_eq]
  refine ⟨hbase (D.handleAnnularCover_mem_band b hp),?_⟩
  have ht : intervalClock (-b) b p.1.1 ∈ Icc (0:ℝ) 1 :=
    intervalClock_bounds _ _ _
  exact homeomorph_mapsTo_interior (Φ.map _).symm (hΦ _ ht).2 (hΦ _ ht).1 hv

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 def annularCoverTwoCoefficient
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) (Λ : ManifoldTwoForm Plane M) (q : Plane) : ℝ :=
  euclideanPullbackTwoForm (fun _ => Λ) (handleAnnularCover e a) (0,q) (1,0) (0,1)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
 theorem annularCoverDomain_eq
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a : ℝ} (ha : a<1/2) (he : compactHandleBand a⊆e.source) :
    annularCoverDomain e a=Ioo (-a) a ×ˢ univ := by
  rw [annularCoverDomain,handleAnnularChart_source e ha he]
  rfl

 theorem annularCoverTwoCoefficient_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) :
    ContDiffOn ℝ ∞ (annularCoverTwoCoefficient e a Λ) (annularCoverDomain e a) := by
  intro q hq
  have hs := euclideanPullbackTwoForm_contDiffAt (Ω := fun _ : ℝ => Λ)
    (g := handleAnnularCover e a) (p := (0,q))
    (SmoothTwoFormFamily.const (P := ℝ) hΛ) (handleAnnularCover_smoothAt e a hq)
  exact (((hs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).comp q
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
 theorem annularCoverTwoCoefficient_ne_zero
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    (a : ℝ) {Λ : ManifoldTwoForm Plane M}
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {q : Plane} (hq : q∈annularCoverDomain e a) :
    annularCoverTwoCoefficient e a Λ q≠0 := by
  intro hz
  let D := handleAnnularCoverLinearEquiv e a hq
  let B := (Λ (handleAnnularCover e a q)).bilinearComp (D : Plane →L[ℝ] Plane) (D : Plane →L[ℝ] Plane)
  have hB : ∀ u v,B u v= -B v u := fun u v => hs _ _ _
  have hB0 : B (1,0) (0,1)=0 := hz
  have hzero : Λ (handleAnnularCover e a q)=0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    have hv := planar_skew_coefficient B hB (D.symm u) (D.symm v)
    simpa only [B,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply,hB0,zero_mul,zero_apply] using hv
  let c := handleAnnularCover e a q
  have hc := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) c
  have hi := hp c (extChartAt 𝓘(ℝ,Plane) c c) ((extChartAt 𝓘(ℝ,Plane) c).map_source hc)
  have hcc : (extChartAt 𝓘(ℝ,Plane) c).symm (extChartAt 𝓘(ℝ,Plane) c c)=c :=
    (extChartAt 𝓘(ℝ,Plane) c).left_inv hc
  simp only [chartTwoForm,hcc,ContinuousLinearMap.bilinearComp_apply] at hi
  change 0<Λ (handleAnnularCover e a q) _ _ at hi
  rw [hzero] at hi
  exact (lt_irrefl 0) hi

 theorem annularCoverTwoCoefficient_positive
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a : ℝ} (ha : a<1/2) (he : compactHandleBand a⊆e.source)
    (hor : PositivePartialChart (handleDensityChart e a))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {q : Plane} (hq : q∈annularCoverDomain e a) :
    0<annularCoverTwoCoefficient e a Λ q := by
  let z : Plane := (q.1,1/2)
  have hsdom : q.1∈Ioo (-a) a := by
    rw [annularCoverDomain_eq e ha he] at hq
    exact hq.1
  have hz : z∈(handleDensityChart e a).source := by
    rw [handleDensityChart_source e ha he]
    exact ⟨hsdom,by norm_num [z]⟩
  have hzd : z∈annularCoverDomain e a := by
    rw [annularCoverDomain_eq e ha he]
    exact ⟨hsdom,mem_univ _⟩
  let c := handleDensityChart e a z
  have hc : handleDensityChart e a z∈(extChartAt 𝓘(ℝ,Plane) c).source := mem_extChartAt_source c
  have hpz : 0<annularCoverTwoCoefficient e a Λ z := by
    change 0<partialChartCoefficient (handleDensityChart e a) Λ z
    rw [partialChartCoefficient_change _ hs hz hc]
    exact mul_pos (hor c z hz hc) (hp c _ ((extChartAt 𝓘(ℝ,Plane) c).map_source hc))
  by_contra hn
  have hn' : annularCoverTwoCoefficient e a Λ q≤0 := le_of_not_gt hn
  have hconn : IsPreconnected (annularCoverDomain e a) := by
    rw [annularCoverDomain_eq e ha he]
    exact isPreconnected_Ioo.prod isPreconnected_univ
  obtain ⟨y,hy,hy0⟩ := hconn.intermediate_value hq hzd
    (annularCoverTwoCoefficient_smooth e a hΛ).continuousOn ⟨hn',hpz.le⟩
  exact annularCoverTwoCoefficient_ne_zero e a hs hp hy hy0

theorem annularCover_positive_exterior
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a : ℝ} (ha : a<1/2) (he : compactHandleBand a⊆e.source)
    (hor : PositivePartialChart (handleDensityChart e a))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {r : ℝ} (hr : 0<r)
    (hγ : ∀ x∈(handleAnnularChart e a).target,manifoldExteriorOneForm γ x=r • Λ x)
    {q : Plane} (hq : q∈annularCoverDomain e a) :
    0 < manifoldExteriorOneForm γ (handleAnnularCover e a q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (handleAnnularCover e a) q (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (handleAnnularCover e a) q (0,1)) := by
  have heq := hγ (handleAnnularCover e a q) ((handleAnnularChart e a).map_source hq)
  have hv := congrArg (fun B : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    B (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (handleAnnularCover e a) q (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (handleAnnularCover e a) q (0,1))) heq
  have hp' := mul_pos hr (annularCoverTwoCoefficient_positive e ha he hor hΛ hs hp hq)
  exact lt_of_lt_of_eq hp' hv.symm

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem handleAnnularCover_surjOn
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞) (a : ℝ) :
    SurjOn (handleAnnularCover e a) (annularCoverDomain e a) (handleAnnularChart e a).target := by
  intro x hx
  let z := (handleAnnularChart e a).symm x
  let q : Plane := (z.1,shortCircleArgument z.2)
  have heq : cylinderCover q=z := by
    exact Prod.ext rfl (circleTurn_shortCircleArgument z.2)
  refine ⟨q,?_,?_⟩
  · change cylinderCover q∈(handleAnnularChart e a).source
    rw [heq]
    exact (handleAnnularChart e a).map_target hx
  · change handleAnnularChart e a (cylinderCover q)=x
    rw [heq]
    exact (handleAnnularChart e a).right_inv hx

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem annularPackingRectangle_subset
    {a b δ : ℝ} (hab : b<a) (hsmall : δ<1/2) :
    Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ) ⊆ Ioo (-a) a ×ˢ Ioo (0:ℝ) 1 := by
  intro q hq
  exact ⟨⟨by linarith [hq.1.1],by linarith [hq.1.2]⟩,
    ⟨by linarith [hq.2.1],by linarith [hq.2.2]⟩⟩

 theorem annularPackingGeometry
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) HandleTorus M ∞)
    {a b δ : ℝ} (ha : a<1/2) (hab : b<a) (hsmall : δ<1/2)
    (he : compactHandleBand a⊆e.source) (hor : PositivePartialChart (handleDensityChart e a))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0<chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {r : ℝ} (hr : 0<r)
    (hγ : ∀ x∈(handleAnnularChart e a).target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈(handleAnnularChart e a).target,manifoldExteriorOneForm γ x=r • Λ x) :
    ContDiffOn ℝ ∞ (annularCoverA e a γ) (Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ)) ∧
    ContDiffOn ℝ ∞ (annularCoverB e a γ) (Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ)) ∧
    ∀ q∈Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ),
      0<fderiv ℝ (annularCoverB e a γ) q (1,0)-fderiv ℝ (annularCoverA e a γ) q (0,1) := by
  have hsub := handleAnnularCover_rectangle_domain e ha he (annularPackingRectangle_subset hab hsmall)
  refine ⟨(annularCover_coefficients_smooth e a hγ).1.mono hsub,
    (annularCover_coefficients_smooth e a hγ).2.mono hsub,?_⟩
  intro q hq
  rw [annularCover_curl e a (hsub hq) (hγ _ ((handleAnnularChart e a).map_source (hsub hq)))]
  exact annularCover_positive_exterior e ha he hor hΛ hs hp hr hdγ (hsub hq)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem annularPackingGeometry
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hbw : b<D.width) (hsmall : δ<1/2)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0<chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {r : ℝ} (hr : 0<r)
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x) :
    ContDiffOn ℝ ∞ (D.annularCoverA γ) (Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ)) ∧
    ContDiffOn ℝ ∞ (D.annularCoverB γ) (Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ)) ∧
    ∀ q∈Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ),
      0<fderiv ℝ (D.annularCoverB γ) q (1,0)-fderiv ℝ (D.annularCoverA γ) q (0,1) := by
  have hsub := D.handleAnnularCover_rectangle_domain (annularPackingRectangle_subset hbw hsmall)
  refine ⟨(D.annularCover_coefficients_smooth hγ).1.mono hsub,
    (D.annularCover_coefficients_smooth hγ).2.mono hsub,?_⟩
  intro q hq
  rw [D.annularCover_curl (hsub hq) (hγ _ (D.chart.map_source (hsub hq)))]
  exact D.annularCover_positive_exterior hor hΛ hs hp hr hdγ (hsub hq)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped Manifold
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

 theorem exists_smooth_base_germs {U : Set Plane} (hU : IsOpen U)
    {a b : Plane → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    {x : Plane} (hx : x∈U) :
    ∃ a' b' : Plane → ℝ, ContDiff ℝ ∞ a' ∧ ContDiff ℝ ∞ b' ∧
      a' =ᶠ[𝓝 x] a ∧ b' =ᶠ[𝓝 x] b := by
  obtain ⟨r,hr,hrU,he⟩ := exists_smooth_local_identity (hU.mem_nhds hx)
  refine ⟨a ∘ r,b ∘ r,ha.comp_contDiff hr hrU,hb.comp_contDiff hr hrU,?_,?_⟩
  · filter_upwards [he] with y hy
    exact congrArg a hy
  · filter_upwards [he] with y hy
    exact congrArg b hy

 theorem euclideanExteriorOneForm_congr_germ {α β : E → E →L[ℝ] ℝ} {x : E}
    (h : α =ᶠ[𝓝 x] β) : euclideanExteriorOneForm α x=euclideanExteriorOneForm β x := by
  simp only [euclideanExteriorOneForm,h.fderiv_eq]

 theorem surfaceFirstPath_isInvertible_local [FiniteDimensional ℝ E]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {S : ℝ → ℝ} {H : E → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H)
    {U : Set Plane} (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hw : ContDiff ℝ ∞ w) (ℓ : ℝ) (p : Plane × E) (hp : p.1∈U)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0 ≤ w p.1)
    (hSpos : 0 ≤ deriv S p.1.1)
    (hHpos : 0 ≤ H ((Φ.map ℓ).symm (Φ.map (ℓ*S p.1.1) p.2))) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
      euclideanExteriorOneForm (fun x => surfaceFirstPrimitive Φ S H a b w (ℓ,x)) p).IsInvertible := by
  obtain ⟨a',b',ha',hb',hea,heb⟩ := exists_smooth_base_germs hU ha hb hp
  have hbase' : 0<fderiv ℝ b' p.1 (1,0)-fderiv ℝ a' p.1 (0,1) := by
    rwa [hea.fderiv_eq,heb.fderiv_eq]
  have hi := surfaceFirstPath_isInvertible hΩ hskew Φ hS hH ha' hb' hw ℓ p
    hbase' hwzero hwpos hSpos hHpos
  have he : (fun x => surfaceFirstPrimitive Φ S H a' b' w (ℓ,x)) =ᶠ[𝓝 p]
      (fun x => surfaceFirstPrimitive Φ S H a b w (ℓ,x)) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds hea,
      continuousAt_fst.preimage_mem_nhds heb] with y hya hyb
    change a' y.1=a y.1 at hya
    change b' y.1=b y.1 at hyb
    apply ContinuousLinearMap.ext
    intro v
    simp only [surfaceFirstPrimitive,horizontalOneForm_apply,hya,hyb]
  rwa [euclideanExteriorOneForm_congr_germ he] at hi

 theorem surfaceSecondPath_isInvertible_local [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {S : ℝ → ℝ} {K H : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) {U : Set Plane} (hU : IsOpen U)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hw : ContDiff ℝ ∞ w)
    (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) (p : Plane × E) (hp : p.1∈U)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0 ≤ w p.1)
    (hSpos : 0 ≤ deriv S p.1.1)
    (hHpos : 0 ≤ H ((Φ.map 1).symm (Φ.map (S p.1.1) p.2)))
    (hclock : ∀ i, 0 ≤ deriv (ρ i) p.1.1) (hclock₀ : 0 ≤ deriv ρ₀ p.1.1)
    (hcap : ∀ i, 0 ≤ h i (Φ.map (S p.1.1) p.2))
    (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm (Φ.map (S p.1.1) p.2)) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
      euclideanExteriorOneForm (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) p).IsInvertible := by
  obtain ⟨a',b',ha',hb',hea,heb⟩ := exists_smooth_base_germs hU ha hb hp
  have hbase' : 0<fderiv ℝ b' p.1 (1,0)-fderiv ℝ a' p.1 (0,1) := by
    rwa [hea.fderiv_eq,heb.fderiv_eq]
  have hi := surfaceSecondPath_isInvertible hΩ hskew Φ hS hK hH hh hρ hρ₀ ha' hb' hw τ hτ p
    hbase' hwzero hwpos hSpos hHpos hclock hclock₀ hcap hres
  have he : (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a' b' w (τ,x)) =ᶠ[𝓝 p]
      (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds hea,
      continuousAt_fst.preimage_mem_nhds heb] with y hya hyb
    change a' y.1=a y.1 at hya
    change b' y.1=b y.1 at hyb
    apply ContinuousLinearMap.ext
    intro v
    simp only [surfaceSecondPrimitive,horizontalOneForm_apply,hya,hyb]
  rwa [euclideanExteriorOneForm_congr_germ he] at hi

theorem horizontalCoupling_congr_germ {A B A' B' : Plane × E → ℝ} {p : Plane × E}
    (hA : A =ᶠ[𝓝 p] A') (hB : B =ᶠ[𝓝 p] B') :
    horizontalCoupling Ω A B p = horizontalCoupling Ω A' B' p := by
  have h : horizontalOneForm A B =ᶠ[𝓝 p] horizontalOneForm A' B' := by
    filter_upwards [hA,hB] with x ha hb
    apply ContinuousLinearMap.ext
    intro v
    simp only [horizontalOneForm_apply,ha,hb]
  simp only [horizontalCoupling,euclideanExteriorOneForm_congr_germ h]

theorem baseShear_weighted_pullback_local (hΩ : Ω.IsInvertible)
    (hskew : ∀ v w, Ω v w = -Ω w v) (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) {U : Set Plane} (hU : IsOpen U)
    {a b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hw : ContDiff ℝ ∞ w) (hG : ContDiff ℝ ∞ G) (p : Plane × E) (hp : p.1 ∈ U) :
    (horizontalCoupling Ω (baseCoefficient a) (weightedSecondCoefficient b w G)
      (hamiltonianBaseShear Φ S hS p)).bilinearComp
        (fderiv ℝ (hamiltonianBaseShear Φ S hS) p) (fderiv ℝ (hamiltonianBaseShear Φ S hS) p) =
      horizontalCoupling Ω
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ S) +
          baseCoefficient a ∘ hamiltonianBaseShear Φ S hS)
        (weightedSecondCoefficient b w G ∘ hamiltonianBaseShear Φ S hS) p := by
  obtain ⟨a',b',ha',hb',hea,heb⟩ := exists_smooth_base_germs hU ha hb hp
  have hl : horizontalCoupling Ω (baseCoefficient a') (weightedSecondCoefficient b' w G)
      (hamiltonianBaseShear Φ S hS p) =
      horizontalCoupling Ω (baseCoefficient a) (weightedSecondCoefficient b w G)
        (hamiltonianBaseShear Φ S hS p) := by
    have hf : ContinuousAt (Prod.fst : Plane × E → Plane) (hamiltonianBaseShear Φ S hS p) := continuousAt_fst
    apply horizontalCoupling_congr_germ
    · exact hf.preimage_mem_nhds hea
    · filter_upwards [hf.preimage_mem_nhds heb] with x hx
      change b' x.1 = b x.1 at hx
      simp only [weightedSecondCoefficient,hx]
  have hr : horizontalCoupling Ω
      (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ S) +
        baseCoefficient a' ∘ hamiltonianBaseShear Φ S hS)
      (weightedSecondCoefficient b' w G ∘ hamiltonianBaseShear Φ S hS) p =
      horizontalCoupling Ω
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ S) +
          baseCoefficient a ∘ hamiltonianBaseShear Φ S hS)
        (weightedSecondCoefficient b w G ∘ hamiltonianBaseShear Φ S hS) p := by
    apply horizontalCoupling_congr_germ
    · filter_upwards [continuousAt_fst.preimage_mem_nhds hea] with x hx
      change a' x.1 = a x.1 at hx
      change _ + a' x.1 = _ + a x.1
      rw [hx]
    · filter_upwards [continuousAt_fst.preimage_mem_nhds heb] with x hx
      change b' x.1 = b x.1 at hx
      change b' x.1 + _ = b x.1 + _
      rw [hx]
  have h := baseShear_coupling_pullback_general hΩ hskew Φ hS
    (baseCoefficient_smooth ha') (weightedSecondCoefficient_smooth hb' hw hG) p
  rwa [hl,hr] at h

theorem surfaceSecondEndpoint_shear_pullback {ι : Type*} [Fintype ι]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {S : ℝ → ℝ}
    {K H : E → ℝ} {h : ι → E → ℝ} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) {U : Set Plane} (hU : IsOpen U)
    {a b w : Plane → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hw : ContDiff ℝ ∞ w) (p : Plane × E) (hp : p.1 ∈ U) :
    (horizontalCoupling Ω (baseCoefficient a)
      (weightedSecondCoefficient b w (surfaceFinalLayer (K-H) h
        (surfaceRemainder K H h (Φ.map 1).symm) ρ ρ₀))
      (hamiltonianBaseShear Φ S hS p)).bilinearComp
        (fderiv ℝ (hamiltonianBaseShear Φ S hS) p) (fderiv ℝ (hamiltonianBaseShear Φ S hS) p) =
      Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
        euclideanExteriorOneForm (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (1,x)) p := by
  rw [surfaceSecondPrimitive_coupling Φ hS]
  have hG := surfaceInterpolatedLayer_smooth hS hK hH hh (Φ.map_inverse_smooth 1) hρ hρ₀ 1
  have he : surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ 1 =
      surfaceFinalLayer (K-H) h (surfaceRemainder K H h (Φ.map 1).symm) ρ ρ₀ := by
    funext q
    simp only [surfaceInterpolatedLayer,sub_self,zero_mul,one_mul,zero_add]
  rw [he]
  exact baseShear_weighted_pullback_local hΩ hskew Φ hS hU ha hb hw (he ▸ hG) p hp

end

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
 theorem annular_normalForm_cover
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b ((handleAnnularChart e a).symm x).1*H v) • globalHandleForm e f x)
    (v : V) {q : Plane} (hq : q∈annularCoverDomain e a) (hx : handleAnnularCover e a q∈W) :
    Γ v (handleAnnularCover e a q)=γ (handleAnnularCover e a q)+
      (intervalClock (-b) b q.1*H v) • globalHandleForm e f (handleAnnularCover e a q) := by
  simpa only [handleAnnularCover_inverse e a hq,cylinderCover] using hN v _ hx

 theorem globalSurfaceFirstPrimitive_cover_germ
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b ((handleAnnularChart e a).symm x).1*H v) • globalHandleForm e f x)
    (ℓ : ℝ) {p : Plane × V} (hp : p.1∈annularCoverDomain e a)
    (hx : handleAnnularCover e a p.1∈W) :
    (fun y => euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceFirstPrimitive e a b f Φ H Γ (ℓ,v)))
      (flatProductMap (handleAnnularCover e a)) (0,y)) =ᶠ[𝓝 p]
    (fun y => surfaceFirstPrimitive Φ (intervalClock (-b) b) H
      (annularCoverA e a γ) (annularCoverB e a γ) (fun q => f (circleTurn q.2)) (ℓ,y)) := by
  have hs := (annularCoverDomain_open e a).mem_nhds hp
  have hw := (handleAnnularCover_smoothAt e a hp).continuousAt.preimage_mem_nhds (hW.mem_nhds hx)
  filter_upwards [continuousAt_fst.preimage_mem_nhds hs,
    continuousAt_fst.preimage_mem_nhds hw] with y hy hyW
  exact globalSurfaceFirstPrimitive_cover e a b f Φ H Γ γ ℓ y hy
    (annular_normalForm_cover e a b f H Γ γ hN y.2 hy hyW)

 theorem globalSurfaceSecondPrimitive_cover_germ {ι : Type*} [Fintype ι]
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b ((handleAnnularChart e a).symm x).1*H v) • globalHandleForm e f x)
    (τ : ℝ) {p : Plane × V} (hp : p.1∈annularCoverDomain e a)
    (hx : handleAnnularCover e a p.1∈W) :
    (fun y => euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ (τ,v)))
      (flatProductMap (handleAnnularCover e a)) (0,y)) =ᶠ[𝓝 p]
    (fun y => surfaceSecondPrimitive Φ (intervalClock (-b) b) K H h ρ ρ₀
      (annularCoverA e a γ) (annularCoverB e a γ) (fun q => f (circleTurn q.2)) (τ,y)) := by
  have hs := (annularCoverDomain_open e a).mem_nhds hp
  have hw := (handleAnnularCover_smoothAt e a hp).continuousAt.preimage_mem_nhds (hW.mem_nhds hx)
  filter_upwards [continuousAt_fst.preimage_mem_nhds hs,
    continuousAt_fst.preimage_mem_nhds hw] with y hy hyW
  exact globalSurfaceSecondPrimitive_cover e a b f Φ K H h ρ ρ₀ Γ γ τ y hy
    (annular_normalForm_cover e a b f H Γ γ hN y.2 hy hyW)

 theorem circleWeight_radial_deriv {f : Circle → ℝ}
    (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (q : Plane) :
    fderiv ℝ (fun y : Plane => f (circleTurn y.2)) q (1,0)=0 := by
  have ht := ((hf.comp circleTurn_smooth).contDiff.differentiable (by simp) q.2).hasFDerivAt
  have hd := (ht.comp q (hasFDerivAt_snd (𝕜 := ℝ) (p := q))).fderiv
  change (fderiv ℝ ((f ∘ circleTurn) ∘ Prod.snd) q) (1,0)=0
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',map_zero]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
