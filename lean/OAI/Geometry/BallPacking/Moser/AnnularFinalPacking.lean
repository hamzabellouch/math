import Mathlib
import OAI.Geometry.BallPacking.Flows.NonautonomousManifoldFlow

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem exists_global_surface_final_packing {m N : ℕ}
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
    {Kbase : Set M} (hbase : D.chart '' band b⊆interior Kbase)
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hN : ∀ p x,x∈W → Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    {Y V : Set (Fin m  →  ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) (hVY : V⊆Y)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    (h : Fin N  →  (Fin m  →  ℝ)  →  ℝ) (hh : ∀ i,ContDiff ℝ ∞ (h i))
    (hhp : ∀ i p,p∈V → 0≤h i p)
    (r r' : Fin N  →  ℝ) (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → (∑ j,p j)≤r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → p∈V → r i-(∑ j,p j)≤h i p) :
    ∃ ρ : Fin (N+1)  →  ℝ  →  ℝ,
      (∀ i,ContDiff ℝ ∞ (ρ i)) ∧ (∀ i s,0≤deriv (ρ i) s) ∧
      (∀ s,s ≤ -b  → ∀ i,ρ i s=0) ∧ (∀ s,b ≤ s  → ∀ i,ρ i s=1) ∧
      ∃ φ : Fin N  →  Ambient (m+1)  →  M × PlanePhase (Fin m),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
          (globalHorizontalCoupling phaseArea (fun v => globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments)
            (fun j => h j ∘ planeMoments) (fun j => ρ j.castSucc) (ρ (Fin.last N))
            (Γ ∘ planeMoments) (1,v))) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ (planeMoments ⁻¹' Y)))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  have hgeo := D.annularPackingGeometry hbw hsmall hor hΛ hsΛ hpΛ hε hγ hdγ
  let R := surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
    (fun j => h j ∘ planeMoments) (Φ.map 1).symm
  have hR : ContDiff ℝ ∞ R := surfaceRemainder_smooth (hK.comp planeMoments_smooth)
    (hH.comp planeMoments_smooth) (fun j => (hh j).comp planeMoments_smooth) (Φ.map_inverse_smooth 1)
  obtain ⟨lo,hi,ρ,hbd,_,hsm,hpos,hcol,U,φ,hU,hBU,hφ,hemb,him,hform,hdis⟩ :=
    exists_final_surface_layer_packing hδ hsmall (by linarith : -b<b)
      hgeo.1 hgeo.2.1 hgeo.2.2 (K-H) R h (hK.sub hH) hR hh hV hhp r r' hr' hrr hsimplex hheight
  have hlo : ∀ s,s ≤ -b  → ∀ i,ρ i s=0 := by
    intro s hs i
    obtain ⟨ε,hε,hlo,_⟩ := hcol i
    exact hlo s (by linarith [(hbd i).1])
  have hhi : ∀ s,b ≤ s  → ∀ i,ρ i s=1 := by
    intro s hs i
    obtain ⟨ε,hε,_,hhi⟩ := hcol i
    exact hhi s (by linarith [(hbd i).2.2])
  let S : Set Plane := Ioo (-b) b ×ˢ Ioo (1/2-δ) (1/2+δ)
  have hS : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  have hsub := D.handleAnnularCover_rectangle_domain (annularPackingRectangle_subset hbw hsmall)
  have himS : ∀ i,MapsTo (φ i) (U i) (S ×ˢ (planeMoments ⁻¹' V)) := by
    intro i z hz
    have hp := him i z hz
    exact ⟨⟨⟨lt_trans (hbd _).1 hp.1.1.1,lt_trans hp.1.1.2 (hbd _).2.2⟩,hp.1.2⟩,hp.2⟩
  have hΓf : SmoothOneFormFamily (fun v => globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments)
      (fun j => h j ∘ planeMoments) (fun j => ρ j.castSucc) (ρ (Fin.last N))
      (Γ ∘ planeMoments) (1,v)) :=
    (globalSurfaceSecondPrimitive_smooth D hb hbw Φ
      (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth)
      (fun j => (hh j).comp planeMoments_smooth) (fun j => (hsm j.castSucc).1) (hsm _).1
      (fun s hs => ⟨fun j => hlo s hs j.castSucc,hlo s hs _⟩)
      (fun s hs => ⟨fun j => hhi s hs j.castSucc,hhi s hs _⟩)
      (hΓ.comp planeMoments_smooth)).comp (contDiff_const.prodMk contDiff_id)
  let Ω₀ := horizontalCoupling phaseArea (baseCoefficient (D.annularCoverA γ))
    (weightedSecondCoefficient (D.annularCoverB γ) (fun q => positiveCircleClock δ (circleTurn q.2))
      (surfaceFinalLayer ((K-H) ∘ planeMoments) (fun j => h j ∘ planeMoments) R
        (fun j => ρ j.castSucc) (ρ (Fin.last N))))
  have hφform : ∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i))
      (fun _ => successorStandardForm m) Ω₀ (φ i) := by
    intro i
    refine ⟨U i,hU i,hBU i,(hφ i).contMDiffOn,hemb i,?_⟩
    intro z hz v u
    rw [mfderiv_eq_fderiv]
    change Ω₀ (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u) = successorStandardForm m v u
    erw [successorStandardForm_apply]
    exact hform i z hz v u
  let Ω₁ := globalHorizontalCoupling phaseArea (fun v => globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments)
    (fun j => h j ∘ planeMoments) (fun j => ρ j.castSucc) (ρ (Fin.last N)) (Γ ∘ planeMoments) (1,v))
  have hgform : ∀ p∈S ×ˢ (univ : Set (PlanePhase (Fin m))),∀ v u,
      Ω₁ (annularUnshearMap D b Φ p)
        (mfderiv 𝓘(ℝ,Plane × PlanePhase (Fin m)) 𝓘(ℝ,Plane × PlanePhase (Fin m)) (annularUnshearMap D b Φ) p v)
        (mfderiv 𝓘(ℝ,Plane × PlanePhase (Fin m)) 𝓘(ℝ,Plane × PlanePhase (Fin m)) (annularUnshearMap D b Φ) p u)=Ω₀ p v u := by
    intro p hp v u
    have Hpull := annularUnshearMap_pullback D b phaseArea_isInvertible phaseArea_skew Φ
      (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth) (fun j => (hh j).comp planeMoments_smooth)
      (fun j => (hsm j.castSucc).1) (hsm _).1 (Γ ∘ planeMoments) γ hW
      (fun v x hx => hN (planeMoments v) x hx) hΓf hS hgeo.1 hgeo.2.1
      (hsub hp.1) hp.1 (hBW (D.handleAnnularCover_mem_band b ⟨hp.1.1.1.le,hp.1.1.2.le⟩)) v u
    dsimp only [Ω₀, Ω₁, R]
    rw [← hclock]
    exact Hpull
  obtain ⟨hemb',hdis'⟩ := postcompose_form_packing (fun i => closedBall (m+1) (r' i))
    (fun _ => successorStandardForm m) Ω₀ Ω₁ (hS.prod isOpen_univ) (annularUnshearMap D b Φ)
    (D.annularUnshearMap_smoothOn b Φ hsub)
    (D.annularUnshearMap_isEmbedding b Φ (annularPackingRectangle_subset hbw hsmall)) hgform
    φ hφform (fun i z hz => ⟨(himS i (hBU i hz)).1,mem_univ _⟩) hdis
  refine ⟨ρ,fun i => (hsm i).1,fun i s => (hpos i s).2.2,hlo,hhi,
    fun i => annularUnshearMap D b Φ ∘ φ i,hemb',?_,hdis'⟩
  intro i z hz
  have hp := himS i (hBU i hz)
  apply D.annularUnshearMap_mem_interior b Φ hbase hΦ ⟨hp.1.1.1.le,hp.1.1.2.le⟩
  exact interior_mono (preimage_mono hVY) (hV.interior_eq.symm ▸ hp.2)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {M V ι : Type*}

def baseFiberMoment (χ : M → ℝ) (μ : ι → V → ℝ) : Option ι → M × V → ℝ := fun i =>
  match i with | none => fun z => -χ z.1 | some i => fun z => μ i z.2

def baseFiberInner (a : ι → ℝ) : Option ι → ℝ :=
  fun i => match i with | none => -3/4 | some i => a i

def baseFiberOuter (c : ι → ℝ) : Option ι → ℝ :=
  fun i => match i with | none => -1/2 | some i => c i

 theorem baseFiber_bounds {a c : ι → ℝ} (h : ∀ i,a i<c i) :
    ∀ i,baseFiberInner a i<baseFiberOuter c i := by
  rintro (_|i)
  · norm_num [baseFiberInner,baseFiberOuter]
  · exact h i

 theorem baseFiber_domain (χ : M → ℝ) (μ : ι → V → ℝ) (c : ι → ℝ) :
    {z | ∀ i,baseFiberMoment χ μ i z≤baseFiberOuter c i}=
      {x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v≤c i} := by
  ext z
  simp only [mem_ofPred_eq,Option.forall,baseFiberMoment,baseFiberOuter,mem_prod]
  constructor
  · rintro ⟨hb,hy⟩
    exact ⟨by linarith,hy⟩
  · rintro ⟨hb,hy⟩
    exact ⟨by linarith,hy⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem baseFiberMoment_smooth [NormedAddCommGroup V] [NormedSpace ℝ V]
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ)
    {μ : ι → V → ℝ} (hμ : ∀ i,ContDiff ℝ ∞ (μ i)) :
    ∀ i,ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) ∞ (baseFiberMoment χ μ i) := by
  rintro (_|i)
  · exact (hχ.comp flatProduct_fst_smooth).neg
  · exact (hμ i).contMDiff.comp flatProduct_snd_smooth

variable [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem exists_base_moser_cutoff {S D : Set M} (hS : IsCompact S) (hSD : S⊆interior D) :
    ∃ χ : M → ℝ,ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧
      IsCompact {x | (1/2:ℝ)≤χ x} ∧ {x | (1/2:ℝ)≤χ x}⊆D ∧
      (∀ x∈S,χ x=1) := by
  obtain ⟨χ,hχ,hχc,hχs,hχ1,_⟩ := exists_smooth_manifold_cutoff (E := E) hS isOpen_interior hSD
  have hc : IsClosed {x | (1/2:ℝ)≤χ x} := isClosed_le continuous_const hχ.continuous
  have hh : {x | (1/2:ℝ)≤χ x}⊆tsupport χ := by
    intro x hx
    apply subset_tsupport χ
    change χ x≠0
    have h : (1/2:ℝ)≤χ x := hx
    linarith
  exact ⟨χ,hχ,hχc.isCompact.of_isClosed_subset hc hh,
    hh.trans (hχs.trans interior_subset),hχ1.self_of_nhdsSet⟩

end

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

 theorem horizontalModel_exterior_vertical
    {A : E × V → E →L[ℝ] ℝ} {x : E × V} (hA : DifferentiableAt ℝ A x)
    (Z : V) (w : E × V) :
    euclideanExteriorOneForm (fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V)) x (0,Z) w=
      fderiv ℝ (fun v => A (x.1,v)) x.2 Z w.1 := by
  let α : (E × V) → (E × V) →L[ℝ] ℝ := fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V)
  have hα : DifferentiableAt ℝ α x := hA.clm_comp (differentiableAt_const _)
  have hz : (fun q => α q (0,Z))=fun _ => (0:ℝ) := by funext q; simp [α]
  have hw : (fun q => α q w)=fun q => A q w.1 := rfl
  have hd : HasFDerivAt (fun v : V => (x.1,v)) (ContinuousLinearMap.inr ℝ E V) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hs := hA.hasFDerivAt.comp x.2 hd
  have he := congrArg (fun L : V →L[ℝ] E →L[ℝ] ℝ => L Z w.1) hs.fderiv
  change fderiv ℝ (fun v => A (x.1,v)) x.2 Z w.1=fderiv ℝ A x (0,Z) w.1 at he
  change fderiv ℝ α x (0,Z) w-fderiv ℝ α x w (0,Z)=_
  rw [← fderiv_clm_eval hα,← fderiv_clm_eval hα,hz,hw,fderiv_const_apply,
    zero_apply,sub_zero]
  rw [(hA.hasFDerivAt.clm_apply (hasFDerivAt_const w.1 x)).fderiv]
  simpa using he.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem SmoothOneFormFamily.parameter_contDiffAt {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (v : V) (x : M) : ContDiffAt ℝ ∞ (fun w => Γ w x) v := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hcam := ((hΓ x).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      (show (v,extChartAt 𝓘(ℝ,E) x x)∈univ ×ˢ (extChartAt 𝓘(ℝ,E) x).target from ⟨mem_univ v,hxt⟩))).comp v
        (contDiffAt_id.prodMk contDiffAt_const)
  have hsm := hcam.clm_comp (contDiffAt_const (c := chartDifferential x x))
  apply hsm.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w => by
    simpa only [(extChartAt 𝓘(ℝ,E) x).left_inv hx,Function.comp_def,id_eq] using
      (chartOneForm_reconstruct_target (α := Γ w) hxt).symm)

 theorem productHorizontalLift_exterior_vertical {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × V) (Z : V)
    (hZ : fderiv ℝ (fun v => Γ v z.1) z.2 Z=0) (w : E × V) :
    manifoldExteriorOneForm (productHorizontalLift Γ) z (0,Z) w=0 := by
  let c := z.1
  let y := extChartAt 𝓘(ℝ,E) c c
  have hc := mem_extChartAt_source (I := 𝓘(ℝ,E)) c
  have hy := (extChartAt 𝓘(ℝ,E) c).map_source hc
  have he := (extChartAt 𝓘(ℝ,E) c).left_inv hc
  have hg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hy)
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y
  have hC : (chartDifferential (E := E) c c).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
  have hD : D (chartDifferential c c w.1)=w.1 := by
    have hDi := chartDifferential_inverse hy
    rw [he] at hDi
    change (chartDifferential (E := E) c c).inverse=D at hDi
    rw [← hDi]
    exact hC.inverse_apply_self _
  let A : E × V → E →L[ℝ] ℝ := fun q => chartOneForm (Γ q.2) c q.1
  have hA : ContDiffAt ℝ ∞ A (y,z.2) :=
    ((hΓ c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds
      ⟨mem_univ _,hy⟩)).comp (y,z.2) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hAz : fderiv ℝ (fun v => A (y,v)) z.2 Z=0 := by
    have hparam := (hΓ.parameter_contDiffAt z.2 c).differentiableAt (by simp)
    have hh : (fun v => A (y,v))=fun v => (Γ v c).comp (chartDifferential c c).inverse := by
      funext v
      simp only [A,chartOneForm,y,he]
    rw [hh]
    have hd := hparam.hasFDerivAt.clm_comp (hasFDerivAt_const (chartDifferential (E := E) c c).inverse z.2)
    rw [hd.fderiv]
    ext u
    simp [hZ,c]
  have hp : (fun q => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ)
        (flatProductMap (extChartAt 𝓘(ℝ,E) c).symm) (0,q)) =ᶠ[𝓝 (y,z.2)]
      fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target c).mem_nhds hy)] with q hq
    have hqg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hq)
    apply ContinuousLinearMap.ext
    intro v
    rw [productHorizontalLift_pullback_apply _ hqg]
    simp only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hq,A,
      ContinuousLinearMap.comp_apply]
    rfl
  have hpb := productHorizontalLift_exterior_pullback hΓ hg (x := (y,z.2))
  have hz := horizontalModel_exterior_vertical (hA.differentiableAt (by simp)) Z
    (chartDifferential c c w.1,w.2)
  have hh := congrArg (fun B : (E × V) →L[ℝ] (E × V) →L[ℝ] ℝ =>
    B (0,Z) (chartDifferential c c w.1,w.2)) hpb
  have hpe : euclideanExteriorOneForm (fun q => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ)
      (flatProductMap (extChartAt 𝓘(ℝ,E) c).symm) (0,q)) (y,z.2)=
      euclideanExteriorOneForm (fun q => (A q).comp (ContinuousLinearMap.fst ℝ E V)) (y,z.2) := by
    unfold euclideanExteriorOneForm
    rw [hp.fderiv_eq]
  rw [hpe,hz,hAz,zero_apply] at hh
  have hpoint : flatProductMap (extChartAt 𝓘(ℝ,E) c).symm (y,z.2)=z := by
    simp [flatProductMap,y,c]
  rw [hpoint] at hh
  change 0=manifoldExteriorOneForm (productHorizontalLift Γ) z (D 0,Z)
    (D (chartDifferential c c w.1),w.2) at hh
  simpa only [map_zero,hD,Prod.mk.eta] using hh.symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport
open Set

theorem constant_above_of_deriv_eq_zero {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {a t₀ : ℝ} (hzero : ∀ t, a < f t → deriv f t = 0) (h₀ : a < f t₀) :
    ∀ t, f t = f t₀ := by
  let s : Set ℝ := {t | f t = f t₀}
  have hclosed : IsClosed s := isClosed_eq hf.continuous continuous_const
  have hopen : IsOpen s := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hft : a < f t := by rw [ht]; exact h₀
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt continuous_const hf.continuous).mem_nhds hft)
    apply Filter.mem_of_superset (Metric.ball_mem_nhds t hr)
    intro u hu
    have he := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball t r).isPreconnected hf.differentiableOn
      (fun {v} hv => hzero v (hball hv)) hu (Metric.mem_ball_self hr)
    exact he.trans ht
  have hs : s = univ := (show IsClopen s from ⟨hclosed,hopen⟩).eq_univ ⟨t₀,rfl⟩
  intro t
  have ht : t ∈ s := hs.symm ▸ mem_univ t
  exact ht

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
open scoped Manifold
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E →L[ℝ] ℝ}
namespace CompactHamiltonianIsotopy

theorem integral_constant_on_collar (Φ : CompactHamiltonianIsotopy A)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    (x : E) {s : ℝ} (hs : a < f (Φ.map s x)) (t : ℝ) :
    f (Φ.map t x) = f (Φ.map s x) := by
  have hd (u : ℝ) := (hf (Φ.map u x)).hasFDerivAt.comp_hasDerivAt u (Φ.flow u x)
  exact constant_above_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u hu => (hd u).deriv.trans (hzero u (Φ.map u x) hu)) hs t

theorem preserves_integral_on_collar (Φ : CompactHamiltonianIsotopy A)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) : f (Φ.map t x) = f x := by
  simpa only [Φ.zero,Homeomorph.refl_apply,id_eq] using
    Φ.integral_constant_on_collar hf hzero x (s := 0)
      (by simpa only [Φ.zero,Homeomorph.refl_apply,id_eq] using hx) t

theorem inverse_preserves_integral_on_collar (Φ : CompactHamiltonianIsotopy A)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) : f ((Φ.map t).symm x) = f x := by
  simpa only [Φ.zero,Homeomorph.refl_apply,id_eq,Homeomorph.apply_symm_apply] using
    Φ.integral_constant_on_collar hf hzero ((Φ.map t).symm x) (s := t)
      (by simpa only [Homeomorph.apply_symm_apply] using hx) 0

end CompactHamiltonianIsotopy

def autonomousField (A : E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) : E :=
  hamiltonianField A (fun p => f p.2) (0,x)

theorem autonomousField_contraction (hA : A.IsInvertible) {f : E → ℝ}
    (hf : Differentiable ℝ f) (x v : E) :
    A (autonomousField A f x) v = -fderiv ℝ f x v := by
  rw [autonomousField,hamiltonianField_contraction hA]
  have hd := (hf x).hasFDerivAt.comp (0,x) (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt
  change HasFDerivAt (fun p : ℝ × E => f p.2) _ _ at hd
  change -fderiv ℝ (fun p : ℝ × E => f p.2) (0,x) (0,v) = _
  rw [hd.fderiv]
  rfl

theorem intertwines_autonomousField (hA : A.IsInvertible)
    (q : E ≃ₜ E) (hq : ContDiff ℝ ∞ q) (hqi : ContDiff ℝ ∞ q.symm)
    (hsymp : ∀ x v w, A (fderiv ℝ q x v) (fderiv ℝ q x w) = A v w)
    {f : E → ℝ} (hf : Differentiable ℝ f) (x : E)
    (hpres : (fun y => f (q y)) =ᶠ[𝓝 x] f) :
    fderiv ℝ q x (autonomousField A f x) = autonomousField A f (q x) := by
  have hinj : Injective A := by
    obtain ⟨e,he⟩ := hA
    rw [← he]
    exact e.injective
  apply hinj
  ext w
  let w' := fderiv ℝ q.symm (q x) w
  have hsurj : fderiv ℝ q x w' = w := by
    have he := ((hq.differentiable (by simp) (q.symm (q x))).hasFDerivAt.comp (q x)
      (hqi.differentiable (by simp) (q x)).hasFDerivAt)
    simp only [Homeomorph.symm_apply_apply] at he
    have he' : HasFDerivAt (fun y => q (q.symm y))
        ((fderiv ℝ q x).comp (fderiv ℝ q.symm (q x))) (q x) := he
    have hid : (fun y => q (q.symm y)) = id := by ext y; simp
    rw [hid] at he'
    have hw := congrArg (fun T : E →L[ℝ] E => T w)
      (he'.unique (hasFDerivAt_id (q x)))
    exact hw
  rw [← hsurj,hsymp,autonomousField_contraction hA hf,
    autonomousField_contraction hA hf]
  congr 1
  have hd := (hf (q x)).hasFDerivAt.comp x (hq.differentiable (by simp) x).hasFDerivAt
  have he : (fderiv ℝ f (q x)).comp (fderiv ℝ q x) = fderiv ℝ f x :=
    hd.fderiv.symm.trans hpres.fderiv_eq
  exact (congrArg (fun T : E →L[ℝ] ℝ => T w') he).symm

theorem homeomorph_fderiv_inverse (q : E ≃ₜ E)
    (hq : Differentiable ℝ q) (hqi : Differentiable ℝ q.symm) (x v : E) :
    fderiv ℝ q.symm (q x) (fderiv ℝ q x v) = v := by
  have hd := (hqi (q x)).hasFDerivAt.comp x (hq x).hasFDerivAt
  have he : (q.symm : E → E) ∘ q = id := by ext y; simp
  rw [he] at hd
  exact congrArg (fun T : E →L[ℝ] E => T v) (hd.unique (hasFDerivAt_id x))

namespace CompactHamiltonianIsotopy

theorem inverse_symplectic (Φ : CompactHamiltonianIsotopy A) (t : ℝ) (x v w : E) :
    A (fderiv ℝ (Φ.map t).symm x v) (fderiv ℝ (Φ.map t).symm x w) = A v w := by
  have hv := homeomorph_fderiv_inverse (Φ.map t).symm
    ((Φ.map_inverse_smooth t).differentiable (by simp))
    ((Φ.map_smooth t).differentiable (by simp)) x v
  have hw := homeomorph_fderiv_inverse (Φ.map t).symm
    ((Φ.map_inverse_smooth t).differentiable (by simp))
    ((Φ.map_smooth t).differentiable (by simp)) x w
  have hs := Φ.symplectic t ((Φ.map t).symm x)
    (fderiv ℝ (Φ.map t).symm x v) (fderiv ℝ (Φ.map t).symm x w)
  simp only [Homeomorph.symm_symm] at hv hw
  rw [hv,hw] at hs
  exact hs.symm

theorem intertwines_on_collar (Φ : CompactHamiltonianIsotopy A) (hA : A.IsInvertible)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) :
    fderiv ℝ (Φ.map t) x (autonomousField A f x) = autonomousField A f (Φ.map t x) := by
  apply intertwines_autonomousField hA (Φ.map t) (Φ.map_smooth t) (Φ.map_inverse_smooth t)
    (Φ.symplectic t) hf x
  filter_upwards [(isOpen_lt continuous_const hf.continuous).mem_nhds hx] with y hy
  exact Φ.preserves_integral_on_collar hf hzero hy t

theorem inverse_intertwines_on_collar (Φ : CompactHamiltonianIsotopy A) (hA : A.IsInvertible)
    {f : E → ℝ} (hf : Differentiable ℝ f) {a : ℝ}
    (hzero : ∀ t x, a < f x →
      fderiv ℝ f x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    {x : E} (hx : a < f x) (t : ℝ) :
    fderiv ℝ (Φ.map t).symm x (autonomousField A f x) = autonomousField A f ((Φ.map t).symm x) := by
  apply intertwines_autonomousField hA (Φ.map t).symm (Φ.map_inverse_smooth t) (Φ.map_smooth t)
    (Φ.inverse_symplectic t) hf x
  filter_upwards [(isOpen_lt continuous_const hf.continuous).mem_nhds hx] with y hy
  exact Φ.inverse_preserves_integral_on_collar hf hzero hy t

end CompactHamiltonianIsotopy

theorem hamiltonian_invariant_of_commutes (hA : A.IsInvertible)
    (hskew : ∀ v w, A v w = -A w v) (H : ℝ × E → ℝ)
    {f : E → ℝ} (hf : Differentiable ℝ f) (t : ℝ) (x : E)
    (hzero : fderiv ℝ f x (hamiltonianField A H (t,x)) = 0) :
    fderiv ℝ H (t,x) (0,autonomousField A f x) = 0 := by
  have hh := hamiltonianField_contraction hA H (t,x) (autonomousField A f x)
  rw [hskew,autonomousField_contraction hA hf,hzero] at hh
  linarith

theorem invariant_pullback_on_collar (hA : A.IsInvertible)
    (q : E ≃ₜ E) (hq : ContDiff ℝ ∞ q) (hqi : ContDiff ℝ ∞ q.symm)
    (hsymp : ∀ x v w, A (fderiv ℝ q x v) (fderiv ℝ q x w) = A v w)
    {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) {a : ℝ}
    (hpres : ∀ x, a < f x → f (q x) = f x)
    (hinv : ∀ x, a < f x → fderiv ℝ g x (autonomousField A f x) = 0)
    {x : E} (hx : a < f x) :
    fderiv ℝ (g ∘ q) x (autonomousField A f x) = 0 := by
  have ht := intertwines_autonomousField hA q hq hqi hsymp hf x (by
    filter_upwards [(isOpen_lt continuous_const hf.continuous).mem_nhds hx] with y hy
    exact hpres y hy)
  rw [fderiv_comp x (hg (q x)) (hq.differentiable (by simp) x),
    ContinuousLinearMap.comp_apply,ht]
  exact hinv (q x) (by rw [hpres x hx]; exact hx)

end
section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {a : ℝ}

def CollarInvariant (Ω : V →L[ℝ] V →L[ℝ] ℝ) (μ : V → ℝ) (a : ℝ) (f : V → W) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ v,a<μ v→fderiv ℝ f v (autonomousField Ω μ v)=0

 theorem CollarInvariant.const (w : W) : CollarInvariant Ω μ a (fun _ => w) := by
  refine ⟨contDiff_const,fun v _ => ?_⟩
  simp

 theorem CollarInvariant.add {f g : V → W} (hf : CollarInvariant Ω μ a f)
    (hg : CollarInvariant Ω μ a g) : CollarInvariant Ω μ a (fun v => f v+g v) := by
  refine ⟨hf.1.add hg.1,fun v hv => ?_⟩
  change fderiv ℝ (f+g) v (autonomousField Ω μ v)=0
  rw [fderiv_add (hf.1.differentiable (by simp) v) (hg.1.differentiable (by simp) v)]
  simp [hf.2 v hv,hg.2 v hv]

 theorem CollarInvariant.sub {f g : V → W} (hf : CollarInvariant Ω μ a f)
    (hg : CollarInvariant Ω μ a g) : CollarInvariant Ω μ a (fun v => f v-g v) := by
  refine ⟨hf.1.sub hg.1,fun v hv => ?_⟩
  change fderiv ℝ (f-g) v (autonomousField Ω μ v)=0
  rw [fderiv_sub (hf.1.differentiable (by simp) v) (hg.1.differentiable (by simp) v)]
  simp [hf.2 v hv,hg.2 v hv]

 theorem CollarInvariant.smul {f : V → ℝ} {g : V → W} (hf : CollarInvariant Ω μ a f)
    (hg : CollarInvariant Ω μ a g) : CollarInvariant Ω μ a (fun v => f v • g v) := by
  refine ⟨hf.1.smul hg.1,fun v hv => ?_⟩
  change fderiv ℝ (f • g) v (autonomousField Ω μ v)=0
  rw [((hf.1.differentiable (by simp) v).hasFDerivAt.smul
    (hg.1.differentiable (by simp) v).hasFDerivAt).fderiv]
  simp [hf.2 v hv,hg.2 v hv]

 theorem CollarInvariant.const_mul {f : V → ℝ} (hf : CollarInvariant Ω μ a f) (b : ℝ) :
    CollarInvariant Ω μ a (fun v => b*f v) := (CollarInvariant.const b).smul hf

 theorem CollarInvariant.sum {ι : Type*} (s : Finset ι) {f : ι → V → W}
    (hf : ∀ i∈s,CollarInvariant Ω μ a (f i)) :
    CollarInvariant Ω μ a (fun v => ∑ i∈s,f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CollarInvariant.const (Ω := Ω) (μ := μ) (a := a) (0:W))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

 theorem CollarInvariant.pullback {f : V → W} (hf : CollarInvariant Ω μ a f)
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,a<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0) (t : ℝ) :
    CollarInvariant Ω μ a (f ∘ Φ.map t) := by
  refine ⟨hf.1.comp (Φ.map_smooth t),fun v hv => ?_⟩
  rw [fderiv_comp v (hf.1.differentiable (by simp) _) ((Φ.map_smooth t).differentiable (by simp) _),
    ContinuousLinearMap.comp_apply,Φ.intertwines_on_collar hΩ hμ hzero hv t]
  apply hf.2
  rwa [Φ.preserves_integral_on_collar hμ hzero hv t]

 theorem CollarInvariant.inverse_pullback {f : V → W} (hf : CollarInvariant Ω μ a f)
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,a<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0) (t : ℝ) :
    CollarInvariant Ω μ a (f ∘ (Φ.map t).symm) := by
  refine ⟨hf.1.comp (Φ.map_inverse_smooth t),fun v hv => ?_⟩
  rw [fderiv_comp v (hf.1.differentiable (by simp) _) ((Φ.map_inverse_smooth t).differentiable (by simp) _),
    ContinuousLinearMap.comp_apply,Φ.inverse_intertwines_on_collar hΩ hμ hzero hv t]
  apply hf.2
  rwa [Φ.inverse_preserves_integral_on_collar hμ hzero hv t]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
 theorem CompactHamiltonianIsotopy.hamiltonian_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,a<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0) (t : ℝ) :
    CollarInvariant Ω μ a (fun v => Φ.hamiltonian (t,v)) := by
  refine ⟨Φ.hamiltonian_smooth.comp (contDiff_const.prodMk contDiff_id),fun v hv => ?_⟩
  have hd := (Φ.hamiltonian_smooth.differentiable (by simp) (t,v)).hasFDerivAt.comp v
    ((hasFDerivAt_const t v).prodMk (hasFDerivAt_id v))
  change fderiv ℝ (Φ.hamiltonian ∘ Prod.mk t) v (autonomousField Ω μ v)=0
  rw [hd.fderiv]
  exact hamiltonian_invariant_of_commutes hΩ hs Φ.hamiltonian hμ t v (hzero t v hv)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
 theorem toric_collarInvariant {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    {G : (ι → ℝ) → W} (hG : ContDiff ℝ ∞ G) (a : ℝ) :
    CollarInvariant phaseArea (F ∘ planeMoments) a (G ∘ planeMoments) := by
  refine ⟨hG.comp planeMoments_smooth,fun v _ => ?_⟩
  rw [fderiv_comp v (hG.differentiable (by simp) _) (planeMoments_smooth.differentiable (by simp) _),
    ContinuousLinearMap.comp_apply]
  have he : autonomousField phaseArea (F ∘ planeMoments) v=
      hamiltonianField phaseArea (toricHamiltonian F) (0,v) := rfl
  rw [he,toricHamiltonian_preserves_moments hF (0,v),map_zero]

end
section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem globalHorizontalCoupling_face
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible)
    {μ : V → ℝ} (hμ : ContDiff ℝ ∞ μ) {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × V)
    (hZ : fderiv ℝ (fun v => Γ v z.1) z.2 (autonomousField Ω μ z.2)=0) :
    globalHorizontalCoupling Ω Γ z (0,autonomousField Ω μ z.2)=
      -mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (fun y : M × V => μ y.2) z := by
  have hd : mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (fun y : M × V => μ y.2) z=
      (fderiv ℝ μ z.2).comp (ContinuousLinearMap.snd ℝ E V) := by
    simpa only [Function.comp_def,flatProduct_snd_derivative,mfderiv_eq_fderiv] using!
      (mfderiv_comp z (hμ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (flatProduct_snd_smooth.contMDiffAt.mdifferentiableAt (by simp)))
  apply ContinuousLinearMap.ext
  intro w
  rw [hd]
  change Ω (autonomousField Ω μ z.2) w.2+
    manifoldExteriorOneForm (productHorizontalLift Γ) z (0,autonomousField Ω μ z.2) w=
      -fderiv ℝ μ z.2 w.2
  rw [productHorizontalLift_exterior_vertical hΓ z _ hZ w,add_zero]
  exact autonomousField_contraction hΩ (hμ.differentiable (by simp)) z.2 w.2

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem productCouplingPrimitive_vertical_value
    (Ω : V →L[ℝ] V →L[ℝ] ℝ) (Γ : V → ManifoldOneForm E M)
    (z : M × V) (Z : V) :
    productCouplingPrimitive Ω Γ z (0,Z)=(1/2:ℝ)*Ω z.2 Z := by
  simp only [productCouplingPrimitive,Pi.add_apply,add_apply,
    productVerticalLiouville_apply,productHorizontalLift_vertical,add_zero]

 theorem productCouplingPrimitive_face
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {μ : V → ℝ} (hμ : ContDiff ℝ ∞ μ) {Γ : ℝ × V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {a : ℝ}
    (hInv : ∀ t x,CollarInvariant Ω μ a (fun v => Γ (t,v) x))
    (p : ℝ × (M × V)) (hp : a<μ p.2.2) :
    manifoldExteriorOneForm (productCouplingPrimitive Ω (fun v => Γ (p.1,v))) p.2
        (0,autonomousField Ω μ p.2.2)=
        -mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (fun y : M × V => μ y.2) p.2 ∧
      ∀ t, productCouplingPrimitive Ω (fun v => Γ (t,v)) p.2 (0,autonomousField Ω μ p.2.2)=
        productCouplingPrimitive Ω (fun v => Γ (0,v)) p.2 (0,autonomousField Ω μ p.2.2) := by
  have hsΓ : SmoothOneFormFamily (fun v => Γ (p.1,v)) :=
    hΓ.comp (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun v : V => v)))
  constructor
  · rw [productCouplingPrimitive_exterior Ω hs hsΓ]
    exact globalHorizontalCoupling_face hΩ hμ hsΓ p.2 ((hInv p.1 p.2.1).2 p.2.2 hp)
  · intro t
    rw [productCouplingPrimitive_vertical_value,productCouplingPrimitive_vertical_value]

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem isInvertible_of_chartTwoForm {Ω : ManifoldTwoForm E M} {c x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ,E) c).source)
    (hΩ : (chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c x)).IsInvertible) :
    (Ω x).IsInvertible := by
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hx using 1
  have hB : ((Ω x).bilinearComp (chartDifferential c x).inverse
      (chartDifferential c x).inverse).IsInvertible := by
    simpa only [chartTwoForm,(extChartAt 𝓘(ℝ,E) c).left_inv hx] using hΩ
  have hi := bilinearComp_isInvertible hB hC
  have he : ((Ω x).bilinearComp (chartDifferential c x).inverse
      (chartDifferential c x).inverse).bilinearComp
      (chartDifferential c x) (chartDifferential c x) = Ω x := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply,hC.inverse_apply_self]
  rwa [he] at hi

variable [CompleteSpace E]

theorem manifoldTwoForm_isOpen_nondegenerate
    {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) :
    IsOpen {p : ℝ × M | (Ω p.1 p.2).IsInvertible} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  let c := p.2
  let y := extChartAt 𝓘(ℝ,E) c c
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target := mem_extChartAt_target c
  have hi : (chartTwoForm (Ω p.1) c y).IsInvertible := by
    apply chartTwoForm_isInvertible hy
    simpa only [y,(extChartAt 𝓘(ℝ,E) c).left_inv (mem_extChartAt_source c)] using (show (Ω p.1 c).IsInvertible from hp)
  have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (p.1,y) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,hy⟩
  have hC : ContinuousAt (fun q : ℝ × M => (q.1,extChartAt 𝓘(ℝ,E) c q.2)) p :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt (I := 𝓘(ℝ,E)) c).comp continuousAt_snd)
  have hO : ContinuousAt (fun q : ℝ × M =>
      chartTwoForm (Ω q.1) c (extChartAt 𝓘(ℝ,E) c q.2)) p :=
    ContinuousAt.comp (f := fun q : ℝ × M => (q.1,extChartAt 𝓘(ℝ,E) c q.2))
      ((hΩ c).continuousOn.continuousAt hn) hC
  have hni : ∀ᶠ A : E →L[ℝ] E →L[ℝ] ℝ in 𝓝 (chartTwoForm (Ω p.1) c y),
      A.IsInvertible := ContinuousLinearEquiv.isOpen.mem_nhds hi
  have hsource : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ (extChartAt 𝓘(ℝ,E) c).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds c)
  filter_upwards [hO.preimage_mem_nhds hni,hsource] with q hq hqs
  exact isInvertible_of_chartTwoForm hqs hq

variable [CompactSpace M]

theorem manifoldTwoForm_isOpen_nondegenerate_times
    {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) :
    IsOpen {t : ℝ | ∀ x, (Ω t x).IsInvertible} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have h := (isCompact_univ : IsCompact (univ : Set M)).eventually_forall_of_forall_eventually
    (P := fun s x => (Ω s x).IsInvertible) (x₀ := t) (fun x _ =>
      (manifoldTwoForm_isOpen_nondegenerate hΩ).mem_nhds (ht x))
  filter_upwards [h] with s hs x
  exact hs x (mem_univ x)

end

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M] [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem productCouplingPrimitive_stationary
    (Ω : V →L[ℝ] V →L[ℝ] ℝ) (Γ : ℝ × V → ManifoldOneForm E M) (z : M × V)
    (hz : ∀ t,Γ (t,z.2) z.1=Γ (0,z.2) z.1) (t : ℝ) :
    productCouplingPrimitive Ω (fun v => Γ (t,v)) z=
      productCouplingPrimitive Ω (fun v => Γ (0,v)) z := by
  change productVerticalLiouville Ω z+(Γ (t,z.2) z.1).comp (ContinuousLinearMap.fst ℝ E V)=
    productVerticalLiouville Ω z+(Γ (0,z.2) z.1).comp (ContinuousLinearMap.fst ℝ E V)
  rw [hz t]

 def baseFiberField (Ω : V →L[ℝ] V →L[ℝ] ℝ) {ι : Type*} (μ : ι → V → ℝ) :
    Option ι → M × V → E × V := fun i => match i with
    | none => fun _ => 0
    | some i => fun z => (0,autonomousField Ω (μ i) z.2)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M] in
 theorem productCouplingPrimitive_baseFiber_face
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {χ : M → ℝ} (hstation : ∀ x,χ x<3/4→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i)) (a : ι → ℝ)
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (i : Option ι) (p : ℝ × (M × V)) (hp : baseFiberInner a i<baseFiberMoment χ μ i p.2) :
      (∀ t,productCouplingPrimitive Ω (fun v => Γ (t,v)) p.2=
        productCouplingPrimitive Ω (fun v => Γ (0,v)) p.2) ∨
      (manifoldExteriorOneForm (productCouplingPrimitive Ω (fun v => Γ (p.1,v))) p.2
          (baseFiberField Ω μ i p.2)=
        -mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,ℝ) (baseFiberMoment χ μ i) p.2 ∧
        ∀ t,productCouplingPrimitive Ω (fun v => Γ (t,v)) p.2 (baseFiberField Ω μ i p.2)=
          productCouplingPrimitive Ω (fun v => Γ (0,v)) p.2 (baseFiberField Ω μ i p.2)) := by
  cases i with
  | none =>
    left
    exact productCouplingPrimitive_stationary Ω Γ p.2
      (fun t => hstation p.2.1 (by change -3/4 < -χ p.2.1 at hp; linarith) t p.2.2)
  | some i =>
    right
    exact productCouplingPrimitive_face hΩ hs (hμ i) hΓ (hInv i) p hp
 theorem horizontal_sublevel_moser
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ)
    (hCb : IsCompact {x | (1/2:ℝ)≤χ x})
    (hstation : ∀ x,χ x<3/4→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i,a i<c i)
    (hY : IsCompact {v | ∀ i,μ i v≤c i})
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈{x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v≤c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
    ∃ Φ Ψ : ℝ × (M × V) → M × V,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Ψ ∧
      (∀ z,Φ (0,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z,Ψ (t,Φ (t,z))=z ∧ Φ (t,Ψ (t,z))=z) ∧
      (∃ C : Set (M × V),IsCompact C ∧ ∀ t z,z∉C→Φ (t,z)=z) ∧
      (∀ z,(∀ t,Γ (t,z.2) z.1=Γ (0,z.2) z.1)→∀ t,Φ (t,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,
        (fun z => Φ (t,z)) '' ({x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v≤c i})=
          {x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v≤c i}) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z∈{x | (1/2:ℝ)≤χ x} ×ˢ {v | ∀ i,μ i v≤c i},∀ u w,
        manifoldPullback Φ (fun s => globalHorizontalCoupling Ω (fun v => Γ (s,v))) t z u w=
          globalHorizontalCoupling Ω (fun v => Γ (0,v)) z u w) := by
  let Λ : ℝ → ManifoldOneForm (E × V) (M × V) :=
    fun t => productCouplingPrimitive Ω (fun v => Γ (t,v))
  have hΛ : SmoothOneFormFamily Λ := productCouplingPrimitive_smooth Ω hΓ
  have hΛe : ∀ t z,manifoldExteriorOneForm (Λ t) z=
      globalHorizontalCoupling Ω (fun v => Γ (t,v)) z := by
    intro t z
    exact productCouplingPrimitive_exterior Ω hs
      (hΓ.comp (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun v : V => v)))) z
  let U := {p : ℝ × (M × V) | (manifoldExteriorOneForm (Λ p.1) p.2).IsInvertible}
  have hU : IsOpen U := manifoldTwoForm_isOpen_nondegenerate
    (Ω := fun s => manifoldExteriorOneForm (Λ s)) (manifoldExteriorOneForm_path_smooth hΛ)
  have hCU : Icc (0:ℝ) 1 ×ˢ {z | ∀ i,baseFiberMoment χ μ i z≤baseFiberOuter c i}⊆U := by
    intro p hp
    rw [baseFiber_domain] at hp
    change (manifoldExteriorOneForm (Λ p.1) p.2).IsInvertible
    rw [hΛe]
    exact hnon p.1 hp.1 p.2 hp.2
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,hfix,hpres,hpull⟩  := manifold_exact_sublevel_moser (E := E × V) (M := M × V)
    hΛ (baseFiberMoment χ μ) (baseFiberMoment_smooth hχ hμ)
    (baseFiberInner a) (baseFiberOuter c) (baseFiber_bounds hac)
    ((baseFiber_domain χ μ c).symm ▸ hCb.prod hY) hU hCU (fun _ hp => hp) (baseFiberField Ω μ)
    (fun i p _ hp => productCouplingPrimitive_baseFiber_face hΩ hs hΓ hstation μ hμ a hInv i p hp)
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,?_,?_,?_⟩
  · intro z hz t
    exact hfix z (productCouplingPrimitive_stationary Ω Γ z hz) t
  · intro t ht
    exact baseFiber_domain χ μ c ▸ (hpres t ht).1
  · intro t ht z hz u w
    have he : (fun s => manifoldExteriorOneForm (Λ s))=
        (fun s => globalHorizontalCoupling Ω (fun v => Γ (s,v))) := funext (fun s => funext (hΛe s))
    simpa only [he,hΛe] using hpull t ht z (by
      change z∈{y | ∀ i,baseFiberMoment χ μ i y≤baseFiberOuter c i}
      rw [baseFiber_domain]
      exact hz) u w

end PackingSufficiencySupport.Hamiltonian
end

end OAI
