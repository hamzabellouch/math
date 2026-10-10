import Mathlib
import OAI.Geometry.BallPacking.Moser.AnnularFinalPacking

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem manifoldPullback_of_stationary_germ
    {Φ : ℝ × M → M} {Γ : ℝ → ManifoldOneForm E M} {t : ℝ} {x : M}
    (hΦ : (fun y => Φ (t,y)) =ᶠ[𝓝 x] id)
    (hΓ : Γ t =ᶠ[𝓝 x] Γ 0) :
    manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x =
      manifoldExteriorOneForm (Γ 0) x := by
  have hd : preferredDifferential (E := E) (fun y => Φ (t,y)) x=ContinuousLinearMap.id ℝ E := by
    unfold preferredDifferential
    rw [hΦ.mfderiv_eq,mfderiv_id]
    rfl
  have hv : Φ (t,x)=x := hΦ.eq_of_nhds
  unfold manifoldPullback
  rw [hv,hd]
  ext v w
  change manifoldExteriorOneForm (Γ t) x v w=manifoldExteriorOneForm (Γ 0) x v w
  rw [manifoldExteriorOneForm_congr_germ hΓ]

end
section

variable {M : Type*}

 theorem image_eq_of_fixed_complement {f : M → M} {C D : Set M}
    (hCD : C⊆D) (hC : f '' C=C) (hfix : ∀ x∈D,x∉C→f x=x) : f '' D=D := by
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    by_cases hc : x∈C
    · exact hCD (hC ▸ mem_image_of_mem f hc)
    · simpa only [hfix x hx hc] using hx
  · intro x hx
    by_cases hc : x∈C
    · obtain ⟨y,hy,he⟩ := show x∈f '' C from hC.symm ▸ hc
      exact ⟨y,hCD hy,he⟩
    · exact ⟨x,hx,hfix x hx hc⟩

 theorem image_interior_eq_of_inverse [TopologicalSpace M]
    {f g : M → M} (hf : Continuous f) (hg : Continuous g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    {D : Set M} (hD : f '' D=D) : f '' interior D=interior D := by
  let e : M ≃ₜ M :=
    { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg,
      continuous_toFun := hf, continuous_invFun := hg }
  have he := e.image_interior D
  change f '' interior D=interior (f '' D) at he
  rwa [hD] at he

end

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem horizontal_compact_moser
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
    (hstation : ∀ x,x∉S→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i,a i<c i)
    (hY : IsCompact {v | ∀ i,μ i v≤c i})
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v≤c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
    ∃ Φ Ψ : ℝ × (M × V) → M × V,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × V)) 𝓘(ℝ,E × V) ∞ Ψ ∧
      (∀ z,Φ (0,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z,Ψ (t,Φ (t,z))=z ∧ Φ (t,Ψ (t,z))=z) ∧
      (∃ C : Set (M × V),IsCompact C ∧ ∀ t z,z∉C→Φ (t,z)=z) ∧
      (∀ t z,z.1∉S→Φ (t,z)=z) ∧
      (∀ t∈Icc (0:ℝ) 1,
        (fun z => Φ (t,z)) '' (D ×ˢ {v | ∀ i,μ i v≤c i})=D ×ˢ {v | ∀ i,μ i v≤c i} ∧
        (fun z => Φ (t,z)) '' interior (D ×ˢ {v | ∀ i,μ i v≤c i})=
          interior (D ×ˢ {v | ∀ i,μ i v≤c i})) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v≤c i},∀ u w,
        manifoldPullback Φ (fun s => globalHorizontalCoupling Ω (fun v => Γ (s,v))) t z u w=
          globalHorizontalCoupling Ω (fun v => Γ (0,v)) z u w) := by
  obtain ⟨χ,hχ,hCb,hCbD,hχ1⟩ := exists_base_moser_cutoff (E := E) hS hSD
  let Y : Set V := {v | ∀ i,μ i v≤c i}
  let Cb : Set M := {x | (1/2:ℝ)≤χ x}
  have hSCb : S⊆Cb := by
    intro x hx
    change (1/2:ℝ)≤χ x
    rw [hχ1 x hx]
    norm_num
  have hsmall : ∀ x,χ x<3/4→∀ t v,Γ (t,v) x=Γ (0,v) x := by
    intro x hx t v
    apply hstation x
    intro hs
    rw [hχ1 x hs] at hx
    norm_num at hx
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,hfix,hpres,hpull⟩ := horizontal_sublevel_moser
    hΩ hs hΓ hχ hCb hsmall μ hμ a c hac hY hInv
    (fun t ht z hz => hnon t ht z ⟨hCbD hz.1,hz.2⟩)
  have hf : ∀ t z,z.1∉S→Φ (t,z)=z := fun t z hz => hfix z (fun s => hstation z.1 hz s z.2) t
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hcomp,hf,?_,?_⟩
  · intro t ht
    have hpC : (fun z => Φ (t,z)) '' (Cb ×ˢ Y)=Cb ×ˢ Y := hpres t ht
    have hpD : (fun z => Φ (t,z)) '' (D ×ˢ Y)=D ×ˢ Y :=
      image_eq_of_fixed_complement (prod_mono hCbD Subset.rfl) hpC (by
        intro z hz hzc
        apply hf t z
        intro hs
        exact hzc ⟨hSCb hs,hz.2⟩)
    refine ⟨hpD,?_⟩
    exact image_interior_eq_of_inverse
      (hΦ.continuous.comp (continuous_const.prodMk continuous_id))
      (hΨ.continuous.comp (continuous_const.prodMk continuous_id))
      (fun z => (hi t ht z).1) (fun z => (hi t ht z).2) hpD
  · intro t ht z hz u w
    by_cases hc : z∈Cb ×ˢ Y
    · exact hpull t ht z hc u w
    · have hn : z.1∉S := fun hs => hc ⟨hSCb hs,hz.2⟩
      have hnh : ∀ᶠ y : M × V in 𝓝 z,y.1∉S :=
        continuousAt_fst.eventually (hS.isClosed.isOpen_compl.mem_nhds hn)
      let Λ : ℝ → ManifoldOneForm (E × V) (M × V) :=
        fun t => productCouplingPrimitive Ω (fun v => Γ (t,v))
      have hΛstation : ∀ y : M × V,y.1∉S→Λ t y=Λ 0 y := by
        intro y hy
        change productVerticalLiouville Ω y+(Γ (t,y.2) y.1).comp (ContinuousLinearMap.fst ℝ E V)=
          productVerticalLiouville Ω y+(Γ (0,y.2) y.1).comp (ContinuousLinearMap.fst ℝ E V)
        rw [hstation y.1 hy t y.2]
      have hp := manifoldPullback_of_stationary_germ
        (hnh.mono (fun y hy => hf t y hy))
        (hnh.mono (fun y hy => hΛstation y hy))
      have he : ∀ s,manifoldExteriorOneForm (Λ s)=globalHorizontalCoupling Ω (fun v => Γ (s,v)) := by
        intro s
        funext y
        exact productCouplingPrimitive_exterior Ω hs
          (hΓ.comp (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun v : V => v)))) y
      rw [funext he,he] at hp
      exact congrArg (fun L : (E × V) →L[ℝ] (E × V) →L[ℝ] ℝ => L u w) hp

 theorem horizontal_moser_endpoint
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
    (hstation : ∀ x,x∉S→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i,a i<c i)
    (hY : IsCompact {v | ∀ i,μ i v≤c i})
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v≤c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
    ∃ e : (M × V) ≃ₘ⟮𝓘(ℝ,E × V),𝓘(ℝ,E × V)⟯ (M × V),
      e '' (D ×ˢ {v | ∀ i,μ i v≤c i})=D ×ˢ {v | ∀ i,μ i v≤c i} ∧
      e '' interior (D ×ˢ {v | ∀ i,μ i v≤c i})=interior (D ×ˢ {v | ∀ i,μ i v≤c i}) ∧
      PreservesTwoFormOn e (globalHorizontalCoupling Ω (fun v => Γ (0,v)))
        (globalHorizontalCoupling Ω (fun v => Γ (1,v))) (D ×ˢ {v | ∀ i,μ i v≤c i}) ∧
      (∃ C : Set (M × V),IsCompact C ∧ ∀ z,z∉C→e z=z) ∧
      (∀ z,z.1∉S→e z=z) := by
  obtain ⟨Φ,Ψ,hΦ,hΨ,_,hi,hC,hfix,hpres,hpull⟩ := horizontal_compact_moser
    hΩ hs hΓ hS hSD hstation μ hμ a c hac hY hInv hnon
  have h1 : (1:ℝ)∈Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  let e : (M × V) ≃ₘ⟮𝓘(ℝ,E × V),𝓘(ℝ,E × V)⟯ (M × V) :=
    { toFun := fun z => Φ (1,z)
      invFun := fun z => Ψ (1,z)
      left_inv := fun z => (hi 1 h1 z).1
      right_inv := fun z => (hi 1 h1 z).2
      contMDiff_toFun := hΦ.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hΨ.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨e,(hpres 1 h1).1,(hpres 1 h1).2,(fun z hz u w => hpull 1 h1 z hz u w),?_,?_⟩
  · obtain ⟨C,hc,h⟩ := hC
    exact ⟨C,hc,fun z hz => h 1 z hz⟩
  · exact fun z hz => hfix 1 z hz

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem globalSurfaceFirstPath_isInvertible_annular
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w,Ω v w= -Ω w v)
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {H : V → ℝ} (hH : ContDiff ℝ ∞ H)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {γ : ManifoldOneForm E M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x))
    {W : Set M} (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (ℓ : ℝ) (p : Plane × V) (hp : p.1∈D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1∈W)
    (hbase : 0 < manifoldExteriorOneForm γ (D.handleAnnularCover p.1)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (0,1)))
    (hfp : 0≤D.clock (circleTurn p.1.2))
    (hHp : 0≤H ((Φ.map ℓ).symm (Φ.map (ℓ*intervalClock (-b) b p.1.1) p.2))) :
    (globalHorizontalCoupling Ω
      (fun v => globalSurfaceFirstPrimitive D b Φ H Γ (ℓ,v))
      (D.handleAnnularCover p.1,p.2)).IsInvertible := by
  have hpath := (globalSurfaceFirstPrimitive_smooth D hb hbw Φ hH hΓ).comp
    (f := fun v : V => (ℓ,v)) (contDiff_const.prodMk contDiff_id)
  have hc := D.annularCover_coefficients_smooth hγ
  have hcurl : 0<fderiv ℝ (D.annularCoverB γ) p.1 (1,0)-
      fderiv ℝ (D.annularCoverA γ) p.1 (0,1) := by
    rw [D.annularCover_curl hp (hγ _ (D.chart.map_source hp))]
    exact hbase
  have hloc := surfaceFirstPath_isInvertible_local hΩ hskew Φ
    (intervalClock_smooth (-b) b) hH (D.annularCoverDomain_open) hc.1 hc.2
    (((D.clock_smooth.comp circleTurn_smooth).contDiff).comp contDiff_snd) ℓ p hp hcurl
    (circleWeight_radial_deriv D.clock_smooth p.1) hfp (intervalClock_deriv_nonneg (by linarith) _) hHp
  have hgerm := globalSurfaceFirstPrimitive_cover_germ D b Φ H Γ γ hW hN ℓ hp hx
  have hd := euclideanExteriorOneForm_congr_germ hgerm
  apply globalHorizontalCoupling_isInvertible_coordinates hpath
    (D.handleAnnularCover_smoothAt hp) (D.handleAnnularCoverLinearEquiv hp) (by rfl)
  exact hd.symm ▸ hloc

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Topology
open scoped Manifold
open Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem toric_differential_eq {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z : PlanePhase ι) :
    fderiv ℝ (fun w => F (planeMoments w)) z =
      spatialDifferential (toricHamiltonian F) (t,z) := by
  have hs : ContDiff ℝ ∞ (toricHamiltonian F) := toricHamiltonian_smooth hF
  have hd := (hs.differentiable (by simp) (t,z)).hasFDerivAt.comp z
    ((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z))
  exact hd.fderiv

theorem toric_covectors_commute {F G : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (z : PlanePhase ι) :
    fderiv ℝ (fun w => G (planeMoments w)) z
      (phaseArea.inverse (fderiv ℝ (fun w => F (planeMoments w)) z))=0 := by
  let X := hamiltonianField phaseArea (toricHamiltonian F) (0,z)
  have hX : X = -phaseArea.inverse (fderiv ℝ (fun w => F (planeMoments w)) z) := by
    rw [toric_differential_eq hF 0 z]
    rfl
  have hd := (hG.differentiable (by simp) (planeMoments z)).hasFDerivAt.comp z
    (planeMoments_hasFDerivAt z)
  change HasFDerivAt (fun w => G (planeMoments w)) _ z at hd
  have hm : fderiv ℝ planeMoments z X=0 := toricHamiltonian_preserves_moments hF (0,z)
  have hh : fderiv ℝ (fun w => G (planeMoments w)) z X=0 := by
    rw [hd.fderiv]
    change fderiv ℝ G (planeMoments z) (momentDifferential z X)=0
    rw [←(planeMoments_hasFDerivAt z).fderiv,hm,map_zero]
  rw [hX,map_neg] at hh
  exact neg_eq_zero.mp hh

theorem toric_twoCovectorForm_isInvertible {F G : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (z : PlanePhase ι)
    {c : ℝ} (hc : 0<c) :
    (twoCovectorForm phaseArea c (fderiv ℝ (fun w => F (planeMoments w)) z)
      (fderiv ℝ (fun w => G (planeMoments w)) z)).IsInvertible :=
  twoCovectorForm_isInvertible phaseArea_isInvertible phaseArea_skew hc.ne'
    _ _ (toric_covectors_commute hF hG z)

def toricHorizontalCoefficient (F : Plane × (ι → ℝ) → ℝ)
    (x : Plane × PlanePhase ι) : ℝ := F (x.1,planeMoments x.2)

omit [DecidableEq ι] in
@[fun_prop] theorem toricHorizontalCoefficient_smooth {F : Plane × (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (toricHorizontalCoefficient F) :=
  hF.comp (contDiff_fst.prodMk (planeMoments_smooth.comp contDiff_snd))

omit [DecidableEq ι] in
theorem toricHorizontalCoefficient_vertical {F : Plane × (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (x : Plane × PlanePhase ι) :
    (fderiv ℝ (toricHorizontalCoefficient F) x).comp (ContinuousLinearMap.inr ℝ Plane (PlanePhase ι)) =
      fderiv ℝ (fun z => F (x.1,planeMoments z)) x.2 := by
  have hd := ((toricHorizontalCoefficient_smooth hF).differentiable (by simp) x).hasFDerivAt.comp x.2
    ((hasFDerivAt_const (𝕜 := ℝ) x.1 x.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) x.2))
  exact hd.fderiv.symm

theorem toric_horizontalCoupling_isInvertible {F G : Plane × (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (x : Plane × PlanePhase ι)
    (hpositive : 0 < fderiv ℝ (toricHorizontalCoefficient G) x ((1,0),0) -
      fderiv ℝ (toricHorizontalCoefficient F) x ((0,1),0)) :
    (horizontalCoupling phaseArea (toricHorizontalCoefficient F) (toricHorizontalCoefficient G) x).IsInvertible := by
  rw [horizontalCoupling_eq ((toricHorizontalCoefficient_smooth hF).differentiable (by simp) x)
    ((toricHorizontalCoefficient_smooth hG).differentiable (by simp) x),
    toricHorizontalCoefficient_vertical hF,toricHorizontalCoefficient_vertical hG]
  apply toric_twoCovectorForm_isInvertible (F := fun p => F (x.1,p))
    (G := fun p => G (x.1,p)) _ _ x.2 hpositive
  · exact hF.comp (contDiff_const.prodMk contDiff_id)
  · exact hG.comp (contDiff_const.prodMk contDiff_id)

omit [DecidableEq ι] in
theorem toricHorizontalCoefficient_contDiffAt {F : Plane × (ι → ℝ) → ℝ}
    {U : Set Plane} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {x : Plane × PlanePhase ι} (hx : x.1∈U) :
    ContDiffAt ℝ ∞ (toricHorizontalCoefficient F) x :=
  (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx,mem_univ _⟩)).comp x
    (contDiffAt_fst.prodMk (planeMoments_smooth.contDiffAt.comp x contDiffAt_snd))

omit [DecidableEq ι] in
theorem toricHorizontalCoefficient_base {F : Plane × (ι → ℝ) → ℝ}
    {U : Set Plane} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ))
    {x : Plane × PlanePhase ι} (hx : x.1∈U) (w : Plane) :
    fderiv ℝ (toricHorizontalCoefficient F) x (w,0)=
      fderiv ℝ (fun y => F (y,planeMoments x.2)) x.1 w := by
  have hi : HasFDerivAt (fun y : Plane => (y,x.2))
      (ContinuousLinearMap.inl ℝ Plane (PlanePhase ι)) x.1 :=
    (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const x.2 x.1)
  have h := ((toricHorizontalCoefficient_contDiffAt hU hF hx).differentiableAt (by simp)).hasFDerivAt.comp x.1 hi
  exact (congrArg (fun L : Plane →L[ℝ] ℝ => L w) h.fderiv).symm

theorem toric_horizontalCoupling_isInvertible_local {F G : Plane × (ι → ℝ) → ℝ}
    {U : Set Plane} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (hG : ContDiffOn ℝ ∞ G (U ×ˢ univ))
    (x : Plane × PlanePhase ι) (hx : x.1∈U)
    (hpositive : 0 < fderiv ℝ (toricHorizontalCoefficient G) x ((1,0),0) -
      fderiv ℝ (toricHorizontalCoefficient F) x ((0,1),0)) :
    (horizontalCoupling phaseArea (toricHorizontalCoefficient F) (toricHorizontalCoefficient G) x).IsInvertible := by
  obtain ⟨r,hr,hrU,he⟩ := exists_smooth_local_identity
    ((hU.prod isOpen_univ).mem_nhds (show (x.1,planeMoments x.2)∈U ×ˢ univ from ⟨hx,mem_univ _⟩))
  let F' := F ∘ r
  let G' := G ∘ r
  have hF' : ContDiff ℝ ∞ F' := hF.comp_contDiff hr hrU
  have hG' : ContDiff ℝ ∞ G' := hG.comp_contDiff hr hrU
  have hm : ContinuousAt (fun y : Plane × PlanePhase ι => (y.1,planeMoments y.2)) x :=
    continuousAt_fst.prodMk (planeMoments_smooth.continuous.continuousAt.comp continuousAt_snd)
  have heF : toricHorizontalCoefficient F' =ᶠ[𝓝 x] toricHorizontalCoefficient F := by
    filter_upwards [hm.preimage_mem_nhds he] with y hy
    exact congrArg F hy
  have heG : toricHorizontalCoefficient G' =ᶠ[𝓝 x] toricHorizontalCoefficient G := by
    filter_upwards [hm.preimage_mem_nhds he] with y hy
    exact congrArg G hy
  have hp' : 0 < fderiv ℝ (toricHorizontalCoefficient G') x ((1,0),0) -
      fderiv ℝ (toricHorizontalCoefficient F') x ((0,1),0) := by
    rwa [heF.fderiv_eq,heG.fderiv_eq]
  have hi := toric_horizontalCoupling_isInvertible hF' hG' x hp'
  have hform : horizontalOneForm (toricHorizontalCoefficient F') (toricHorizontalCoefficient G') =ᶠ[𝓝 x]
      horizontalOneForm (toricHorizontalCoefficient F) (toricHorizontalCoefficient G) := by
    filter_upwards [heF,heG] with y hyF hyG
    simp only [horizontalOneForm,hyF,hyG]
  unfold horizontalCoupling at hi ⊢
  rwa [euclideanExteriorOneForm_congr_germ hform] at hi

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

def toricChartA (Γ : (ι → ℝ) → ManifoldOneForm Plane M) (c : M) (q : Plane × (ι → ℝ)) :=
  chartOneForm (Γ q.2) c q.1 (1,0)
def toricChartB (Γ : (ι → ℝ) → ManifoldOneForm Plane M) (c : M) (q : Plane × (ι → ℝ)) :=
  chartOneForm (Γ q.2) c q.1 (0,1)

omit [DecidableEq ι] [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem toricChart_coefficients_smooth {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (c : M) :
    ContDiffOn ℝ ∞ (toricChartA Γ c) ((extChartAt 𝓘(ℝ,Plane) c).target ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (toricChartB Γ c) ((extChartAt 𝓘(ℝ,Plane) c).target ×ˢ univ) := by
  have hs := (hΓ c).comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (show MapsTo (fun q : Plane × (ι → ℝ) => (q.2,q.1))
      ((extChartAt 𝓘(ℝ,Plane) c).target ×ˢ univ) (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target)
      from fun _ hq => ⟨mem_univ _,hq.1⟩)
  exact ⟨hs.clm_apply contDiffOn_const,hs.clm_apply contDiffOn_const⟩

omit [DecidableEq ι] in
theorem toricChart_curl {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (c : M) {x : Plane × PlanePhase ι}
    (hx : x.1∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    fderiv ℝ (toricHorizontalCoefficient (toricChartB Γ c)) x ((1,0),0)-
      fderiv ℝ (toricHorizontalCoefficient (toricChartA Γ c)) x ((0,1),0)=
      chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments x.2))) c x.1 (1,0) (0,1) := by
  have hs := toricChart_coefficients_smooth hΓ c
  rw [toricHorizontalCoefficient_base (isOpen_extChartAt_target c) hs.2 hx,
    toricHorizontalCoefficient_base (isOpen_extChartAt_target c) hs.1 hx]
  have hα := (hΓ.spatial_smooth (planeMoments x.2) c hx).differentiableAt (by simp)
  rw [manifoldExteriorOneForm_chart (fun z y hy =>
    (hΓ.spatial_smooth (planeMoments x.2) z hy).contDiffWithinAt) hx]
  change fderiv ℝ (fun y => chartOneForm (Γ (planeMoments x.2)) c y (0,1)) x.1 (1,0)-
      fderiv ℝ (fun y => chartOneForm (Γ (planeMoments x.2)) c y (1,0)) x.1 (0,1)=_
  rw [fderiv_clm_eval hα,fderiv_clm_eval hα]
  rfl

omit [DecidableEq ι] in
theorem toricChart_horizontal_pullback (Γ : (ι → ℝ) → ManifoldOneForm Plane M)
    (c : M) {x : Plane × PlanePhase ι} (hx : x.1∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    euclideanPullbackOneForm (fun _ => productHorizontalLift (Γ ∘ planeMoments))
      (flatProductMap (extChartAt 𝓘(ℝ,Plane) c).symm) (0,x)=
    horizontalOneForm (toricHorizontalCoefficient (toricChartA Γ c))
      (toricHorizontalCoefficient (toricChartB Γ c)) x := by
  have hg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hx)
  apply ContinuousLinearMap.ext
  intro v
  rw [productHorizontalLift_pullback_apply _ hg]
  have he : euclideanPullbackOneForm (fun _ => (Γ ∘ planeMoments) x.2)
      (extChartAt 𝓘(ℝ,Plane) c).symm (0,x.1)=chartOneForm (Γ (planeMoments x.2)) c x.1 := by
    simp only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hx,Function.comp_apply]
  rw [he,horizontalOneForm_apply]
  let L := chartOneForm (Γ (planeMoments x.2)) c x.1
  change L v.1=L (1,0)*v.1.1+L (0,1)*v.1.2
  have hv : v.1=v.1.1 • (1,0)+v.1.2 • (0,1) := by ext <;> simp
  rw [show L v.1=L (v.1.1 • (1,0)+v.1.2 • (0,1)) from congrArg L hv]
  simp only [map_add,map_smul,smul_eq_mul]
  ring

theorem globalToricCoupling_isInvertible_chart {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (c : M) {x : Plane × PlanePhase ι}
    (hx : x.1∈(extChartAt 𝓘(ℝ,Plane) c).target)
    (hpos : 0 < chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments x.2))) c x.1 (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)
      ((extChartAt 𝓘(ℝ,Plane) c).symm x.1,x.2)).IsInvertible := by
  have hs := toricChart_coefficients_smooth hΓ c
  have hp : 0 < fderiv ℝ (toricHorizontalCoefficient (toricChartB Γ c)) x ((1,0),0)-
      fderiv ℝ (toricHorizontalCoefficient (toricChartA Γ c)) x ((0,1),0) := by
    rwa [toricChart_curl hΓ c hx]
  have hi := toric_horizontalCoupling_isInvertible_local
    (isOpen_extChartAt_target c) hs.1 hs.2 x hx hp
  have hg := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hx)
  have hC : (chartDifferential (E := Plane) c ((extChartAt 𝓘(ℝ,Plane) c).symm x.1)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,Plane))
      ((extChartAt 𝓘(ℝ,Plane) c).map_target hx) using 1
  have hD : (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (extChartAt 𝓘(ℝ,Plane) c).symm x.1).IsInvertible := by
    rw [← chartDifferential_inverse hx]
    exact hC.inverse
  obtain ⟨d,hd⟩ := hD
  have he : (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift (Γ ∘ planeMoments))
        (flatProductMap (extChartAt 𝓘(ℝ,Plane) c).symm) (0,y)) =ᶠ[𝓝 x]
      horizontalOneForm (toricHorizontalCoefficient (toricChartA Γ c))
        (toricHorizontalCoefficient (toricChartB Γ c)) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target c).mem_nhds hx)] with y hy
    exact toricChart_horizontal_pullback Γ c hy
  have hext := euclideanExteriorOneForm_congr_germ he
  apply globalHorizontalCoupling_isInvertible_coordinates (hΓ.comp planeMoments_smooth) hg d hd
  exact hext.symm ▸ hi

theorem globalToricCoupling_isInvertible {Γ : (ι → ℝ) → ManifoldOneForm Plane M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × PlanePhase ι)
    (hpos : 0 < chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments z.2)))
      z.1 (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments) z).IsInvertible := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) z.1
  have hi := globalToricCoupling_isInvertible_chart hΓ z.1
    (x := (extChartAt 𝓘(ℝ,Plane) z.1 z.1,z.2)) ((extChartAt 𝓘(ℝ,Plane) z.1).map_source hx) hpos
  simpa only [(extChartAt 𝓘(ℝ,Plane) z.1).left_inv hx,Prod.mk.eta] using hi

end PackingSufficiencySupport.Hamiltonian
end

end OAI
