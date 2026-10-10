import Mathlib
import OAI.Geometry.BallPacking.Toric.ToricClosedShift

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem globalSurfaceSecondPath_isInvertible_annular {ι : Type*} [Fintype ι]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w,Ω v w= -Ω w v)
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ}
    (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {h : ι → V → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : ι → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {γ : ManifoldOneForm E M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x))
    {W : Set M} (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (τ : ℝ) (hτ : τ∈Icc (0:ℝ) 1) (p : Plane × V) (hp : p.1∈D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1∈W)
    (hbase : 0 < manifoldExteriorOneForm γ (D.handleAnnularCover p.1)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (0,1)))
    (hfp : 0≤D.clock (circleTurn p.1.2))
    (hHp : 0≤H ((Φ.map 1).symm (Φ.map (intervalClock (-b) b p.1.1) p.2)))
    (hclock : ∀ i,0≤deriv (ρ i) p.1.1) (hclock₀ : 0≤deriv ρ₀ p.1.1)
    (hcap : ∀ i,0≤h i (Φ.map (intervalClock (-b) b p.1.1) p.2))
    (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm
      (Φ.map (intervalClock (-b) b p.1.1) p.2)) :
    (globalHorizontalCoupling Ω
      (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v))
      (D.handleAnnularCover p.1,p.2)).IsInvertible := by
  have hpath := (globalSurfaceSecondPrimitive_smooth D hb hbw Φ hK hH hh hρ hρ₀ hlo hhi hΓ).comp
    (f := fun v : V => (τ,v)) (contDiff_const.prodMk contDiff_id)
  have hc := D.annularCover_coefficients_smooth hγ
  have hcurl : 0<fderiv ℝ (D.annularCoverB γ) p.1 (1,0)-
      fderiv ℝ (D.annularCoverA γ) p.1 (0,1) := by
    rw [D.annularCover_curl hp (hγ _ (D.chart.map_source hp))]
    exact hbase
  have hloc := surfaceSecondPath_isInvertible_local hΩ hskew Φ
    (intervalClock_smooth (-b) b) hK hH hh hρ hρ₀ (D.annularCoverDomain_open) hc.1 hc.2
    (((D.clock_smooth.comp circleTurn_smooth).contDiff).comp contDiff_snd) τ hτ p hp hcurl
    (circleWeight_radial_deriv D.clock_smooth p.1) hfp (intervalClock_deriv_nonneg (by linarith) _) hHp hclock hclock₀ hcap hres
  have hgerm := globalSurfaceSecondPrimitive_cover_germ D b Φ K H h ρ ρ₀ Γ γ hW hN τ hp hx
  have hd := euclideanExteriorOneForm_congr_germ hgerm
  apply globalHorizontalCoupling_isInvertible_coordinates hpath
    (D.handleAnnularCover_smoothAt hp) (D.handleAnnularCoverLinearEquiv hp) (by rfl)
  exact hd.symm ▸ hloc

end
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem globalSurfaceSecondPath_isInvertible {κ : Type*} [Fintype κ]
    (D : AnnularHandleData Plane M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0<chartTwoForm Λ c y (1,0) (0,1))
    {r : ℝ} (hr : 0<r) {γ : ManifoldOneForm Plane M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x)
    {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {K H : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M}
    (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W→Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {h : κ → PlanePhase ι → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : κ → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (hclock : ∀ i s,0≤deriv (ρ i) s) (hclock₀ : ∀ s,0≤deriv ρ₀ s)
    (hcap : ∀ v,planeMoments v∈Y→∀ i,0≤h i v)
    (hres : ∀ v,planeMoments v∈Y→0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments) h (Φ.map 1).symm v)
    {τ : ℝ} (hτ : τ∈Icc (0:ℝ) 1) {z : M × PlanePhase ι} (hz : z∈Kbase ×ˢ (planeMoments ⁻¹' Y)) :
    (globalHorizontalCoupling phaseArea (fun v =>
      globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
        (Γ ∘ planeMoments) (τ,v)) z).IsInvertible := by
  by_cases hband : z.1∈D.chart '' band b
  · obtain ⟨q,hq,heq⟩ := D.handleAnnularCover_surjOn (hWA (hBW hband))
    have hS := intervalClock_bounds (-b) b q.1
    have hv := (hΦ _ hS).1 hz.2
    have hm := (hΦ 1 (by norm_num)).2 hv
    have hi := globalSurfaceSecondPath_isInvertible_annular phaseArea_isInvertible phaseArea_skew
      D hb hbw Φ (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth)
      hh hρ hρ₀ hlo hhi (hΓ.comp planeMoments_smooth) hγ hW
      (fun v x hx => hN (planeMoments v) x hx) τ hτ (q,z.2) hq (heq.symm ▸ hBW hband)
      (D.annularCover_positive_exterior hor hΛ hsΛ hpΛ hr hdγ hq) (D.clock_nonneg _) (hHp _ hm)
      (fun i => hclock i q.1) (hclock₀ q.1) (hcap _ hv) (hres _ hv)
    simpa only [heq,Prod.mk.eta] using hi
  · exact globalSurfaceSecondPrimitive_isInvertible_outside D hb hbw Φ hK hH h ρ ρ₀ hlo hhi
      hΓ τ z hband (hbase _ hz.2 _ hz.1)

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

 theorem globalSurfaceSecondPath_moser_endpoint {κ : Type*} [Fintype κ]
    (D : AnnularHandleData Plane M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0<chartTwoForm Λ c y (1,0) (0,1))
    {r : ℝ} (hr : 0<r) {γ : ManifoldOneForm Plane M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x)
    {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {K H : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M} (heD : D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
    (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W→Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {h : κ → PlanePhase ι → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : κ → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (hclock : ∀ i s,0≤deriv (ρ i) s) (hclock₀ : ∀ s,0≤deriv ρ₀ s)
    (hcap : ∀ v,planeMoments v∈Y→∀ i,0≤h i v)
    (hres : ∀ v,planeMoments v∈Y→0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments) h (Φ.map 1).symm v)
    {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j<c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v≤c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v→
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0)
    (hhInv : ∀ j i,CollarInvariant phaseArea (F j ∘ planeMoments) (α j) (h i)) :
    ∃ ψ : (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ,Plane × PlanePhase ι),𝓘(ℝ,Plane × PlanePhase ι)⟯ (M × PlanePhase ι),
      ψ '' (Kbase ×ˢ (planeMoments ⁻¹' Y))=Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
      ψ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y))=interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn ψ
        (globalHorizontalCoupling phaseArea (fun v =>
          globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (1,v)))
        (globalHorizontalCoupling phaseArea (fun v =>
          globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
            (Γ ∘ planeMoments) (1,v)))
        (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      (∃ C : Set (M × PlanePhase ι),IsCompact C ∧ ∀ z,z∉C→ψ z=z) ∧
      (∀ z,z.1∉(D.chart '' band b) ∪ tsupport (D.dual)→ψ z=z) := by
  have hSD : (D.chart '' band b) ∪ tsupport D.dual⊆interior Kbase :=
    union_subset ((D.image_band_subset_target hbw).trans heD) hβD
  have hparam : ∀ x,ContDiff ℝ ∞ (fun p => Γ p x) :=
    fun x => contDiff_iff_contDiffAt.mpr (fun p => hΓ.parameter_contDiffAt p x)
  obtain ⟨ψ,hD,hI,hp,hC,hfix⟩ := horizontal_moser_endpoint phaseArea_isInvertible phaseArea_skew
    (globalSurfaceSecondPrimitive_smooth D hb hbw Φ
      (hK.comp planeMoments_smooth) (hH.comp planeMoments_smooth) hh hρ hρ₀ hlo hhi
      (hΓ.comp planeMoments_smooth))
    ((D.image_band_compact hbw).union D.dual_compact) hSD
    (fun x hx t v => by
      have hb' : x∉D.chart '' band b := fun h => hx (Or.inl h)
      have hf' : D.dual x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
      rw [globalSurfaceSecondPrimitive_off_band D hb Φ _ _ h ρ ρ₀ hlo hhi _ (t,v) hb',
        globalSurfaceSecondPrimitive_off_band D hb Φ _ _ h ρ ρ₀ hlo hhi _ (0,v) hb',hf']
      simp)
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => globalSurfaceSecondPrimitive_collarInvariant D b Φ phaseArea_isInvertible
      phaseArea_skew (((hF j).comp planeMoments_smooth).differentiable (by simp)) (hzero j)
      (toric_collarInvariant (hF j) hK (α j)) (toric_collarInvariant (hF j) hH (α j))
      (hhInv j) ρ ρ₀ (fun x => toric_collarInvariant (hF j) (hparam x) (α j)) t x)
    (fun t ht z hz => globalSurfaceSecondPath_isInvertible D hb hbw hor hΛ hsΛ hpΛ
      hr hγ hdγ hΓ hK hH hHp hbase hW hBW hWA hN Φ hΦ hh hρ hρ₀ hlo hhi hclock hclock₀
      hcap hres ht (by simpa only [hYeq] using hz))
  refine ⟨ψ,?_,?_,?_,hC,hfix⟩
  · simpa only [←hYeq] using hD
  · simpa only [←hYeq] using hI
  · simpa only [←hYeq,globalSurfaceSecondPrimitive_zero] using hp

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

def cylinderAreaCoefficient (Λ : ManifoldTwoForm CylinderModel HandleCylinder) (q : Plane) : ℝ :=
  euclideanPullbackTwoForm (fun _ => Λ) cylinderCover (0,q) (1,0) (0,1)

theorem cylinderAreaCoefficient_periodic (Λ : ManifoldTwoForm CylinderModel HandleCylinder)
    (s : ℝ) : Periodic (fun t => cylinderAreaCoefficient Λ (s,t)) 1 := by
  intro t
  have hq : (s,t+1)=(s,t)+(0,1) := by ext <;> simp
  change Λ (cylinderCover (s,t+1))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t+1) (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t+1) (0,1)) =
    Λ (cylinderCover (s,t))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t) (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (s,t) (0,1))
  rw [hq,cylinderCover_period_one,cylinderCover_derivative_period_one]
  rfl

theorem cylinderAreaCoefficient_rep {Λ : ManifoldTwoForm CylinderModel HandleCylinder}
    (hsk : ∀ z v w,Λ z v w= -Λ z w v) (q : Plane) :
    Λ (cylinderCover q)=cylinderAreaCoefficient Λ q • cylinderAreaForm (cylinderCover q) := by
  let D : Plane →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
  have hd (v : CylinderModel) : D (v.1,circleAngular (circleTurn q.2) v.2)=v :=
    cylinderCover_derivative_right_inverse q v
  have hs : ∀ v w,euclideanPullbackTwoForm (fun _ => Λ) cylinderCover (0,q) v w=
      -euclideanPullbackTwoForm (fun _ => Λ) cylinderCover (0,q) w v := by
    intro v w
    exact hsk _ _ _
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hv := planar_skew_coefficient _ hs
    (v.1,circleAngular (circleTurn q.2) v.2) (w.1,circleAngular (circleTurn q.2) w.2)
  change Λ (cylinderCover q) (D _) (D _)=_ at hv
  rw [hd v,hd w] at hv
  simpa only [cylinderAreaCoefficient,planarArea_apply,cylinderAreaForm_apply,
    smul_apply,smul_eq_mul,cylinderCover] using hv

theorem exists_cylinder_area_primitive {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {Λ : ManifoldTwoForm CylinderModel HandleCylinder}
    (hΛ : ∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞ (chartTwoForm Λ z)
      (extChartAt 𝓘(ℝ,CylinderModel) z z))
    (hsk : ∀ z v w,Λ z v w= -Λ z w v) :
    ∃ γ : ManifoldOneForm CylinderModel HandleCylinder,
      (∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞ (chartOneForm γ z)
        (extChartAt 𝓘(ℝ,CylinderModel) z z)) ∧
      (∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm γ z=Λ z) := by
  let κ : ℝ × Plane → ℝ := fun q => cylinderAreaCoefficient Λ q.2
  have hκ : ContDiffOn ℝ ∞ κ (univ ×ˢ (I ×ˢ univ)) := by
    intro q hq
    have hform := (hΛ (cylinderCover q.2) hq.2.1).comp
      (q.1,extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q.2) (cylinderCover q.2)) contDiffAt_snd
    have hs := parameterEuclideanPullbackTwoForm_contDiffAt (α := fun _ : ℝ => Λ)
      (p := q) hform cylinderCover_smooth.contMDiffAt
    exact ((hs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).contDiffWithinAt
  have hper : ∀ p∈(univ : Set ℝ),∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1 := by
    intro _ _ s _
    exact cylinderAreaCoefficient_periodic Λ s
  refine ⟨cylinderCurvaturePrimitive a κ 0,?_,?_⟩
  · intro z hz
    exact cylinderCurvaturePrimitive_smoothAt isOpen_univ hI hc ha hκ hper (mem_univ 0) hz
  · intro z hz
    let q : Plane := (z.1,shortCircleArgument z.2)
    have he : cylinderCover q=z := by
      apply Prod.ext
      · rfl
      · exact circleTurn_shortCircleArgument z.2
    rw [←he]
    exact (cylinderCurvaturePrimitive_exterior_covered isOpen_univ hI hc ha hκ hper
      (mem_univ 0) hz).trans (cylinderAreaCoefficient_rep hsk q).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_annular_area_primitive {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I)
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞)
    (hsource : e.source=I ×ˢ univ)
    {Λ : ManifoldTwoForm E M} (hΛ : SmoothTwoForm Λ)
    (hsk : ∀ x v w,Λ x v w= -Λ x w v) :
    ∃ γ : ManifoldOneForm E M,
      (∀ x∈e.target,ContDiffAt ℝ ∞ (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x)) ∧
      (∀ x∈e.target,manifoldExteriorOneForm γ x=Λ x) := by
  let Ω : ManifoldTwoForm CylinderModel HandleCylinder :=
    manifoldPullbackTwoForm (E := E) (F := CylinderModel) (fun _ => Λ) e 0
  have hs (z : HandleCylinder) (hz : z.1∈I) : z∈e.source := by
    rw [hsource]; exact ⟨hz,mem_univ _⟩
  have hΩ (z : HandleCylinder) (hz : z.1∈I) :
      ContDiffAt ℝ ∞ (chartTwoForm Ω z) (extChartAt 𝓘(ℝ,CylinderModel) z z) := by
    have hd := e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hs z hz))
    have hform := ((hΛ (e z)).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) (e z)).mem_nhds
        ((extChartAt 𝓘(ℝ,E) (e z)).map_source (mem_extChartAt_source (e z))))).comp
      ((0:ℝ),extChartAt 𝓘(ℝ,E) (e z) (e z)) contDiffAt_snd
    have hp := parameterManifoldPullbackTwoForm_contDiffAt (α := fun _ : ℝ => Λ) hform hd
    exact hp.comp (extChartAt 𝓘(ℝ,CylinderModel) z z)
      (contDiffAt_const.prodMk contDiffAt_id)
  have hskΩ : ∀ z v w,Ω z v w= -Ω z w v := fun _ _ _ => hsk _ _ _
  obtain ⟨γc,hγc,hdγc⟩ := exists_cylinder_area_primitive hI hc ha hΩ hskΩ
  let γ : ManifoldOneForm E M :=
    manifoldPullbackOneForm (E := CylinderModel) (F := E) (fun _ => γc) e.symm 0
  refine ⟨γ,?_,?_⟩
  · intro x hx
    apply partial_inverse_oneForm_smooth e (x := x) ?_ hx
    intro z hz
    exact hγc z (by rw [hsource] at hz; exact hz.1)
  · intro x hx
    apply partial_inverse_oneForm_exterior e (x := x) ?_ ?_ hx
    · intro z hz
      exact hγc z (by rw [hsource] at hz; exact hz.1)
    · intro z hz v w
      have hd := hdγc z (by rw [hsource] at hz; exact hz.1)
      exact congrArg (fun A : CylinderModel →L[ℝ] CylinderModel →L[ℝ] ℝ => A v w) hd

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def clockPrimitive
    (H : AnnularHandleData E M) (b : ℝ) : ManifoldOneForm E M :=
  manifoldPullbackOneForm (E := CylinderModel) (F := E)
    (fun _ => cylinderClockPrimitive (intervalClock (-b) b) H.clock)
    H.chart.symm 0

theorem clockPrimitive_smooth
    (H : AnnularHandleData E M) (b : ℝ)
    {x : M} (hx : x∈H.chart.target) :
    ContDiffAt ℝ ∞ (chartOneForm (H.clockPrimitive b) x)
      (extChartAt 𝓘(ℝ,E) x x) :=
  partial_inverse_oneForm_smooth H.chart
    (fun z _ => cylinderClockPrimitive_smoothAt (intervalClock_smooth (-b) b) H.clock_smooth z) hx

theorem clockPrimitive_exterior
    (H : AnnularHandleData E M) (b : ℝ)
    {x : M} (hx : x∈H.chart.target) :
    manifoldExteriorOneForm (H.clockPrimitive b) x=H.density b x := by
  apply partial_inverse_oneForm_exterior H.chart
    (fun z _ => cylinderClockPrimitive_smoothAt (intervalClock_smooth (-b) b) H.clock_smooth z) _ hx
  intro z hz v w
  rw [cylinderClockPrimitive_exterior (intervalClock_smooth (-b) b) H.clock_smooth]
  exact (H.density_pullback b hz v w).symm

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem clockPrimitive_eq
    (H : AnnularHandleData E M) (b : ℝ) {x : M} (hx : x∈H.chart.target) :
    H.clockPrimitive b x=
      intervalClock (-b) b (H.chart.symm x).1 • H.dual x := by
  let c := H.chart
  let z := c.symm x
  let A : E →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) c.symm x
  let B : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c z
  have hAB : B.comp A=ContinuousLinearMap.id ℝ E := handle_mfderiv_symm_comp c.symm hx
  have hc (v : E) : B (A v)=v := congrArg (fun D : E →L[ℝ] E => D v) hAB
  apply ContinuousLinearMap.ext
  intro v
  have hβ := H.dual_pullback z (c.map_target hx) (A v)
  change H.dual (c z) (B (A v))=H.clock z.2*circleAngular z.2 (A v).2 at hβ
  rw [hc v,show c z=x from c.right_inv hx] at hβ
  change (intervalClock (-b) b z.1*H.clock z.2)*cylinderAngular z (A v)=
    intervalClock (-b) b z.1*H.dual x v
  rw [cylinderAngular_apply,hβ]
  ring

end
section

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_normal_form
    (D : AnnularHandleData E M) (b q : ℝ)
    {Λ : ManifoldTwoForm E M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x v w,Λ x v w= -Λ x w v)
    {H : P → ℝ} (hH : ContDiff ℝ ∞ H) :
    ∃ (γ : ManifoldOneForm E M) (N : P → ManifoldOneForm E M),
      (∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x)) ∧
      (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
      (∀ p,∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (fun z : P × E => chartOneForm (N z.1) x z.2) (p,extChartAt 𝓘(ℝ,E) x x)) ∧
      (∀ p,∀ x∈D.chart.target,
        manifoldExteriorOneForm (N p) x=q • Λ x+H p • D.density b x) ∧
      (∀ p,∀ x∈D.chart.target,N p x=γ x+
        (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) := by
  obtain ⟨γ₀,hγ₀,hdγ₀⟩ := exists_annular_area_primitive isOpen_Ioo (convex_Ioo (-D.width) D.width)
    (a := 0) ⟨by linarith [D.width_pos],D.width_pos⟩ D.chart D.source_eq hΛ hsΛ
  let γ : ManifoldOneForm E M := q • γ₀
  let C := D.clockPrimitive b
  let N : P → ManifoldOneForm E M := fun p => γ+H p • C
  have hγ (x : M) (hx : x∈D.chart.target) :
      ContDiffAt ℝ ∞ (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x) := by
    rw [show chartOneForm γ x=(fun y => q • chartOneForm γ₀ x y) from
      funext (chartOneForm_smul q γ₀ x)]
    exact (contDiffAt_const (c := q)).smul (hγ₀ x hx)
  have hdγ (x : M) (hx : x∈D.chart.target) :
      manifoldExteriorOneForm γ x=q • Λ x := by
    rw [manifoldExteriorOneForm_smul_at q (hγ₀ x hx),hdγ₀ x hx]
  have hC (x : M) (hx : x∈D.chart.target) :
      ContDiffAt ℝ ∞ (chartOneForm C x) (extChartAt 𝓘(ℝ,E) x x) :=
    D.clockPrimitive_smooth b hx
  refine ⟨γ,N,hγ,hdγ,?_,?_,?_⟩
  · intro p x hx
    have h1 := (hγ x hx).comp (p,extChartAt 𝓘(ℝ,E) x x) contDiffAt_snd
    have h2 := (hC x hx).comp (p,extChartAt 𝓘(ℝ,E) x x) contDiffAt_snd
    have h3 := h1.add ((hH.contDiffAt.comp _ contDiffAt_fst).smul h2)
    change ContDiffAt ℝ ∞ (fun z : P × E =>
      chartOneForm γ x z.2+H z.1 • chartOneForm C x z.2) _ at h3
    simpa only [N,chartOneForm_add,chartOneForm_smul] using h3
  · intro p x hx
    have hs : ContDiffAt ℝ ∞ (chartOneForm (H p • C) x) (extChartAt 𝓘(ℝ,E) x x) := by
      rw [show chartOneForm (H p • C) x=(fun y => H p • chartOneForm C x y) from
        funext (chartOneForm_smul (H p) C x)]
      exact (contDiffAt_const (c := H p)).smul (hC x hx)
    change manifoldExteriorOneForm (γ+H p • C) x=_
    rw [manifoldExteriorOneForm_add_at (hγ x hx) hs,hdγ x hx,
      manifoldExteriorOneForm_smul_at (H p) (hC x hx),
      D.clockPrimitive_exterior b hx]
  · intro p x hx
    change γ x+H p • C x=_
    rw [show C x=_ from D.clockPrimitive_eq b hx,smul_smul,mul_comm (H p)]

end

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem normalize_primitive
    (D : AnnularHandleData E M) {V : Set P} (hV : IsOpen V) {b : ℝ} (hb : b<D.width)
    {Γ N : P → ManifoldOneForm E M}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hN : ∀ p∈V,∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (N q.1) x q.2) (p,extChartAt 𝓘(ℝ,E) x x))
    (hcurv : ∀ p∈V,∀ x∈D.chart.target,
      manifoldExteriorOneForm (Γ p) x=manifoldExteriorOneForm (N p) x) :
    ∃ (Γ₁ : P → ManifoldOneForm E M) (L W : Set M),
      IsCompact L ∧ L⊆D.chart.target ∧ IsOpen W ∧
      D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
      (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
        (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
      (∀ p,support (Γ₁ p-Γ p)⊆tsupport D.dual∪L) ∧
      (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
      (∀ p∈V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p∈V,∀ x∈W,Γ₁ p x=N p x) := by
  have hβ (c : M) : ContDiffOn ℝ ∞ (chartOneForm D.dual c)
      (extChartAt 𝓘(ℝ,E) c).target :=
    (D.dual_smooth c).comp (f := fun y => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)
  exact exists_normalized_primitive_on_annular_chart hV isOpen_Ioo
    (convex_Ioo (-D.width) D.width) (a := 0) ⟨by linarith [D.width_pos],D.width_pos⟩
    D.chart D.source_eq (D.image_band_compact hb)
    (image_subset_iff.mpr (fun _ hz => D.chart.map_source (D.band_subset_source hb hz)))
    hΓ hN hcurv hβ D.dual_closed D.dual_compact D.clock_smooth D.clock_integral D.dual_pullback

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
