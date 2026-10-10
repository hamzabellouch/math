import Mathlib
import OAI.Geometry.BallPacking.Toric.StationaryManifoldPullback

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def toricClosedShift (Γ : P → ManifoldOneForm E M) (J : P → ℝ)
    (β : ManifoldOneForm E M) (t : ℝ) (p : P) : ManifoldOneForm E M :=
  Γ p+(t*J p) • β

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem toricClosedShift_smooth {Γ : P → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {J : P → ℝ} (hJ : ContDiff ℝ ∞ J) {β : ManifoldOneForm E M}
    (hβ : SmoothOneFormFamily (fun _ : ℝ => β)) (t : ℝ) :
    SmoothOneFormFamily (toricClosedShift Γ J β t) := by
  exact hΓ.add ((hβ.comp (f := fun _ : P => (0:ℝ)) contDiff_const).smul (contDiff_const.mul hJ))

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem toricClosedShift_exterior {Γ : P → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    (J : P → ℝ) {β : ManifoldOneForm E M}
    (hβ : SmoothOneFormFamily (fun _ : ℝ => β)) (hdβ : ∀ x,manifoldExteriorOneForm β x=0)
    (t : ℝ) (p : P) : manifoldExteriorOneForm (toricClosedShift Γ J β t p)=manifoldExteriorOneForm (Γ p) := by
  funext x
  have hx := (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source (I := 𝓘(ℝ,E)) x)
  have ha := hΓ.spatial_smooth p x hx
  have hb := hβ.spatial_smooth 0 x hx
  have hs : ContDiffAt ℝ ∞ (chartOneForm ((t*J p) • β) x) (extChartAt 𝓘(ℝ,E) x x) := by
    have he : chartOneForm ((t*J p) • β) x=(t*J p) • chartOneForm β x := funext (chartOneForm_smul _ _ _)
    rw [he]
    exact contDiffAt_const.smul hb
  change manifoldExteriorOneForm (Γ p+(t*J p) • β) x=_
  rw [manifoldExteriorOneForm_add_at ha hs,manifoldExteriorOneForm_smul_at _ hb,hdβ]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change manifoldExteriorOneForm (Γ p) x v w+(t*J p)*0=manifoldExteriorOneForm (Γ p) x v w
  simp only [mul_zero,add_zero]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem globalSurfaceFirstPrimitive_isInvertible_outside
    (D : AnnularHandleData Plane M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι))) (H : (ι → ℝ) → ℝ)
    {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    (ℓ : ℝ) (z : M × PlanePhase ι) (hn : z.1∉D.chart '' band b)
    (hp : 0 < chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments z.2))) z.1
      (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (fun v =>
      globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (ℓ,v)) z).IsInvertible := by
  have heq := globalHorizontalCoupling_congr_germ phaseArea
    (Γ := fun v => globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (ℓ,v))
    (Γ' := Γ ∘ planeMoments) (z := z) (by
      filter_upwards [((D.image_band_compact hbw).isClosed.isOpen_compl).mem_nhds hn] with x hx
      intro v
      exact globalSurfaceFirstPrimitive_off_band D hb Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (ℓ,v) hx)
  exact heq.symm ▸ globalToricCoupling_isInvertible hΓ z hp

 theorem globalSurfaceSecondPrimitive_isInvertible_outside {κ : Type*} [Fintype κ]
    (D : AnnularHandleData Plane M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    {K H : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (h : κ → PlanePhase ι → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s,s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    (τ : ℝ) (z : M × PlanePhase ι) (hn : z.1∉D.chart '' band b)
    (hp : 0 < chartTwoForm (manifoldExteriorOneForm (Γ (planeMoments z.2))) z.1
      (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1)) :
    (globalHorizontalCoupling phaseArea (fun v =>
      globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments)
        h ρ ρ₀ (Γ ∘ planeMoments) (τ,v)) z).IsInvertible := by
  have hβ := D.dual_smooth
  let Γ' := toricClosedShift Γ (K-H) (D.dual) τ
  have hs : SmoothOneFormFamily Γ' := toricClosedShift_smooth hΓ (hK.sub hH) hβ τ
  have hp' : 0 < chartTwoForm (manifoldExteriorOneForm (Γ' (planeMoments z.2))) z.1
      (extChartAt 𝓘(ℝ,Plane) z.1 z.1) (1,0) (0,1) := by
    change 0 < chartTwoForm (manifoldExteriorOneForm (toricClosedShift Γ (K-H) (D.dual) τ
      (planeMoments z.2))) z.1 _ _ _
    rw [toricClosedShift_exterior hΓ _ hβ D.dual_closed]
    exact hp
  have heq := globalHorizontalCoupling_congr_germ phaseArea
    (Γ := fun v => globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments)
      h ρ ρ₀ (Γ ∘ planeMoments) (τ,v))
    (Γ' := Γ' ∘ planeMoments) (z := z) (by
      filter_upwards [((D.image_band_compact hbw).isClosed.isOpen_compl).mem_nhds hn] with x hx
      intro v
      exact globalSurfaceSecondPrimitive_off_band D hb Φ (K ∘ planeMoments) (H ∘ planeMoments)
        h ρ ρ₀ hlo hhi (Γ ∘ planeMoments) (τ,v) hx)
  exact heq.symm ▸ globalToricCoupling_isInvertible hs z hp'

 theorem globalSurfaceFirstPath_isInvertible
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
    {H : (ι → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
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
    {ℓ : ℝ} (hℓ : ℓ∈Icc (0:ℝ) 1) {z : M × PlanePhase ι} (hz : z∈Kbase ×ˢ (planeMoments ⁻¹' Y)) :
    (globalHorizontalCoupling phaseArea (fun v =>
      globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (ℓ,v)) z).IsInvertible := by
  by_cases hband : z.1∈D.chart '' band b
  · obtain ⟨q,hq,heq⟩ := D.handleAnnularCover_surjOn (hWA (hBW hband))
    have hS := intervalClock_bounds (-b) b q.1
    have ht : ℓ*intervalClock (-b) b q.1∈Icc (0:ℝ) 1 :=
      ⟨mul_nonneg hℓ.1 hS.1,(mul_le_mul hℓ.2 hS.2 hS.1 (by norm_num)).trans (by norm_num)⟩
    have hm := (hΦ ℓ hℓ).2 ((hΦ _ ht).1 hz.2)
    have hi := globalSurfaceFirstPath_isInvertible_annular phaseArea_isInvertible phaseArea_skew
      D hb hbw Φ (hH.comp planeMoments_smooth) (hΓ.comp planeMoments_smooth) hγ hW
      (fun v x hx => hN (planeMoments v) x hx) ℓ (q,z.2) hq (heq.symm ▸ hBW hband)
      (D.annularCover_positive_exterior hor hΛ hsΛ hpΛ hr hdγ hq) (D.clock_nonneg _) (hHp _ hm)
    simpa only [heq,Prod.mk.eta] using hi
  · exact globalSurfaceFirstPrimitive_isInvertible_outside D hb hbw Φ H hΓ ℓ z hband
      (hbase _ hz.2 _ hz.1)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {c : ℝ}

 theorem surfaceSuspensionCoefficient_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    (S : ℝ → ℝ) (t s : ℝ) :
    CollarInvariant Ω μ c (fun v => surfaceSuspensionCoefficient Φ S ((t,v),s)) :=
  ((Φ.hamiltonian_collarInvariant hΩ hs hμ hzero (t*S s)).pullback
    Φ hΩ hμ hzero (t*S s)).const_mul t

 theorem surfaceFirstCorrectionCoefficient_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {H : V → ℝ} (hH : CollarInvariant Ω μ c H) (S : ℝ → ℝ) (t s : ℝ) :
    CollarInvariant Ω μ c (fun v => surfaceFirstCorrectionCoefficient Φ S H ((t,v),s)) :=
  (((hH.inverse_pullback Φ hΩ hμ hzero t).pullback Φ hΩ hμ hzero (t*S s)).sub hH).const_mul (S s)

variable {κ : Type*} [Fintype κ]
 theorem surfaceSecondExtraCoefficient_collarInvariant
    (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {K H : V → ℝ} (hK : CollarInvariant Ω μ c K) (hH : CollarInvariant Ω μ c H)
    {h : κ → V → ℝ} (hh : ∀ i,CollarInvariant Ω μ c (h i))
    (S : ℝ → ℝ) (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (t s : ℝ) :
    CollarInvariant Ω μ c (fun v => surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀ ((t,v),s)) := by
  have hr : CollarInvariant Ω μ c (surfaceRemainder K H h (Φ.map 1).symm) :=
    (((hK.inverse_pullback Φ hΩ hμ hzero 1).sub hK).add hH).sub
      (CollarInvariant.sum Finset.univ (fun i _ => hh i))
  have hf : CollarInvariant Ω μ c (fun v => surfaceFinalLayer (K-H) h
      (surfaceRemainder K H h (Φ.map 1).symm) ρ ρ₀ (s,v)) :=
    ((hK.sub hH).add (CollarInvariant.sum Finset.univ
      (fun i _ => (hh i).const_mul (ρ i s)))).add (hr.const_mul (ρ₀ s))
  have hfirst : CollarInvariant Ω μ c (fun v => surfaceFirstLayer S H (Φ.map 1).symm (s,v)) :=
    (hH.inverse_pullback Φ hΩ hμ hzero 1).const_mul (S s)
  have hi : CollarInvariant Ω μ c (fun v => surfaceInterpolatedLayer S K H h
      (Φ.map 1).symm ρ ρ₀ t (s,v)) :=
    (hfirst.const_mul (1-t)).add (hf.const_mul t)
  exact (((hi.pullback Φ hΩ hμ hzero (S s)).sub (hH.const_mul (S s))).sub
    ((hK.sub hH).const_mul t)).sub
    (surfaceFirstCorrectionCoefficient_collarInvariant Φ hΩ hμ hzero hH S 1 s)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem globalSurfaceFirstPrimitive_collarInvariant
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {H : V → ℝ} (hH : CollarInvariant Ω μ c H) {Γ : V → ManifoldOneForm E M}
    (hΓ : ∀ x,CollarInvariant Ω μ c (fun v => Γ v x)) (t : ℝ) (x : M) :
    CollarInvariant Ω μ c (fun v => globalSurfaceFirstPrimitive e a b f Φ H Γ (t,v) x) := by
  by_cases hx : x∈(handleAnnularChart e a).target
  · simpa only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_inside hx,
      handleFirstCorrection] using
      (hΓ x).add (((surfaceSuspensionCoefficient_collarInvariant Φ hΩ hs hμ hzero
        (intervalClock (-b) b) t ((handleAnnularChart e a).symm x).1).smul
          (CollarInvariant.const (globalHandleRadialForm e b x))).add
        ((surfaceFirstCorrectionCoefficient_collarInvariant Φ hΩ hμ hzero hH
          (intervalClock (-b) b) t ((handleAnnularChart e a).symm x).1).smul
            (CollarInvariant.const (globalHandleForm e f x))))
  · simpa only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_outside hx,add_zero]
      using hΓ x

 theorem globalSurfaceSecondPrimitive_collarInvariant
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {K H : V → ℝ} (hK : CollarInvariant Ω μ c K) (hH : CollarInvariant Ω μ c H)
    {h : κ → V → ℝ} (hh : ∀ i,CollarInvariant Ω μ c (h i))
    (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ) {Γ : V → ManifoldOneForm E M}
    (hΓ : ∀ x,CollarInvariant Ω μ c (fun v => Γ v x)) (t : ℝ) (x : M) :
    CollarInvariant Ω μ c (fun v => globalSurfaceSecondPrimitive e a b f Φ K H h ρ ρ₀ Γ (t,v) x) := by
  have hfirst := globalSurfaceFirstPrimitive_collarInvariant e a b f Φ hΩ hs hμ hzero hH hΓ 1 x
  have hbg := hfirst.add (((hK.sub hH).const_mul t).smul
    (CollarInvariant.const (globalHandleForm e f x)))
  by_cases hx : x∈(handleAnnularChart e a).target
  · simpa only [globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_inside hx,handleSecondExtra] using
      hbg.add ((surfaceSecondExtraCoefficient_collarInvariant Φ hΩ hμ hzero hK hH hh
        (intervalClock (-b) b) ρ ρ₀ t ((handleAnnularChart e a).symm x).1).smul
          (CollarInvariant.const (globalHandleForm e f x)))
  · simpa only [globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_outside hx,add_zero] using hbg

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {μ : V → ℝ} {c : ℝ}

variable {κ : Type*} [Fintype κ]
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem globalSurfaceFirstPrimitive_collarInvariant
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {H : V → ℝ} (hH : CollarInvariant Ω μ c H) {Γ : V → ManifoldOneForm E M}
    (hΓ : ∀ x,CollarInvariant Ω μ c (fun v => Γ v x)) (t : ℝ) (x : M) :
    CollarInvariant Ω μ c (fun v => globalSurfaceFirstPrimitive D b Φ H Γ (t,v) x) := by
  by_cases hx : x∈D.chart.target
  · simpa only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_inside hx,
      handleFirstCorrection] using
      (hΓ x).add (((surfaceSuspensionCoefficient_collarInvariant Φ hΩ hs hμ hzero
        (intervalClock (-b) b) t (D.chart.symm x).1).smul
          (CollarInvariant.const (D.radial b x))).add
        ((surfaceFirstCorrectionCoefficient_collarInvariant Φ hΩ hμ hzero hH
          (intervalClock (-b) b) t (D.chart.symm x).1).smul
            (CollarInvariant.const (D.dual x))))
  · simpa only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_outside hx,add_zero]
      using hΓ x

 theorem globalSurfaceSecondPrimitive_collarInvariant
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (hΩ : Ω.IsInvertible)
    (hs : ∀ u v,Ω u v= -Ω v u) (hμ : Differentiable ℝ μ)
    (hzero : ∀ t v,c<μ v→fderiv ℝ μ v (hamiltonianField Ω Φ.hamiltonian (t,v))=0)
    {K H : V → ℝ} (hK : CollarInvariant Ω μ c K) (hH : CollarInvariant Ω μ c H)
    {h : κ → V → ℝ} (hh : ∀ i,CollarInvariant Ω μ c (h i))
    (ρ : κ → ℝ → ℝ) (ρ₀ : ℝ → ℝ) {Γ : V → ManifoldOneForm E M}
    (hΓ : ∀ x,CollarInvariant Ω μ c (fun v => Γ v x)) (t : ℝ) (x : M) :
    CollarInvariant Ω μ c (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (t,v) x) := by
  have hfirst := globalSurfaceFirstPrimitive_collarInvariant D b Φ hΩ hs hμ hzero hH hΓ 1 x
  have hbg := hfirst.add (((hK.sub hH).const_mul t).smul
    (CollarInvariant.const (D.dual x)))
  by_cases hx : x∈D.chart.target
  · simpa only [globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_inside hx,handleSecondExtra] using
      hbg.add ((surfaceSecondExtraCoefficient_collarInvariant Φ hΩ hμ hzero hK hH hh
        (intervalClock (-b) b) ρ ρ₀ t (D.chart.symm x).1).smul
          (CollarInvariant.const (D.dual x)))
  · simpa only [globalSurfaceSecondPrimitive,Pi.add_apply,Pi.smul_apply,
      extendManifoldOneForm_outside hx,add_zero] using hbg

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

 theorem globalSurfaceFirstPath_moser_endpoint
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
    {H : (ι → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M} (heD : D.chart.target⊆interior Kbase)
    (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W→Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j<c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v≤c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v→
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
    ∃ ψ : (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ,Plane × PlanePhase ι),𝓘(ℝ,Plane × PlanePhase ι)⟯ (M × PlanePhase ι),
      ψ '' (Kbase ×ˢ (planeMoments ⁻¹' Y))=Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
      ψ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y))=interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn ψ (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments))
        (globalHorizontalCoupling phaseArea (fun v =>
          globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (1,v)))
        (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      (∃ C : Set (M × PlanePhase ι),IsCompact C ∧ ∀ z,z∉C→ψ z=z) ∧
      (∀ z,z.1∉D.chart '' band b→ψ z=z) := by
  have hSD : D.chart '' band b⊆interior Kbase :=
    (D.image_band_subset_target hbw).trans heD
  have hparam : ∀ x,ContDiff ℝ ∞ (fun p => Γ p x) :=
    fun x => contDiff_iff_contDiffAt.mpr (fun p => hΓ.parameter_contDiffAt p x)
  obtain ⟨ψ,hD,hI,hp,hC,hfix⟩ := horizontal_moser_endpoint phaseArea_isInvertible phaseArea_skew
    (globalSurfaceFirstPrimitive_smooth D hb hbw Φ
      (hH.comp planeMoments_smooth) (hΓ.comp planeMoments_smooth))
    (D.image_band_compact hbw) hSD
    (fun x hx t v => by rw [globalSurfaceFirstPrimitive_off_band D hb Φ _ _ (t,v) hx,
      globalSurfaceFirstPrimitive_zero])
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => globalSurfaceFirstPrimitive_collarInvariant D b Φ phaseArea_isInvertible
      phaseArea_skew (((hF j).comp planeMoments_smooth).differentiable (by simp)) (hzero j)
      (toric_collarInvariant (hF j) hH (α j))
      (fun x => toric_collarInvariant (hF j) (hparam x) (α j)) t x)
    (fun t ht z hz => globalSurfaceFirstPath_isInvertible D hb hbw hor hΛ hsΛ hpΛ
      hr hγ hdγ hΓ hH hHp hbase hW hBW hWA hN Φ hΦ ht (by simpa only [hYeq] using hz))
  refine ⟨ψ,?_,?_,?_,hC,hfix⟩
  · simpa only [←hYeq] using hD
  · simpa only [←hYeq] using hI
  · simpa only [←hYeq,globalSurfaceFirstPrimitive_zero] using hp

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
