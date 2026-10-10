import Mathlib
import OAI.Geometry.BallPacking.Flows.AnnularInverseDomain

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
 theorem annular_normalForm_cover
    (D : AnnularHandleData E M)
    (b : ℝ) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (v : V) {q : Plane} (hq : q∈D.annularCoverDomain) (hx : D.handleAnnularCover q∈W) :
    Γ v (D.handleAnnularCover q)=γ (D.handleAnnularCover q)+
      (intervalClock (-b) b q.1*H v) • D.dual (D.handleAnnularCover q) := by
  simpa only [D.handleAnnularCover_inverse hq,cylinderCover] using hN v _ hx

 theorem globalSurfaceFirstPrimitive_cover_germ
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (ℓ : ℝ) {p : Plane × V} (hp : p.1∈D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1∈W) :
    (fun y => euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceFirstPrimitive D b Φ H Γ (ℓ,v)))
      (flatProductMap (D.handleAnnularCover)) (0,y)) =ᶠ[𝓝 p]
    (fun y => surfaceFirstPrimitive Φ (intervalClock (-b) b) H
      (D.annularCoverA γ) (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2)) (ℓ,y)) := by
  have hs := (D.annularCoverDomain_open).mem_nhds hp
  have hw := (D.handleAnnularCover_smoothAt hp).continuousAt.preimage_mem_nhds (hW.mem_nhds hx)
  filter_upwards [continuousAt_fst.preimage_mem_nhds hs,
    continuousAt_fst.preimage_mem_nhds hw] with y hy hyW
  exact globalSurfaceFirstPrimitive_cover D b Φ H Γ γ ℓ y hy
    (annular_normalForm_cover D b H Γ γ hN y.2 hy hyW)

 theorem globalSurfaceSecondPrimitive_cover_germ {ι : Type*} [Fintype ι]
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (τ : ℝ) {p : Plane × V} (hp : p.1∈D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1∈W) :
    (fun y => euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v)))
      (flatProductMap (D.handleAnnularCover)) (0,y)) =ᶠ[𝓝 p]
    (fun y => surfaceSecondPrimitive Φ (intervalClock (-b) b) K H h ρ ρ₀
      (D.annularCoverA γ) (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2)) (τ,y)) := by
  have hs := (D.annularCoverDomain_open).mem_nhds hp
  have hw := (D.handleAnnularCover_smoothAt hp).continuousAt.preimage_mem_nhds (hW.mem_nhds hx)
  filter_upwards [continuousAt_fst.preimage_mem_nhds hs,
    continuousAt_fst.preimage_mem_nhds hw] with y hy hyW
  exact globalSurfaceSecondPrimitive_cover D b Φ K H h ρ ρ₀ Γ γ τ y hy
    (annular_normalForm_cover D b H Γ γ hN y.2 hy hyW)

end
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

theorem globalSurfaceSecondEndpoint_cover_pullback
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x, x ∈ W → Γ v x = γ x +
      (intervalClock (-b) b (D.chart.symm x).1 * H v) • D.dual x)
    (hΓ : SmoothOneFormFamily (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (1,v)))
    {p : Plane × V} (hp : p.1 ∈ D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1 ∈ W) :
    (globalHorizontalCoupling Ω (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (1,v))
      (flatProductMap (D.handleAnnularCover) p)).bilinearComp
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) (flatProductMap (D.handleAnnularCover)) p)
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) (flatProductMap (D.handleAnnularCover)) p) =
      Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane V) (ContinuousLinearMap.snd ℝ Plane V) +
        euclideanExteriorOneForm (fun y => surfaceSecondPrimitive Φ (intervalClock (-b) b) K H h ρ ρ₀
          (D.annularCoverA γ) (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2)) (1,y)) p := by
  have hs := D.handleAnnularCover_smoothAt hp
  rw [flatProductMap_derivative hs,globalHorizontalCoupling_pullback hΓ hs]
  rw [euclideanExteriorOneForm_congr_germ
    (globalSurfaceSecondPrimitive_cover_germ D b Φ K H h ρ ρ₀ Γ γ hW hN 1 hp hx)]

theorem globalSurfaceSecondEndpoint_shear_cover
    (D : AnnularHandleData E M)
    (b : ℝ)
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ} {h : ι → V → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) (hh : ∀ i, ContDiff ℝ ∞ (h i))
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x, x ∈ W → Γ v x = γ x +
      (intervalClock (-b) b (D.chart.symm x).1 * H v) • D.dual x)
    (hΓ : SmoothOneFormFamily (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (1,v)))
    {U : Set Plane} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (D.annularCoverA γ) U)
    (hB : ContDiffOn ℝ ∞ (D.annularCoverB γ) U)
    {p : Plane × V} (hp : p.1 ∈ D.annularCoverDomain) (hpu : p.1 ∈ U)
    (hx : D.handleAnnularCover p.1 ∈ W) :
    (globalHorizontalCoupling Ω (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (1,v))
      (flatProductMap (D.handleAnnularCover) p)).bilinearComp
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) (flatProductMap (D.handleAnnularCover)) p)
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) (flatProductMap (D.handleAnnularCover)) p) =
    (horizontalCoupling Ω (baseCoefficient (D.annularCoverA γ))
      (weightedSecondCoefficient (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2))
        (surfaceFinalLayer (K-H) h (surfaceRemainder K H h (Φ.map 1).symm) ρ ρ₀))
      (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b) p)).bilinearComp
      (fderiv ℝ (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)) p)
      (fderiv ℝ (hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)) p) := by
  rw [globalSurfaceSecondEndpoint_cover_pullback D b Φ K H h ρ ρ₀ Γ γ hW hN hΓ hp hx]
  exact (surfaceSecondEndpoint_shear_pullback hΩ hskew Φ (intervalClock_smooth (-b) b)
    hK hH hh hρ hρ₀ hU hA hB (((D.clock_smooth.comp circleTurn_smooth).contDiff).comp contDiff_snd) p hpu).symm

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

theorem annularUnshearMap_pullback
    (D : AnnularHandleData Plane M)
    (b : ℝ)
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ} {h : ι → V → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) (hh : ∀ i, ContDiff ℝ ∞ (h i))
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (Γ : V → ManifoldOneForm Plane M) (γ : ManifoldOneForm Plane M) {W : Set M}
    (hW : IsOpen W)
    (hN : ∀ v x, x ∈ W → Γ v x = γ x +
      (intervalClock (-b) b (D.chart.symm x).1 * H v) • D.dual x)
    (hΓ : SmoothOneFormFamily (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (1,v)))
    {U : Set Plane} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (D.annularCoverA γ) U)
    (hB : ContDiffOn ℝ ∞ (D.annularCoverB γ) U)
    {p : Plane × V} (hp : p.1 ∈ D.annularCoverDomain) (hpu : p.1 ∈ U)
    (hx : D.handleAnnularCover p.1 ∈ W) (v u : Plane × V) :
    globalHorizontalCoupling Ω (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (1,v))
      (annularUnshearMap D b Φ p)
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) (annularUnshearMap D b Φ) p v)
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) (annularUnshearMap D b Φ) p u) =
    horizontalCoupling Ω (baseCoefficient (D.annularCoverA γ))
      (weightedSecondCoefficient (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2))
        (surfaceFinalLayer (K-H) h (surfaceRemainder K H h (Φ.map 1).symm) ρ ρ₀)) p v u := by
  let L := hamiltonianBaseShear Φ (intervalClock (-b) b) (intervalClock_smooth (-b) b)
  have hd : ContDiff ℝ ∞ L := hamiltonianBaseShear_smooth Φ (intervalClock_smooth (-b) b)
  have hi : ContDiff ℝ ∞ L.symm := hamiltonianBaseShear_inverse_smooth Φ (intervalClock_smooth (-b) b)
  have hχ : ContMDiffAt 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) ∞
      (flatProductMap (D.handleAnnularCover)) (L.symm p) :=
    flatProductMap_smoothAt (D.handleAnnularCover_smoothAt hp)
  have hder : mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) (annularUnshearMap D b Φ) p =
      (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane × V) (flatProductMap (D.handleAnnularCover)) (L.symm p)).comp
        (fderiv ℝ L.symm p) := by
    exact (mfderiv_comp p (hχ.mdifferentiableAt (by simp))
      (hi.contMDiff.mdifferentiableAt (by simp))).trans (by rw [mfderiv_eq_fderiv]; rfl)
  have ht := globalSurfaceSecondEndpoint_shear_cover D b hΩ hskew Φ hK hH hh hρ hρ₀
    Γ γ hW hN hΓ hU hA hB (p := L.symm p) hp hpu hx
  have hh' := congrArg (fun B : (Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ =>
    B (fderiv ℝ L.symm p v) (fderiv ℝ L.symm p u)) ht
  rw [hder]
  change _ = (horizontalCoupling Ω _ _ (L (L.symm p)))
    (fderiv ℝ L (L.symm p) (fderiv ℝ L.symm p v))
    (fderiv ℝ L (L.symm p) (fderiv ℝ L.symm p u)) at hh'
  rw [L.apply_symm_apply,smoothHomeomorph_inverse_derivative L hd hi,
    smoothHomeomorph_inverse_derivative L hd hi] at hh'
  exact hh'

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_joint_localized_manifold_moser_field
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {K U : Set (ℝ × M)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible) :
    ∃ V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
        (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)) ∧
      (∀ᶠ p in 𝓝ˢ K, V p = manifoldMoserField Ω α p) ∧
      (∀ p, α p.1 p.2=0 → V p=0) ∧
      (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → V (t,x)=0) ∧
      (∀ p (L : E →L[ℝ] ℝ), (p ∈ U → L (manifoldMoserField Ω α p)=0) → L (V p)=0) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : NormalSpace (ℝ × M) := inferInstance
  have hprod : IsManifold ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ (ℝ × M) := inferInstance
  let instProd : ChartedSpace (ℝ × E) (ℝ × M) := prodChartedSpace ℝ ℝ E M
  have : IsManifold 𝓘(ℝ,ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod,instProd] using hprod
  obtain ⟨χ,hχ,hχc,hχU,hχ1,_⟩ := exists_smooth_manifold_cutoff (E := ℝ × E) hK hU hKU
  have hχs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ χ := by
    simpa only [modelWithCornersSelf_prod,instProd] using hχ
  let V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2 := fun p => χ p • manifoldMoserField Ω α p
  have he (c : M) (q : ℝ × E) : timeChartField V c q =
      χ (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2) • timeChartField (manifoldMoserField Ω α) c q := by
    dsimp only [timeChartField,V]
    exact (chartDifferential c _).map_smul _ _
  refine ⟨V,?_,?_,?_,?_,?_⟩
  · apply timeField_smooth_of_coordinates
    intro p
    let c := p.2
    let q : ℝ × E := (p.1,extChartAt 𝓘(ℝ,E) c c)
    let F : ℝ × E → ℝ × M := fun z => (z.1,(extChartAt 𝓘(ℝ,E) c).symm z.2)
    have hq : q.2 ∈ (extChartAt 𝓘(ℝ,E) c).target := mem_extChartAt_target c
    have hFe : F q=p := by dsimp only [F,q,c]; rw [extChartAt_to_inv]
    have hi : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) c).symm q.2 :=
      (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hq)
    have hF : ContMDiffAt 𝓘(ℝ,ℝ × E) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ F q :=
      contDiffAt_fst.contMDiffAt.prodMk (hi.comp q contDiffAt_snd.contMDiffAt)
    have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 q :=
      (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hq⟩
    by_cases hp : p ∈ U
    · have hnU : ∀ᶠ z in 𝓝 q, F z ∈ U := hF.continuousAt.preimage_mem_nhds
        (by rw [hFe]; exact hU.mem_nhds hp)
      have hs := timeChartField_moser_contDiffAt hq ((hΩ c).contDiffAt hn)
        ((hα c).contDiffAt hn) (hnU.mono fun z hz => hinv (F z) hz)
      have hc : ContDiffAt ℝ ∞ (fun z => χ (F z)) q :=
        (hχs.contMDiffAt.comp q hF).contDiffAt
      exact (hc.smul hs).congr_of_eventuallyEq (Filter.Eventually.of_forall (he c))
    · have hp' : p ∉ tsupport χ := fun h => hp (hχU h)
      have hz : ∀ᶠ z in 𝓝 q, χ (F z)=0 := by
        have hh : F ⁻¹' (tsupport χ)ᶜ ∈ 𝓝 q := hF.continuousAt.preimage_mem_nhds
          (show (tsupport χ)ᶜ ∈ 𝓝 (F q) by
            rw [hFe]; exact (isClosed_tsupport χ).isOpen_compl.mem_nhds hp')
        filter_upwards [hh] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
      filter_upwards [hz] with z hz
      rw [he,hz,zero_smul]
  · filter_upwards [hχ1] with p hp
    change χ p • _ = _
    rw [hp,one_smul]
  · intro p hp
    change χ p • (-((Ω p.1 p.2).inverse (α p.1 p.2)))=0
    rw [hp,map_zero,neg_zero,smul_zero]
  · refine ⟨Prod.snd '' tsupport χ,hχc.image continuous_snd,?_⟩
    intro t x hx
    have hz : χ (t,x)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(t,x),h,rfl⟩)
    change χ (t,x) • _ = 0
    rw [hz,zero_smul]
  · intro p L hL
    change L (χ p • manifoldMoserField Ω α p)=0
    erw [map_smul]
    by_cases hp : p ∈ U
    · rw [hL hp,smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hχU h)),zero_smul]

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_contraction_derivative
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} {X : ℝ × E → E} {p : ℝ × E}
    (hΩ : DifferentiableAt ℝ Ω p) (hα : DifferentiableAt ℝ α p)
    (hX : DifferentiableAt ℝ X p)
    (hcon : (fun q => Ω q (X q)) =ᶠ[𝓝 p] (fun q => -α q))
    (q : ℝ × E) (w : E) :
    fderiv ℝ Ω p q (X p) w + Ω p (fderiv ℝ X p q) w = -(fderiv ℝ α p q w) := by
  have hl := hΩ.hasFDerivAt.clm_apply hX.hasFDerivAt
  have hr := hα.hasFDerivAt.neg.congr_of_eventuallyEq hcon
  have he := congrArg (fun A : (ℝ × E) →L[ℝ] E →L[ℝ] ℝ => A q w) (hl.unique hr)
  simpa only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    neg_apply,add_comm] using he

theorem local_moser_transport_equation
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} {X : ℝ × E → E} {p : ℝ × E}
    (hΩ : DifferentiableAt ℝ Ω p) (hα : DifferentiableAt ℝ α p)
    (hX : DifferentiableAt ℝ X p)
    (hcon : (fun q => Ω q (X q)) =ᶠ[𝓝 p] (fun q => -α q))
    (hskew : ∀ u v, Ω p u v = -Ω p v u)
    (hclosed : ∀ u v w, fderiv ℝ Ω p (0,u) v w - fderiv ℝ Ω p (0,v) u w +
      fderiv ℝ Ω p (0,w) u v = 0)
    (htime : ∀ v w, fderiv ℝ Ω p (1,0) v w =
      fderiv ℝ α p (0,v) w - fderiv ℝ α p (0,w) v) (v w : E) :
    fderiv ℝ Ω p (1,X p) v w +
      Ω p (fderiv ℝ X p (0,v)) w + Ω p v (fderiv ℝ X p (0,w)) = 0 := by
  have h1 := local_contraction_derivative hΩ hα hX hcon (0,v) w
  have h2 := local_contraction_derivative hΩ hα hX hcon (0,w) v
  have hc := hclosed (X p) v w
  have ht := htime v w
  rw [show (1,X p) = ((1,0) : ℝ × E)+(0,X p) by ext <;> simp,
    map_add,add_apply,add_apply,hskew v]
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem joint_manifold_moser_PDE
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {U : Set (ℝ × M)} (hU : IsOpen U) {t : ℝ} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (ht : (t,(extChartAt 𝓘(ℝ,E) c).symm y) ∈ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    (heq : ∀ᶠ p in 𝓝 (t,(extChartAt 𝓘(ℝ,E) c).symm y),
      V p = manifoldMoserField Ω α p)
    (hΩ : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y))
    (hα : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y))
    (hskew : ∀ u v, chartTwoForm (Ω t) c y u v = -chartTwoForm (Ω t) c y v u)
    (hclosed : ∀ u v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,w) u v = 0)
    (htime : ∀ v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,w) v)
    (v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y)
        (1,timeChartField V c (t,y)) v w +
      chartTwoForm (Ω t) c y (fderiv ℝ (timeChartField V c) (t,y) (0,v)) w +
      chartTwoForm (Ω t) c y v (fderiv ℝ (timeChartField V c) (t,y) (0,w)) = 0 := by
  have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (t,y) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,hy⟩
  have hX := ((timeChartField_contDiffOn hV c).contDiffAt hn).differentiableAt (by simp)
  apply local_moser_transport_equation (hΩ.differentiableAt (by simp))
    (hα.differentiableAt (by simp)) hX _ hskew hclosed htime
  let F : ℝ × E → ℝ × M := fun q => (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)
  have hCs : ContinuousAt (fun z : E => (extChartAt 𝓘(ℝ,E) c).symm z) y :=
    continuousAt_extChartAt_symm'' (I := 𝓘(ℝ,E)) hy
  have hS : ContinuousAt (fun q : ℝ × E => (extChartAt 𝓘(ℝ,E) c).symm q.2) (t,y) :=
    ContinuousAt.comp (f := fun q : ℝ × E => q.2)
      (g := fun z : E => (extChartAt 𝓘(ℝ,E) c).symm z) (x := (t,y)) hCs continuousAt_snd
  have hF : ContinuousAt F (t,y) := continuousAt_fst.prodMk hS
  have hspaceU : ∀ᶠ q in 𝓝 (t,y), F q ∈ U :=
    hF.preimage_mem_nhds (hU.mem_nhds ht)
  have hVe : ∀ᶠ q in 𝓝 (t,y), V (F q)=manifoldMoserField Ω α (F q) :=
    hF.preimage_mem_nhds heq
  have htarg : ∀ᶠ q : ℝ × E in 𝓝 (t,y), q.2 ∈ (extChartAt 𝓘(ℝ,E) c).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  filter_upwards [hspaceU,htarg,hVe] with q hq hqt hqe
  have hVC : timeChartField V c q = timeChartField (manifoldMoserField Ω α) c q := by
    dsimp only [timeChartField]
    rw [show V (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)=
      manifoldMoserField Ω α (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2) from hqe]
  rw [hVC]
  exact chart_moser_contraction hqt (hinv (F q) hq)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smoothAt_fderiv_apply_const {D G : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : D → G}
    {p : D} (hf : ContDiffAt ℝ ∞ f p) (v w : D) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w = fderiv ℝ (fderiv ℝ f) p w v := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ f) p := hf.fderiv_right (by simp)
  have hh := (hfd.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)
  rw [hh.fderiv]
  simp

theorem local_spatial_fderiv {F : ℝ × E → E} {p : ℝ × E}
    (hF : DifferentiableAt ℝ F p) (v : E) :
    fderiv ℝ (fun y => F (p.1,y)) p.2 v = fderiv ℝ F p (0,v) := by
  have hd := hF.hasFDerivAt.comp p.2
    ((hasFDerivAt_const (c := p.1) p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
  exact congrArg (fun A : E →L[ℝ] E => A v) hd.fderiv

theorem local_time_fderiv {F X : ℝ × E → E} {p : ℝ × E}
    (hF : DifferentiableAt ℝ F p)
    (hflow : HasDerivAt (fun s => F (s,p.2)) (X (p.1,F p)) p.1) :
    fderiv ℝ F p (1,0) = X (p.1,F p) := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.unique hflow

theorem local_flow_variation {F X : ℝ × E → E} {p : ℝ × E}
    (hF : ContDiffAt ℝ ∞ F p) (hX : DifferentiableAt ℝ X (p.1,F p))
    (hflow : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => F (s,q.2)) (X (q.1,F q)) q.1)
    (v : E) :
    HasDerivAt (fun s => fderiv ℝ F (s,p.2) (0,v))
      (fderiv ℝ X (p.1,F p) (0,fderiv ℝ F p (0,v))) p.1 := by
  have hFd : ContDiffAt ℝ ∞ (fderiv ℝ F) p := hF.fderiv_right (by simp)
  have hV : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (0,v)) p :=
    hFd.clm_apply contDiffAt_const
  have hd := (hV.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have he : (fun q => fderiv ℝ F q (1,0)) =ᶠ[𝓝 p] (fun q => X (q.1,F q)) := by
    have hF1 : ContDiffAt ℝ 1 F p := hF.of_le (by simp)
    filter_upwards [hF1.eventually (by simp),hflow] with q hq hqf
    exact local_time_fderiv (hq.differentiableAt (by simp)) hqf
  have hchain := hX.hasFDerivAt.comp p
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
      (hF.differentiableAt (by simp)).hasFDerivAt)
  have hc := congrArg (fun A : (ℝ × E) →L[ℝ] E => A (0,v)) hchain.fderiv
  have he' := congrArg (fun A : (ℝ × E) →L[ℝ] E => A (0,v)) he.fderiv_eq
  change fderiv ℝ (fun q => X (q.1,F q)) p (0,v) = _ at hc
  rw [smoothAt_fderiv_apply_const hF,hc] at he'
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply] at he'
  have hs := hF.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  apply hd.congr_deriv
  rw [smoothAt_fderiv_apply_const hF,hs.eq (1,0) (0,v)]
  exact he'

theorem local_flow_form_derivative {F X : ℝ × E → E} {p : ℝ × E}
    (hF : ContDiffAt ℝ ∞ F p) (hX : DifferentiableAt ℝ X (p.1,F p))
    (hflow : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => F (s,q.2)) (X (q.1,F q)) q.1)
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : DifferentiableAt ℝ Ω (p.1,F p))
    (hPDE : ∀ u z, fderiv ℝ Ω (p.1,F p) (1,X (p.1,F p)) u z +
      Ω (p.1,F p) (fderiv ℝ X (p.1,F p) (0,u)) z +
      Ω (p.1,F p) u (fderiv ℝ X (p.1,F p) (0,z)) = 0) (v w : E) :
    HasDerivAt (fun s => Ω (s,F (s,p.2))
      (fderiv ℝ (fun y => F (s,y)) p.2 v) (fderiv ℝ (fun y => F (s,y)) p.2 w)) 0 p.1 := by
  have hpos : HasDerivAt (fun s => (s,F (s,p.2))) (1,X (p.1,F p)) p.1 := by
    simpa only [id_eq,Prod.eta] using
      (hasDerivAt_id p.1).prodMk hflow.self_of_nhds
  have hdΩ := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := ℝ × E) (l := Ω)
    p.1 hΩ.hasFDerivAt hpos (by simp only [Prod.eta])
  have hd := (hdΩ.clm_apply (local_flow_variation hF hX hflow v)).clm_apply
    (local_flow_variation hF hX hflow w)
  have hz : HasDerivAt (fun s => Ω (s,F (s,p.2))
      (fderiv ℝ F (s,p.2) (0,v)) (fderiv ℝ F (s,p.2) (0,w))) 0 p.1 := by
    apply hd.congr_deriv
    simpa only [add_apply,Function.comp_apply,id_eq] using hPDE
      (fderiv ℝ F p (0,v)) (fderiv ℝ F p (0,w))
  apply hz.congr_of_eventuallyEq
  have hF1 : ContDiffAt ℝ 1 F p := hF.of_le (by simp)
  have hev := (hF1.eventually (by simp)).filter_mono
    (continuousAt_id.prodMk continuousAt_const).tendsto
  filter_upwards [hev] with s hs
  change ContDiffAt ℝ 1 F (s,p.2) at hs
  rw [local_spatial_fderiv (hs.differentiableAt (by simp)),
    local_spatial_fderiv (hs.differentiableAt (by simp))]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
