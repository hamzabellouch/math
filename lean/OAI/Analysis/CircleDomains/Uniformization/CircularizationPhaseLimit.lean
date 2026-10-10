import OAI.Analysis.CircleDomains.Uniformization.CyclicCircularization
import OAI.Analysis.CircleDomains.Uniformization.OmittedLimits
import OAI.Analysis.CircleDomains.Uniformization.HurwitzZeroFreeProof
import OAI.Analysis.CircleDomains.Modulus.NormalizedLimitEquivalence
import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative

namespace OAI

/-! A phase of the actual cyclic construction has a conformal normal
limit which omits the entire limiting selected disk, including a
possible radius-zero disk. This does not yet identify the other holes. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity.FiniteJordanConfiguration

variable {I : Type*} [Finite I]

lemma planeRegion_nontrivial (C : FiniteJordanConfiguration I) : C.planeRegion.Nontrivial := by
  obtain ⟨R,hR,hsource⟩ := C.exists_exterior_radius
  have hmem (t : ℝ) (ht : R≤t) : (t : ℂ) ∈ C.planeRegion := by
    apply hsource
    simpa only [OnePoint.coe_injective.mem_set_image,mem_ball,dist_zero_right,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hR.le.trans ht),
      mem_compl_iff,not_lt] using ht
  refine ⟨(R : ℂ),hmem R le_rfl,((R+1 : ℝ) : ℂ),hmem (R+1) (by linarith),?_⟩
  intro he
  have := Complex.ofReal_injective he
  linarith

lemma not_constant_of_injOn (C : FiniteJordanConfiguration I) {F : ℂ → ℂ}
    (hi : InjOn F C.planeRegion) : ¬ ∃a, ∀z∈C.planeRegion,F z=a := by
  rintro ⟨a,ha⟩
  obtain ⟨x,hx,y,hy,hne⟩ := C.planeRegion_nontrivial
  exact hne (hi hx hy ((ha x hx).trans (ha y hy).symm))

omit [Finite I] in
lemma region_eq_plane_with_infty (C : FiniteJordanConfiguration I) :
    C.region=((↑) : ℂ → Sphere) '' C.planeRegion ∪ {∞} := by
  ext p
  cases p using OnePoint.rec <;> simp [planeRegion,C.infty_mem_region]

lemma conformal_limit (C : FiniteJordanConfiguration I) {F : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F C.planeRegion) (hi : InjOn F C.planeRegion)
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalEquivalence (extendAtInfinity F) C.region (extendAtInfinity F '' C.region) := by
  obtain ⟨R,hR,hsource⟩ := C.exists_exterior_radius
  rw [C.region_eq_plane_with_infty]
  apply normalized_limit_conformal_equivalence C.planeRegion_open hd hi
    (fun z hz => holomorphicInjOn_deriv_ne_zero C.planeRegion_open hd hi hz) hn
  intro z hz
  change R ≤ ‖z‖ at hz
  apply hsource
  simpa only [OnePoint.coe_injective.mem_set_image,mem_ball,dist_zero_right,
    mem_compl_iff,not_lt] using hz

lemma selected_disk_omitted (C : FiniteJordanConfiguration I) (schedule : ℕ → I)
    (n : ℕ) (z : ℂ) (hz : z ∈ C.planeRegion) :
    finiteCoord (cumulativeMap C schedule (n+1) (z : Sphere)) ∉
      closedBall (selectedCenter C schedule n) (selectedRadius C schedule n) := by
  have hf := cumulativeMap_conformal C schedule (n+1)
  have hfin := finite_image_of_fixes_infty hf.bijOn.injOn C.infty_mem_region
    (cumulativeMap_principal C schedule (n+1)).1 hz
  intro hdisk
  have hcap : cumulativeMap C schedule (n+1) (z : Sphere) ∈
      FiniteTransfer.closedTerminalCap ((iterate C schedule (n+1)).hole (schedule n)) := by
    rw [selected_cap_eq]
    exact ⟨_,hdisk,coe_finiteCoord hfin⟩
  exact hf.bijOn.mapsTo hz (mem_iUnion.mpr ⟨schedule n,hcap⟩)

lemma exists_cyclic_phase_limit {m : ℕ}
    (C : FiniteJordanConfiguration (Fin (m+1))) (i : Fin (m+1)) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ) (c : Fin (m+1) → ℂ) (r : Fin (m+1) → ℝ),
      StrictMono s ∧ (∀j,0≤r j) ∧
      (∀j,Tendsto (fun n => selectedCenter C (cyclicSchedule m) (visitTime (s n) j))
        atTop (𝓝 (c j))) ∧
      (∀j,Tendsto (fun n => selectedRadius C (cyclicSchedule m) (visitTime (s n) j))
        atTop (𝓝 (r j))) ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord
        (cumulativeMap C (cyclicSchedule m) (visitTime (s n) i+1) (z : Sphere)))
        F atTop C.planeRegion ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F) C.region (extendAtInfinity F '' C.region) ∧
      ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
        (extendAtInfinity F '' C.region)ᶜ := by
  obtain ⟨t,c,r,ht,hr,hc,hrlim,_⟩ := exists_cyclic_selected_disk_limits C
  obtain ⟨s,F,hs,hlim,hd,hi,hn⟩ := exists_circularization_normal_limit_along C
    (cyclicSchedule m) (fun n => visitTime (t n) i+1)
  refine ⟨t ∘ s,F,c,r,ht.comp hs,hr,fun j => (hc j).comp hs.tendsto_atTop,
    fun j => (hrlim j).comp hs.tendsto_atTop,hlim,
    isPrincipalNormalized_extendAtInfinity hn,C.conformal_limit hd hi hn,?_⟩
  rw [C.region_eq_plane_with_infty]
  apply sphere_disk_omitted_of_plane_disk
  apply omitted_closedBall_limit hurwitzZeroFreeLimit C.planeRegion_open C.planeRegion_connected
    (Filter.Eventually.of_forall (fun n => ?_))
    (fun n => (selectedRadius_pos C (cyclicSchedule m) (visitTime (t (s n)) i)).le)
    (hr i) hlim ((hc i).comp hs.tendsto_atTop) ((hrlim i).comp hs.tendsto_atTop)
    (C.not_constant_of_injOn hi)
  exact ⟨((cumulativeMap_conformal C (cyclicSchedule m) (visitTime (t (s n)) i+1)).1.finite_open_embedding
    C.region_open (cumulativeMap_conformal C (cyclicSchedule m)
      (visitTime (t (s n)) i+1)).bijOn.injOn C.infty_mem_region
    (cumulativeMap_principal C (cyclicSchedule m) (visitTime (t (s n)) i+1)).1).1,
    fun z hz => selected_disk_omitted C (cyclicSchedule m) (visitTime (t (s n)) i) z hz⟩

end CircleDomainRigidity.FiniteJordanConfiguration

end

end OAI
