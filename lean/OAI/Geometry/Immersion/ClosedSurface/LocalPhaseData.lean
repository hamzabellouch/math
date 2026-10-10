import OAI.Geometry.Immersion.ClosedSurface.ImmersionJets

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]




theorem smooth_extension_near {F : M → V} {U : Set M} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ F U) {p : M} (hp : p ∈ U) :
    ∃ G : M → V, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ G ∧
      HasCompactSupport G ∧ tsupport G ⊆ U ∧ G =ᶠ[𝓝 p] F := by
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
    (hU.mem_nhds hp)
  let G : M → V := fun q => b q • F q
  have hs : tsupport G ⊆ tsupport b := tsupport_smul_subset_left _ _
  refine ⟨G, ?_, ?_, hs.trans hb, ?_⟩
  · apply contMDiff_of_tsupport
    intro q hq
    exact b.contMDiffAt.smul ((hF q (hb (hs hq))).contMDiffAt
      (hU.mem_nhds (hb (hs hq))))
  · exact b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport G) hs
  · filter_upwards [b.eventuallyEq_one] with q hq
    simp only [G, hq, Pi.one_apply, one_smul]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma coordDeriv_eventuallyEq {n : ℕ} {F G : RField n} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v : Base) : coordDeriv v F =ᶠ[𝓝 p] coordDeriv v G := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun A : Base →L[ℝ] RVec n => A v) hq

lemma realSecondForm_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v w : Base) :
    (fun q => realSecondForm F v w q) =ᶠ[𝓝 p] (fun q => realSecondForm G v w q) := by
  filter_upwards [coordDeriv_eventuallyEq h dx, coordDeriv_eventuallyEq h dy,
    coordDeriv_eventuallyEq (coordDeriv_eventuallyEq h w) v] with q hx hy hxy
  simp only [realSecondForm, hx, hy, hxy]

lemma realSecondTensor_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) : realSecondTensor F =ᶠ[𝓝 p] realSecondTensor G := by
  filter_upwards [realSecondForm_eventuallyEq h dx dx, realSecondForm_eventuallyEq h dx dy,
    realSecondForm_eventuallyEq h dy dy] with q hxx hxy hyy
  ext i
  fin_cases i <;> simp [realSecondTensor, hxx, hxy, hyy]




theorem actual_local_phase_data_on {F : RField 4} {O : Set Base}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {H : Base → PhaseMean.Tensor} {p : Base} (hp : p ∈ O) (hH : ContinuousAt H p)
    (hImm : Function.Injective (fderiv ℝ F p))
    (hB : ∃ v w : Base, realSecondForm F v w p ≠ 0)
    (hH0 : 0 < H p 0) (hHdet : 0 < H p 0 * H p 2 - (H p 1)^2) :
    ∃ (G : RField 4) (ξ : Fin 3 → Base)
      (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ) (U : Set Base),
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ O ∧ EqOn G F U ∧
      (∀ A, ∑ i, Q i A • covectorSquare (ξ i) = A) ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ F x) ∧
        (∀ i, 0 < Q i (H x)) ∧ (∀ i, Good (realSecondTensor F x) (ξ i)) ∧
        (∀ i j, i ≠ j → Good (realSecondTensor F x) (ξ i + ξ j) ∧
          Good (realSecondTensor F x) (ξ i - ξ j))) := by
  obtain ⟨G,hG,hGc,hGsp,he⟩ := smooth_extension_near hO hF.contMDiffOn hp
  have heir := he.fderiv_eq (𝕜 := ℝ)
  have hGi : Function.Injective (fderiv ℝ G p) := by rw [heir]; exact hImm
  have hGB : ∃ v w : Base, realSecondForm G v w p ≠ 0 := by
    obtain ⟨v,w,hvw⟩ := hB
    exact ⟨v,w,by rwa [(realSecondForm_eventuallyEq he v w).eq_of_nhds]⟩
  obtain ⟨ξ,Q,V,hV,hpV,hdec,hdata⟩ := actual_local_phase_data hG.contDiff hH hGi hGB hH0 hHdet
  have hnb : ∀ᶠ x in 𝓝 p, x ∈ O ∧ x ∈ V ∧ G x = F x ∧
      fderiv ℝ G x = fderiv ℝ F x ∧ realSecondTensor G x = realSecondTensor F x := by
    filter_upwards [hO.mem_nhds hp, hV.mem_nhds hpV, he, he.fderiv (𝕜 := ℝ),
      realSecondTensor_eventuallyEq he] with x hxO hxV hx hd hb
    exact ⟨hxO,hxV,hx,hd,hb⟩
  obtain ⟨U,hUs,hU,hpU⟩ := mem_nhds_iff.mp hnb
  refine ⟨G,ξ,Q,U,hG.contDiff,hGc,hU,hpU,fun x hx => (hUs hx).1,
    fun x hx => (hUs hx).2.2.1,hdec,?_⟩
  intro x hx
  obtain ⟨hxO,hxV,he,hd,hb⟩ := hUs hx
  have hh := hdata x hxV
  rwa [hd,hb] at hh

end ClosedSurfaceR4.RealModes

end

end OAI
