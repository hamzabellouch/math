import OAI.Geometry.Immersion.ClosedSurface.FreeCharts
import OAI.Geometry.Immersion.ClosedSurface.ChartModel

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

/-- Coordinate data for one supported free mode. The representative `model`
is a genuine smooth extension of the immersed map in these coordinates. -/
structure ManifoldFreeChart (F : M → Space) (S : Set M) where
  source : Set M
  target : Set SmallModes.Base
  coord : M → SmallModes.Base
  model : RField 4
  open_source : IsOpen source
  closed_support : IsClosed S
  support_source : S ⊆ source
  smooth_coord : ContMDiffOn planeModel 𝓘(ℝ, SmallModes.Base) ∞ coord source
  coord_target : MapsTo coord source target
  smooth_model : ContDiff ℝ ∞ model
  model_domain : RealModeDomain model target
  represents : EqOn (model ∘ coord) (spaceCoordinates ∘ F) source

namespace ManifoldFreeChart

variable {F : M → Space} {S : Set M}

/-- The oscillatory increment, written directly as an ambient four-space map. -/
def increment (c : ManifoldFreeChart F S) (ψ u : SmallModes.Base → ℝ)
    (δ τ : ℝ) (q : ℕ) : M → Space :=
  c.source.indicator (fun x => spaceCoordinates.symm
    (realOsc τ (modeApprox τ (fun y => complexify (c.model y))
      (freeSeed δ τ (phaseAmplitude ψ u) c.model) (fun _ => 0) q) (c.coord x)))

/-- The local finite free mode extends smoothly by zero on the manifold.
No regularity of its values outside the coordinate source is required. -/
theorem increment_smooth_support (c : ManifoldFreeChart F S)
    {ψ u : SmallModes.Base → ℝ}
    (hb : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) c.target)
    (hsp : ∀ x ∈ c.source, c.coord x ∈ tsupport ψ → x ∈ S)
    (δ τ : ℝ) (q : ℕ) :
    ContMDiff planeModel spaceModel ∞ (c.increment ψ u δ τ q) ∧
      tsupport (c.increment ψ u δ τ q) ⊆ S := by
  have hv := freeSeed_isFree c.smooth_model c.model_domain δ τ hb
  have hz := contDiffOn_modeApprox τ (c.model_domain.complexDomain c.smooth_model)
    hv.smooth (f := fun _ => 0) contDiffOn_const q
  have hr := contDiffOn_realOsc hz τ
  have hloc := spaceCoordinates.symm.contDiff.contMDiff.comp_contMDiffOn
    (hr.contMDiffOn.comp c.smooth_coord c.coord_target)
  apply contMDiff_indicator_of_support c.open_source c.closed_support c.support_source hloc
  intro x hx hxS
  have hxψ : c.coord x ∉ tsupport ψ := fun hp => hxS (hsp x hx hp)
  have hm : modeApprox τ (fun y => complexify (c.model y))
      (freeSeed δ τ (phaseAmplitude ψ u) c.model) (fun _ => 0) q (c.coord x) = 0 := by
    simpa only [chartFreeAmplitude, Function.comp_apply, id_eq] using
      chartFree_vanishes (U := Set.univ) (S := tsupport ψ) (χ := id)
        (fun _ _ hp => hp) δ τ c.model u q (c.coord x) (Set.mem_univ _) hxψ
  change spaceCoordinates.symm (realOsc τ (modeApprox τ
    (fun y => complexify (c.model y))
    (freeSeed δ τ (phaseAmplitude ψ u) c.model) (fun _ => 0) q) (c.coord x)) = 0
  simp only [realOsc, oscillate, hm, smul_zero]
  have hzreal : QuadraticMean.realPart (0 : Fin 4 → ℂ) = 0 := by ext i; rfl
  rw [hzreal, map_zero]

/-- On the source chart the global increment is the original finite mode. -/
theorem increment_eq_on_source (c : ManifoldFreeChart F S)
    (ψ u : SmallModes.Base → ℝ) (δ τ : ℝ) (q : ℕ)
    {x : M} (hx : x ∈ c.source) :
    spaceCoordinates (c.increment ψ u δ τ q x) =
      realOsc τ (modeApprox τ (fun y => complexify (c.model y))
        (freeSeed δ τ (phaseAmplitude ψ u) c.model) (fun _ => 0) q) (c.coord x) := by
  rw [increment, indicator_of_mem hx, spaceCoordinates.apply_symm_apply]

theorem increment_hasCompactSupport (c : ManifoldFreeChart F S)
    (hS : IsCompact S) {ψ u : SmallModes.Base → ℝ}
    (hb : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) c.target)
    (hsp : ∀ x ∈ c.source, c.coord x ∈ tsupport ψ → x ∈ S)
    (δ τ : ℝ) (q : ℕ) : HasCompactSupport (c.increment ψ u δ τ q) :=
  hS.of_isClosed_subset isClosed_closure (c.increment_smooth_support hb hsp δ τ q).2

end ManifoldFreeChart

/-- Finitely many coordinate free modes give one smooth ambient correction,
supported in the union of their prescribed supports. -/
theorem finite_free_increment_smooth_support {ι : Type*} [Fintype ι]
    {F : M → Space} {S : ι → Set M} (c : ∀ i, ManifoldFreeChart F (S i))
    (ψ u : ι → SmallModes.Base → ℝ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (phaseAmplitude (ψ i) (u i)) (c i).target)
    (hsp : ∀ i x, x ∈ (c i).source → (c i).coord x ∈ tsupport (ψ i) → x ∈ S i)
    (δ τ : ℝ) (q : ℕ) :
    ContMDiff planeModel spaceModel ∞ (fun x => ∑ i, (c i).increment (ψ i) (u i) δ τ q x) ∧
      tsupport (fun x => ∑ i, (c i).increment (ψ i) (u i) δ τ q x) ⊆ ⋃ i, S i := by
  classical
  have hloc (i) := (c i).increment_smooth_support (hb i) (hsp i) δ τ q
  refine ⟨ContMDiff.sum (fun i _ => (hloc i).1), ?_⟩
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i => (c i).closed_support))
  intro x hx
  by_contra hnot
  have hz (i : ι) : (c i).increment (ψ i) (u i) δ τ q x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hnot (mem_iUnion.mpr ⟨i, (hloc i).2 h⟩))
  exact hx (by simp only [hz, Finset.sum_const_zero])

end ClosedSurfaceR4

end

end OAI
