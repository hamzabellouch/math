import OAI.Analysis.SphereIsometry.CompactApproximation
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Compact convex fixed points

Finite-net approximate fixed points force the minimum of the continuous
displacement function to be zero. Ambient completeness is not required.
-/

noncomputable section

namespace Tingley

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem exists_fixedPoint_of_isCompact_of_approximate
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {g : E → E} (hg : ContinuousOn g K)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ x ∈ K, ‖x - g x‖ < δ) :
    ∃ x ∈ K, g x = x := by
  have hd : ContinuousOn (fun x => ‖x - g x‖) K := (continuousOn_id.sub hg).norm
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hd
  have hzero : ‖z - g z‖ = 0 := by
    by_contra hnezero
    have hpos : 0 < ‖z - g z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnezero)
    obtain ⟨x, hx, hsmall⟩ := happrox ‖z - g z‖ hpos
    exact (not_lt_of_ge ((isMinOn_iff.mp hmin) x hx)) hsmall
  exact ⟨z, hz, (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm⟩

/-- The compact-convex fixed-point theorem, obtained from the explicit
finite-net coefficient map and the proved simplex theorem. -/
theorem exists_fixedPoint_of_isCompact_convex
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    {g : E → E} (hg : ContinuousOn g K) (hmap : MapsTo g K K) :
    ∃ x ∈ K, g x = x := by
  apply exists_fixedPoint_of_isCompact_of_approximate hK hne hg
  intro δ hδ
  exact exists_approximate_fixedPoint_of_isCompact_convex hK hne hconv hg hmap hδ

/-- An explicit ambient representative of a subtype self-map. Its values
outside the subtype are immaterial; only continuity on that subtype is used. -/
def extendSelfMap {K : Set E} (g : K → K) (x : E) : E := by
  classical
  exact if hx : x ∈ K then (g ⟨x, hx⟩ : E) else x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extendSelfMap_of_mem {K : Set E} (g : K → K) {x : E} (hx : x ∈ K) :
    extendSelfMap g x = (g ⟨x, hx⟩ : E) := by
  simp only [extendSelfMap, dite_eq_left hx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem extendSelfMap_coe {K : Set E} (g : K → K) (x : K) :
    extendSelfMap g (x : E) = (g x : E) :=
  extendSelfMap_of_mem g x.property

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extendSelfMap_mapsTo {K : Set E} (g : K → K) :
    MapsTo (extendSelfMap g) K K := by
  intro x hx
  rw [extendSelfMap_of_mem g hx]
  exact (g ⟨x, hx⟩).property

omit [NormedSpace ℝ E] in
theorem continuousOn_extendSelfMap {K : Set E} {g : K → K} (hg : Continuous g) :
    ContinuousOn (extendSelfMap g) K := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun x : K => (g x : E)) := continuous_subtype_val.comp hg
  exact h.congr (fun x => (extendSelfMap_coe g x).symm)

/-- Subtype formulation of the compact-convex fixed-point theorem. -/
theorem continuous_compactConvex_fixedPoint
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (g : K → K) (hg : Continuous g) : ∃ x, g x = x := by
  obtain ⟨x, hx, heq⟩ := exists_fixedPoint_of_isCompact_convex hK hne hconv
    (continuousOn_extendSelfMap hg) (extendSelfMap_mapsTo g)
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [extendSelfMap_of_mem g hx] at heq
  exact heq

end Tingley

end

end OAI
