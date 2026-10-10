import OAI.Analysis.CircleDomains.Probability.BandMeasure
import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import OAI.Analysis.CircleDomains.Uniformization.Conformal
import OAI.Analysis.CircleDomains.Selection.LocalBandTransitions

namespace OAI

/-! The period-coordinate level graph of Definition 2.3, assembled from
local real branches on the punctured mask. The singular point belongs to
every level. Integer changes of sheet give the compatibility used below;
the closedness proof only needs the resulting equality of projected bands. -/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

def periodBandGraph {ι : Type*} (D M : Set Sphere) (b : Sphere)
    (V : ι → Set Sphere) (f : ι → Sphere → ℝ) : Set (Sphere × UnitAddCircle) :=
  {p | p.1 ∈ M ∧ (p.1 = b ∨ ∃ i, p.1 ∈ V i ∧ p ∈ circleBandGraph D (f i))}

theorem periodBandGraph_on_patch {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    (hmiss : ∀ i, b ∉ V i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j))
    {i : ι} {x : Sphere} (hx : x ∈ V i) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔ x ∈ M ∧ (x, θ) ∈ circleBandGraph D (f i) := by
  constructor
  · rintro ⟨hxM, rfl | ⟨j, hxj, hj⟩⟩
    · exact (hmiss i hx).elim
    · exact ⟨hxM, (hcompat j i x hxj hx θ).mp hj⟩
  · rintro ⟨hxM, hi⟩
    exact ⟨hxM, Or.inr ⟨i, hx, hi⟩⟩

theorem isClosed_periodBandGraph {ι : Type*}
    (D M : Set Sphere) (hM : IsClosed M) (b : Sphere)
    (V : ι → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hmiss : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (bound : ι → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ bound i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j)) :
    IsClosed (periodBandGraph D M b V f) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  by_cases hxM : p.1 ∈ M
  · have hxb : p.1 ≠ b := fun heq => hp ⟨hxM, Or.inl heq⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
    have hc : IsClosed (Prod.fst ⁻¹' M ∩ circleBandGraph D (f i)) :=
      (hM.preimage continuous_fst).inter (isCompact_circleBandGraph (hbound i)).isClosed
    have hp' : p ∈ (Prod.fst ⁻¹' M ∩ circleBandGraph D (f i))ᶜ := by
      intro h
      exact hp ((periodBandGraph_on_patch D M b V f hmiss hcompat hi p.2).mpr h)
    apply mem_of_superset (((hV i).preimage continuous_fst).inter hc.isOpen_compl |>.mem_nhds ⟨hi, hp'⟩)
    intro q hq hqgraph
    exact hq.2 ((periodBandGraph_on_patch D M b V f hmiss hcompat hq.1 q.2).mp hqgraph)
  · apply mem_of_superset ((hM.isOpen_compl.preimage continuous_fst).mem_nhds hxM)
    intro q hq hqgraph
    exact hq hqgraph.1

theorem periodBandGraph_singular {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    (hb : b ∈ M) (θ : UnitAddCircle) : (b, θ) ∈ periodBandGraph D M b V f :=
  ⟨hb, Or.inl rfl⟩

theorem periodBandGraph_subset_mask {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    {x : Sphere} {θ : UnitAddCircle} (h : (x, θ) ∈ periodBandGraph D M b V f) :
    x ∈ M := h.1

theorem periodBandGraph_fiber_on_patch {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    (hmiss : ∀ i, b ∉ V i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j))
    {i : ι} {x : Sphere} (hxM : x ∈ M) (hx : x ∈ V i) :
    {θ | (x, θ) ∈ periodBandGraph D M b V f} =
      {θ | (x, θ) ∈ circleBandGraph D (f i)} := by
  ext θ
  change (x, θ) ∈ periodBandGraph D M b V f ↔ (x, θ) ∈ circleBandGraph D (f i)
  rw [periodBandGraph_on_patch D M b V f hmiss hcompat hx]
  exact and_iff_right hxM

theorem isClosed_periodBandGraph_of_integer_transitions {ι : Type*}
    [FirstCountableTopology Sphere]
    (D M : Set Sphere) (hM : IsClosed M) (b : Sphere)
    (V : ι → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hmiss : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (bound : ι → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ bound i)
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, f j =ᶠ[𝓝[D] x] fun y => f i y + (k : ℝ)) :
    IsClosed (periodBandGraph D M b V f) := by
  apply isClosed_periodBandGraph D M hM b V hV hmiss hcover f bound hbound
  intro i j x hxi hxj θ
  obtain ⟨k, hk⟩ := htrans i j x hxi hxj
  exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm

end CircleDomainRigidity

end OAI
