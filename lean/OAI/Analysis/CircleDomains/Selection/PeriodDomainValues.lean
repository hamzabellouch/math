import OAI.Analysis.CircleDomains.Selection.PeriodBandGraph

namespace OAI

/-! On the physical domain, the assembled period bands are the actual
circle-valued coordinate. Only continuity in the local patch is needed. -/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem circleBandGraph_of_continuousAt
    {X : Type*} [TopologicalSpace X] {D : Set X} {f : X → ℝ}
    {x : X} (hf : ContinuousAt f x) (hx : x ∈ D) (θ : UnitAddCircle) :
    (x, θ) ∈ circleBandGraph D f ↔ (f x : UnitAddCircle) = θ := by
  have hband (t : ℝ) : (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = f x := by
    constructor
    · intro ht
      obtain ⟨a, b, s, ha, hb, _, heq⟩ := mem_intervalFiberHull_iff.mp ht
      rw [clusterGraph_fiber_eq_of_continuousAt hf ha,
        clusterGraph_fiber_eq_of_continuousAt hf hb] at heq
      nlinarith [heq]
    · rintro rfl
      exact subset_intervalFiberHull _ (subset_closure ⟨x, hx, rfl⟩)
  constructor
  · rintro ⟨⟨y, t⟩, ht, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    simpa only [(hband t).mp ht] using congrArg Prod.snd he
  · intro he
    exact ⟨(x, f x), (hband (f x)).mpr rfl, Prod.ext rfl he⟩

theorem periodBandGraph_on_domain {ι : Type*}
    {D : Set Sphere} (hD : IsOpen D) (M : Set Sphere) (b : Sphere) (hb : b ∉ D)
    (V : ι → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (hf : ∀ i, ContinuousOn (f i) (D ∩ V i))
    (w : Sphere → UnitAddCircle)
    (hw : ∀ i x, x ∈ D ∩ V i → (f i x : UnitAddCircle) = w x)
    {x : Sphere} (hx : x ∈ D) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔ x ∈ M ∧ w x = θ := by
  have hxb : x ≠ b := fun he => hb (he ▸ hx)
  have hlocal (i : ι) (hi : x ∈ V i) :
      (x, θ) ∈ circleBandGraph D (f i) ↔ w x = θ := by
    rw [circleBandGraph_of_continuousAt
      ((hf i).continuousAt ((hD.inter (hV i)).mem_nhds ⟨hx, hi⟩)) hx,
      hw i x ⟨hx, hi⟩]
  constructor
  · rintro ⟨hxM, heq | ⟨i, hi, hband⟩⟩
    · exact (hxb heq).elim
    · exact ⟨hxM, (hlocal i hi).mp hband⟩
  · rintro ⟨hxM, hθ⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
    exact ⟨hxM, Or.inr ⟨i, hi, (hlocal i hi).mpr hθ⟩⟩

end CircleDomainRigidity

end OAI
