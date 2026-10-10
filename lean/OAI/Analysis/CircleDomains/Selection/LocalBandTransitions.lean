import OAI.Analysis.CircleDomains.Selection.BandStability
import OAI.Analysis.CircleDomains.Sobolev.PeriodizedLevels

namespace OAI

/-! Integer changes of local sheet preserve the actual interval-band
level graph. Eventual equality is enough: values outside the patch do
not enter its boundary band. -/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

theorem clusterGraph_add_const_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {c : ℝ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + c) (t : ℝ) :
    (x, t + c) ∈ clusterGraph D g ↔ (x, t) ∈ clusterGraph D f := by
  simp only [mem_clusterGraph_iff_mapClusterPt]
  constructor
  · intro ht
    have h := (ht.congrFun heq).continuousAt_comp
      (continuousAt_id.sub_const c)
    simpa only [Function.comp_def, id_eq, add_sub_cancel_right] using h
  · intro ht
    have h := ht.continuousAt_comp (continuousAt_id.add_const c)
    exact h.congrFun heq.symm

theorem intervalBand_add_const_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {c : ℝ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + c) (t : ℝ) :
    (x, t + c) ∈ intervalFiberHull (clusterGraph D g) ↔
      (x, t) ∈ intervalFiberHull (clusterGraph D f) := by
  constructor
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, ht⟩ := mem_intervalFiberHull_iff.mp ht
    have ha' : (x, (a - c) + c) ∈ clusterGraph D g := by simpa using ha
    have hb' : (x, (b - c) + c) ∈ clusterGraph D g := by simpa using hb
    exact mem_intervalFiberHull_iff.mpr ⟨a - c, b - c, s,
      (clusterGraph_add_const_of_eventuallyEq heq _).mp ha',
      (clusterGraph_add_const_of_eventuallyEq heq _).mp hb', hs, by nlinarith [ht]⟩
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, ht⟩ := mem_intervalFiberHull_iff.mp ht
    exact mem_intervalFiberHull_iff.mpr ⟨a + c, b + c, s,
      (clusterGraph_add_const_of_eventuallyEq heq _).mpr ha,
      (clusterGraph_add_const_of_eventuallyEq heq _).mpr hb, hs, by nlinarith [ht]⟩

theorem circleBand_fiber_eq_of_eventually_add_int
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {k : ℤ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + (k : ℝ)) :
    {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph D g} =
      {θ | (x, θ) ∈ circleBandGraph D f} := by
  have hadd (a : ℝ) : ((a + (k : ℝ) : ℝ) : UnitAddCircle) = (a : UnitAddCircle) :=
    unitAddCircle_eq_iff_exists_int.mpr ⟨k, rfl⟩
  ext θ
  constructor
  · rintro ⟨⟨y, a⟩, ha, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    have ha' : (x, (a - (k : ℝ)) + (k : ℝ)) ∈ intervalFiberHull (clusterGraph D g) := by
      simpa using ha
    refine ⟨(x, a - (k : ℝ)), (intervalBand_add_const_of_eventuallyEq heq _).mp ha', ?_⟩
    change (x, ((a - (k : ℝ) : ℝ) : UnitAddCircle)) = (x, θ)
    have hc := hadd (a - (k : ℝ))
    have hs : ((a - (k : ℝ) : ℝ) : UnitAddCircle) = θ := by
      have hc' : (a : UnitAddCircle) = ((a - (k : ℝ) : ℝ) : UnitAddCircle) := by
        simpa only [sub_add_cancel] using hc
      exact hc'.symm.trans (congrArg Prod.snd he)
    exact congrArg (fun θ => (x, θ)) hs
  · rintro ⟨⟨y, a⟩, ha, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    refine ⟨(x, a + (k : ℝ)), (intervalBand_add_const_of_eventuallyEq heq _).mpr ha, ?_⟩
    change (x, ((a + (k : ℝ) : ℝ) : UnitAddCircle)) = (x, θ)
    exact Prod.ext rfl ((hadd a).trans (congrArg Prod.snd he))

end CircleDomainRigidity

end OAI
