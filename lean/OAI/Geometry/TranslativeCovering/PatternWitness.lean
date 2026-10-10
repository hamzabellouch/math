import OAI.Geometry.TranslativeCovering.TargetGeometry

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace PatternWitness
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set Metric MeasureTheory SphericalLaw PatternGeometry ResidualCaps PoissonDiagrams CapCost
open scoped BigOperators Classical

structure Certificate {n : ℕ} {J : Type u_1} [Fintype J] (e : Sphere n)
    (p : J → Space n) (y : Space n) (a K A C : ℝ) where
  P : Finpartition (Finset.univ : Finset (relevant p (RadialShell.high a n) y))
  nonempty : P.parts.Nonempty
  card_le : P.parts.card ≤ n^2
  anchor : P.parts → relevant p (RadialShell.high a n) y
  slot : P.parts → Set (Sphere n)
  measurable_slot : ∀ S,MeasurableSet (slot S)
  subset_cap : ∀ S,slot S ⊆ cap (y-p (anchor S)) (1+3*RadialShell.η n)
  thinned : ∀ S,Real.exp (-K*Real.log n)*min
    ((intensity e (1/a)).real (cap (y-p (anchor S)) (1+3*RadialShell.η n))) (1/2) ≤
      (intensity e (1/a)).real (slot S)
  positive : ∀ S,0 < (intensity e (1/a)).real (slot S)
  lower : Real.exp (-A*C) ≤ ∏ S,(intensity e (1/a)).real (slot S)
  upper : (∏ S,(intensity e (1/a)).real (slot S)) ≤ 1
  self : diagram (intensity e (1/a)) slot slot ≤
    (∏ S,(intensity e (1/a)).real (slot S))^2*Real.exp (2*A*C)
  hole : ∀ U : PoissonConfig.Config (Sphere n),0 < PoissonConfig.witnessCount slot U →
    ∀ j,y-p j ∉ RandomBody.body (RadialShell.high a n) (1+3*RadialShell.η n) U

theorem construct {a l u₀ u : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) :
    ∃ K A : ℝ,0 < K ∧ 0 < A ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (J : Type u_2) [Fintype J] (e : Sphere n) (p : J → Space n) (y : Space n) (D C : ℝ),
    0 < RadialShell.low a n →
    y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    (relevant p (RadialShell.high a n) y).Nonempty →
    (relevant p (RadialShell.high a n) y).card ≤ n^2 →
    Nonempty (Certificate e p y a K A C) := by
  obtain ⟨K,A,hK,hA,n₀,hn₀⟩ := WitnessConstruction.shell ha hl hlt hu₀ hu hu1 (by norm_num : (0:ℝ)<2)
  refine ⟨K,A,hK,hA,n₀,?_⟩
  intro n hn _ _ J _ e p y D C hlo hy hne hcard
  let I := relevant p (RadialShell.high a n) y
  let : Nonempty I := hne.to_subtype
  have hrad (i : I) : RadialShell.low a n ≤ ‖y-p i‖ ∧ ‖y-p i‖ ≤ RadialShell.high a n :=
    (budgets p hy).1 i
  have hx (i : I) : y-p i ≠ 0 := norm_pos_iff.mp (hlo.trans_le (hrad i).1)
  let axes : I → Sphere n := fun i => unit (y-p i) (hx i)
  have hbudget : (Fintype.card I:ℝ)+(∑ i : I,RadialCost.weight n a ‖y-p i‖) ≤ 2*C := by
    exact (budgets p hy).2
  obtain ⟨P,b,E,hE,hloν,hhiν,hself⟩ := hn₀ n hn I (by simpa [I] using hcard) e axes
    (fun i => ‖y-p i‖) C (fun i => (hrad i).1) (fun i => (hrad i).2) hbudget
  have hc (i : I) : cap (axes i).val ((1+3*RadialShell.η n)/‖y-p i‖) =
      cap (y-p i) (1+3*RadialShell.η n) := cap_unit _ _ _
  let anchor : P.parts → I := fun S => b S.val
  let slot : P.parts → Set (Sphere n) := fun S => E S.val
  have hcommon : ∀ S ∈ P.parts,E S ⊆ ⋂ i ∈ S,cap (y-p i) (1+3*RadialShell.η n) := by
    intro S hS
    simpa only [BlockSets.common,hc] using (hE S hS).2.2.1
  refine ⟨{
    P := P
    nonempty := P.parts_nonempty (by simpa using (Finset.univ_nonempty : (Finset.univ : Finset I).Nonempty).ne_empty)
    card_le := P.card_parts_le_card.trans (by simpa [I] using hcard)
    anchor := anchor
    slot := slot
    measurable_slot := fun S => (hE S S.property).2.1
    subset_cap := fun S => by simpa only [hc] using (hE S S.property).2.2.2.1
    thinned := fun S => by simpa only [BlockSets.clipped,hc] using (hE S S.property).2.2.2.2.1
    positive := fun S => (hE S S.property).2.2.2.2.2.1
    lower := hloν
    upper := hhiν
    self := hself
    hole := fun U hU => witness_hole p y _ _ P E hcommon U hU
  }⟩

lemma separated {n : ℕ} {J : Type u_3} [Fintype J] (p : J → Space n)
    {x y : Space n} {L t r : ℝ} (hr : 0 < r)
    (hx : ∀ j,r ≤ ‖x-p j‖) (hy : ∀ j,r ≤ ‖y-p j‖)
    (hsep : (x,y) ∉ TargetGeometry.bad p L t)
    (i : relevant p L x) (j : relevant p L y) :
    t < ProjectiveCaps.angle (x-p i) (y-p j) := by
  by_contra h
  apply hsep
  apply mem_iUnion.mpr ⟨i.val,?_⟩
  apply mem_iUnion.mpr ⟨j.val,?_⟩
  exact ⟨norm_pos_iff.mp (hr.trans_le (hx i)),(Finset.mem_filter.mp i.property).2,
    norm_pos_iff.mp (hr.trans_le (hy j)),(Finset.mem_filter.mp j.property).2,le_of_not_gt h⟩
end PatternWitness

end OAI
