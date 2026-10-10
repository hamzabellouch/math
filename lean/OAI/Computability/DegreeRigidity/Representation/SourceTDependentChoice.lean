import OAI.Computability.DegreeRigidity.SetModels.InternalFunctionOrbit
import OAI.Computability.DegreeRigidity.SetModels.InternalSerialSelection
import OAI.Computability.DegreeRigidity.Representation.SourceTWellFounded

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse InternalWellOrder
universe u

theorem sourceT_dependent_choice (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r x : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hx : x ∈ d)
    (hser : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ r) :
    ∃ a : ℕ → ZFSet.{u}, a 0 = x ∧ (∀ n, a n ∈ d) ∧ orbitGraph a ∈ M ∧
      ∀ n, ZFSet.pair (a (n+1)) (a n) ∈ r := by
  classical
  obtain ⟨F,hFM,hF,hrel⟩ := internal_serial_function M hM hT hd hr hser
  let next (y : ZFSet.{u}) : ZFSet.{u} := if hy : y ∈ d then (hF.2 y hy).choose else y
  have hn (y : ZFSet.{u}) (hy : y ∈ d) : next y ∈ d ∧ ZFSet.pair y (next y) ∈ F := by
    simp only [next,dite_eq_left hy]
    exact ⟨(hF.2 y hy).choose_spec.1,(hF.2 y hy).choose_spec.2.1⟩
  let a : ℕ → ZFSet.{u} := Nat.rec x (fun _ y => next y)
  have ha : ∀ n, a n ∈ d := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => exact (hn (a n) ih).1
  have hstep : ∀ n, ZFSet.pair (a n) (a (n+1)) ∈ F := fun n => (hn (a n) (ha n)).2
  exact ⟨a,rfl,ha,internal_orbitGraph M hM hT hd hFM hF a ha hstep,
    fun n => hrel _ _ (hstep n)⟩

theorem sourceT_internal_descent (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hon : On d r)
    (hw : ¬ WellFounded (Rel d r)) :
    ∃ a : ℕ → ZFSet.{u}, (∀ n, a n ∈ d) ∧ orbitGraph a ∈ M ∧
      ∀ n, ZFSet.pair (a (n+1)) (a n) ∈ r := by
  classical
  have hn : ¬ InternallyWellFounded M d r := fun h => hw (sourceT_wellFounded M hM hT hd hr hon h)
  change ¬ (∀ b ∈ M, b ⊆ d → (∃ x, x ∈ b) → ∃ x, MinimalIn r b x) at hn
  simp only [not_forall] at hn
  obtain ⟨b,hb,hbd,hne,hbad⟩ := hn
  obtain ⟨x,hx⟩ := hne
  have hser : ∀ x ∈ b, ∃ y ∈ b, ZFSet.pair y x ∈ r := by
    intro y hy
    by_contra hn
    exact hbad ⟨y,hy,fun z hz hzy => hn ⟨z,hz,hzy⟩⟩
  obtain ⟨a,_,ha,hAM,hstep⟩ := sourceT_dependent_choice M hM hT hb hr hx hser
  exact ⟨a,fun n => hbd (ha n),hAM,hstep⟩

theorem wellFounded_no_descent (d r : ZFSet.{u}) (hw : WellFounded (Rel d r))
    (a : ℕ → ZFSet.{u}) (ha : ∀ n, a n ∈ d)
    (hstep : ∀ n, ZFSet.pair (a (n+1)) (a n) ∈ r) : False := by
  have hno (x : ZFSet.{u}) : Acc (Rel d r) x → ∀ n, a n = x → False := by
    intro hx
    induction hx with
    | intro x _ ih =>
      intro n he
      exact ih (a (n+1)) ⟨ha (n+1),he ▸ hstep n⟩ (n+1) rfl
  exact hno (a 0) (hw.apply (a 0)) 0 rfl

theorem sourceT_descent_absolute (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hon : On d r) :
    (∃ a : ℕ → ZFSet.{u}, (∀ n, a n ∈ d) ∧ orbitGraph a ∈ M ∧
      ∀ n, ZFSet.pair (a (n+1)) (a n) ∈ r) ↔ ¬ WellFounded (Rel d r) := by
  constructor
  · rintro ⟨a,ha,_,hstep⟩ hw
    exact wellFounded_no_descent d r hw a ha hstep
  · exact sourceT_internal_descent M hM hT hd hr hon

end TuringRigidity.BoundedSetTheory

end OAI
