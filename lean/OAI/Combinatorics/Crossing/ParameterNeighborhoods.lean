import OAI.Combinatorics.Crossing.FiniteSeparation
import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Tactic.FunProp

namespace OAI

namespace Zarankiewicz

def parameterNeighborhood (t : unitInterval) (δ : ℝ) : Set unitInterval :=
  {s | |s.val-t.val| < δ}

theorem parameterNeighborhood_open (t : unitInterval) (δ : ℝ) :
    IsOpen (parameterNeighborhood t δ) := by
  apply isOpen_lt _ continuous_const
  fun_prop

theorem parameterNeighborhood_between (t : unitInterval) (δ : ℝ)
    (u v w : unitInterval) (hu : u ∈ parameterNeighborhood t δ)
    (hv : v ∈ parameterNeighborhood t δ) (huw : u ≤ w) (hwv : w ≤ v) :
    w ∈ parameterNeighborhood t δ := by
  change |w.val-t.val| < δ
  change |u.val-t.val| < δ at hu
  change |v.val-t.val| < δ at hv
  rw [abs_lt] at hu hv ⊢
  have h₁ : u.val ≤ w.val := huw
  have h₂ : w.val ≤ v.val := hwv
  constructor <;> linarith

theorem parameterNeighborhood_ordered (a b : unitInterval) (δ : ℝ) (hδ : 0 < δ)
    (hab : a < b) (hd : Disjoint (parameterNeighborhood a δ) (parameterNeighborhood b δ))
    (u v : unitInterval) (hu : u ∈ parameterNeighborhood a δ)
    (hv : v ∈ parameterNeighborhood b δ) : u < v := by
  by_contra hn
  have hvu : v ≤ u := le_of_not_gt hn
  have ha : a ∈ parameterNeighborhood a δ := by simpa [parameterNeighborhood] using hδ
  have hb : b ∈ parameterNeighborhood b δ := by simpa [parameterNeighborhood] using hδ
  by_cases hva : v ≤ a
  · exact Set.disjoint_left.mp hd ha (parameterNeighborhood_between b δ v b a hv hb hva hab.le)
  · have hav : a ≤ v := (lt_of_not_ge hva).le
    exact Set.disjoint_left.mp hd (parameterNeighborhood_between a δ a u v ha hu hav hvu) hv

theorem finite_parameter_neighborhoods {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → unitInterval) (ht : Function.Injective t) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, t i ∈ parameterNeighborhood (t i) δ) ∧
      (∀ i j, i ≠ j → Disjoint (closure (parameterNeighborhood (t i) δ))
        (closure (parameterNeighborhood (t j) δ))) := by
  obtain ⟨ε,hε,hsep⟩ := finite_node_separation (fun i => (t i).val)
    (Subtype.val_injective.comp ht)
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hclosed (i : ι) : IsClosed {s : unitInterval | |s.val-(t i).val| ≤ δ} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hcl (i : ι) : closure (parameterNeighborhood (t i) δ) ⊆
      {s : unitInterval | |s.val-(t i).val| ≤ δ} :=
    closure_minimal (fun s hh => le_of_lt (show |s.val-(t i).val| < δ from hh)) (hclosed i)
  refine ⟨δ,hδ,fun i => by simpa [parameterNeighborhood] using hδ,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := hcl i hx
  have hy' := hcl j hy
  have hg := hsep i j hij
  have htri := abs_sub_le (t i).val x.val (t j).val
  rw [abs_sub_comm (t i).val x.val] at htri
  change |x.val-(t i).val| ≤ δ at hx'
  change |x.val-(t j).val| ≤ δ at hy'
  dsimp [δ] at hx' hy'
  linarith

end Zarankiewicz

end OAI
