import OAI.NumberTheory.Ostmann.Characters.BinaryPriorExposure

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.BinaryPriorExposure
open Construction BinaryHaar

def AllLeaves {α:Type*} (P:List Bool→α→Prop) :
    (j:ℕ)→List Bool→Leaves α j→Prop
  | 0,p,x => P p x
  | j+1,p,x => AllLeaves P j (false::p) x.1 ∧ AllLeaves P j (true::p) x.2

theorem allLeaves_mono {α:Type*} (P Q:List Bool→α→Prop)
    (hPQ:∀p x,P p x→Q p x) (j:ℕ) (p:List Bool) (x:Leaves α j)
    (hx:AllLeaves P j p x) : AllLeaves Q j p x := by
  induction j generalizing p with
  | zero => exact hPQ p x hx
  | succ j ih => exact ⟨ih _ _ hx.1,ih _ _ hx.2⟩

theorem mean_mono_on_support {α:Type*} [Fintype α]
    (μ:List Bool→FinitePrior α) (P:List Bool→α→Prop)
    (hμ:∀p x,¬P p x→(μ p).mass x=0)
    (j:ℕ) (p:List Bool) (F G:Leaves α j→ℝ)
    (hFG:∀x,AllLeaves P j p x→F x≤G x) :
    mean μ j p F ≤ mean μ j p G := by
  induction j generalizing p with
  | zero =>
    apply Finset.sum_le_sum
    intro x hx
    by_cases hp:P p x
    · exact mul_le_mul_of_nonneg_left (hFG x hp) ((μ p).mass_nonneg x)
    · simp only [hμ p x hp,zero_mul,le_refl]
  | succ j ih =>
    apply ih
    intro x hx
    exact ih _ _ _ (fun y hy=>hFG (x,y) ⟨hx,hy⟩)

theorem allLeaves_map {α β:Type*} (f:List Bool→α→β) (P:List Bool→β→Prop)
    (j:ℕ) (p:List Bool) (x:Leaves α j) :
    AllLeaves P j p (map f j p x) ↔ AllLeaves (fun p x=>P p (f p x)) j p x := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih => simp only [AllLeaves,map,ih]

end Ostmann.Characters.BinaryPriorExposure

end

end OAI
