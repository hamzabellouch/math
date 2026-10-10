import Mathlib

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Boundary

def balancedPermutation {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) : Equiv.Perm E :=
  Equiv.ofFiberEquiv (fun v => Fintype.equivOfCardEq (hb v))

lemma balancedPermutation_tail {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) (e : E) :
    tail (balancedPermutation tail head hb e)=head e :=
  Equiv.ofFiberEquiv_map _ e

theorem exists_closed_trail {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) (e₀ : E) :
    ∃ n : ℕ, 0<n ∧ ∃ e : ℕ → E, e 0=e₀ ∧ e n=e₀ ∧
      (∀ i, head (e i)=tail (e (i+1))) ∧ Set.InjOn e (Set.Iio n) := by
  let p := balancedPermutation tail head hb
  let n := Function.minimalPeriod p e₀
  have hn : 0<n := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts e₀)
  refine ⟨n,hn,(fun i => p^[i] e₀),rfl,?_,?_,Function.iterate_injOn_Iio_minimalPeriod⟩
  · exact Function.isPeriodicPt_minimalPeriod p e₀
  · intro i
    dsimp only
    rw [Function.iterate_succ_apply']
    exact (balancedPermutation_tail tail head hb _).symm

end CriticalPercolation.Boundary
end
end
end

end OAI
