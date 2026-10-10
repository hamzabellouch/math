import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem exists_box_avoiding_polynomials {σ κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial σ ℝ) (hP : ∀ k, P k ≠ 0)
    (lo hi : σ → ℝ) (hinterval : ∀ i, lo i < hi i) :
    ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ ∀ k, MvPolynomial.eval x (P k) ≠ 0 := by
  classical
  let Q := ∏ k, P k
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hP k)
  have hex : ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ MvPolynomial.eval x Q ≠ 0 := by
    by_contra hh
    apply hQ
    apply MvPolynomial.funext_set (fun i => Set.Ioo (lo i) (hi i)) (fun i => Set.Ioo_infinite (hinterval i))
    intro x hx
    rw [map_zero]
    by_contra hz
    exact hh ⟨x,fun i => hx i (Set.mem_univ i),hz⟩
  obtain ⟨x,hx,hval⟩ := hex
  refine ⟨x,hx,?_⟩
  have he : (∏ k, MvPolynomial.eval x (P k)) ≠ 0 := by simpa only [Q,map_prod] using hval
  exact fun k => (Finset.prod_ne_zero_iff.mp he) k (Finset.mem_univ k)

end Zarankiewicz

end

end OAI
