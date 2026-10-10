import Mathlib
import OAI.Combinatorics.UniformKServer.BoundedFilter
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

noncomputable section

/-! A literal labeled strongly-lazy simulation. Fixed-label mismatch suffices
for the movement telescope; no forbidden move or future request is used. -/
namespace UniformKServer.LazyFinance
open Finset
open scoped Classical
variable {X : Type*} [PseudoMetricSpace X] {k : ℕ}

def mismatch (a b : Fin k→X) : ℝ := ∑ i,dist (a i) (b i)

theorem mismatch_nonneg (a b : Fin k→X) : 0 ≤ mismatch a b := sum_nonneg fun _ _=>dist_nonneg

theorem mismatch_triangle (a b c : Fin k→X) : mismatch a c ≤ mismatch a b+mismatch b c := by
  unfold mismatch
  rw [←sum_add_distrib]
  exact sum_le_sum fun i _=>dist_triangle _ _ _

def choice (hk : 0 < k) (a v : Fin k→X) (r : X) : Fin k :=
  if h : ∃ i,a i=r then h.choose else if h : ∃ i,v i=r then h.choose else ⟨0,hk⟩

omit [PseudoMetricSpace X] in
theorem lazy (hk : 0 < k) (a v : Fin k→X) (r : X) (h : ∃ i,a i=r) :
    a (choice hk a v r)=r := by
  rw [choice,dite_eq_left h]
  exact h.choose_spec

theorem at_request (a v : Fin k→X) (r : X) (i : Fin k) (hi : v i=r) :
    dist (a i) r+mismatch (Function.update a i r) v=mismatch a v := by
  symm
  calc
    _ = ∑ j : Fin k,((if j=i then dist (a i) r else 0)+dist (Function.update a i r j) (v j)) := by
      apply sum_congr rfl
      intro j _
      by_cases hj : j=i
      · subst j; simp [hi]
      · simp [hj]
    _ = _ := by simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true,mismatch]

theorem step (hk : 0 < k) (a u v : Fin k→X) (r : X) (hv : ∃ i,v i=r) :
    dist (a (choice hk a v r)) r+mismatch (Function.update a (choice hk a v r) r) v ≤
      mismatch a u+mismatch u v := by
  by_cases ha : ∃ i,a i=r
  · have he := lazy hk a v r ha
    have hz : dist (a (choice hk a v r)) r=0 := by rw [he,dist_self]
    have hu : Function.update a (choice hk a v r) r=a := by
      conv_lhs => arg 3; rw [←he]
      exact Function.update_eq_self _ _
    rw [hz,zero_add,hu]
    exact mismatch_triangle a u v
  · have he : v (choice hk a v r)=r := by rw [choice,dite_eq_right ha,dite_eq_left hv]; exact hv.choose_spec
    rw [at_request a v r _ he]
    exact mismatch_triangle a u v

theorem initial_bound (a b : Fin k→X) (Δ : ℝ) (hdiam : ∀ x y : X,dist x y ≤ Δ) :
    mismatch a b ≤ k*Δ := by
  calc
    _  ≤  ∑ _ : Fin k,Δ := sum_le_sum fun i _=>hdiam _ _
    _ = _ := by simp

end UniformKServer.LazyFinance

end

end OAI
