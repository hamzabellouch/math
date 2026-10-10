import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # Exact independent-word law of a finite adaptive-history experiment -/

namespace ContingencyTables.FiniteUniformHistory

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {X : Type*} [Fintype X] [Nonempty X]

def kernel (_ : List X) (_ : X) : ℝ := 1/Fintype.card X

lemma kernel_nonneg (h : List X) (x : X) : 0 ≤ kernel h x := by
  unfold kernel
  positivity

lemma kernel_mass (h : List X) : ∑ x,kernel h x=1 := by
  have hx : (Fintype.card X:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [kernel,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [hx]

lemma expectation (N : ℕ) (h : List X) (f : List X → ℝ) :
    FiniteExperiment.expect kernel N h f=
      uniformAverage (fun xs : Fin N → X => f (h++List.ofFn xs)) := by
  induction N generalizing h with
  | zero => simp only [FiniteExperiment.expect,List.ofFn_zero,List.append_nil,uniformAverage_const]
  | succ N ih =>
    simp only [FiniteExperiment.expect,ih]
    rw [uniformAverage_fin_succ]
    have he : (fun x : X => uniformAverage
        (fun xs : Fin N → X => f ((h++[x])++List.ofFn xs)))=
        (fun x : X => uniformAverage
          (fun xs : Fin N → X => f (h++List.ofFn (Fin.cons x xs)))) := by
      funext x
      congr 1
      funext xs
      simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,List.append_assoc,List.singleton_append]
    rw [←he]
    let g : X → ℝ := fun x => uniformAverage
      (fun xs : Fin N → X => f ((h++[x])++List.ofFn xs))
    change (∑ x,kernel h x*g x)=uniformAverage g
    unfold kernel uniformAverage
    rw [←Finset.mul_sum]
    ring

/-- A history-dependent success predicate is evaluated on genuinely
independent finite words; only its conditional one-step loss is assumed. -/
theorem good_probability (Good : List X → Prop) (N : ℕ) (e : ℝ) (he : 0 ≤ e)
    (hstep : ∀ h,Good h → h.length<N →
      1-e ≤ uniformAverage (fun x : X => if Good (h++[x]) then (1:ℝ) else 0))
    (hzero : Good []) :
    1-(N:ℝ)*e ≤ uniformAverage (fun xs : Fin N → X =>
      if Good (List.ofFn xs) then (1:ℝ) else 0) := by
  have hs (h : List X) (hh : Good h) (hlen : h.length<N) :
      1-e ≤ ∑ x,FiniteExperiment.restrict kernel Good h x := by
    have hprob := hstep h hh hlen
    unfold FiniteExperiment.restrict kernel
    have heq (x : X) :
        (if Good (h ++ [x]) then (1:ℝ)/Fintype.card X else 0)=
          (if Good (h ++ [x]) then (1:ℝ) else 0)/Fintype.card X := by
      split_ifs <;> simp
    simp_rw [heq]
    rw [←Finset.sum_div]
    exact hprob
  have hp := FiniteExperiment.good_probability_bounded kernel Good kernel_nonneg
    (fun h => (kernel_mass h).le) N e he hs hzero
  rw [expectation] at hp
  simpa only [List.nil_append] using hp

end
end ContingencyTables.FiniteUniformHistory

end OAI
