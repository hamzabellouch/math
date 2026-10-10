import OAI.Probability.DilutedSpin.TerminalMarginal

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma uniform_cons_expect (N : ℕ) (F : (Fin (N+1) → Spin) → ℝ) :
    (uniform : FiniteLaw (Fin (N+1) → Spin)).expect F =
      (uniform : FiniteLaw (Fin N → Spin)).expect (fun σ =>
        (uniform : FiniteLaw Spin).expect (fun ε => F (Fin.cons ε σ))) := by
  rw [uniform_expect,uniform_expect]
  simp_rw [uniform_expect]
  rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Spin)).sum_comp F]
  simp only [Fintype.sum_prod_type,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,← Finset.sum_div,Fin.consEquiv,Equiv.coe_fn_mk]
  rw [Finset.sum_comm]
  push_cast
  rw [pow_succ]
  ring

lemma exp_logMean_one (P : FiniteLaw Spin) (F : Spin → ℝ) :
    Real.exp (P.logMean 1 F) = P.expect (fun ε => Real.exp (F ε)) := by
  rw [logMean,div_one,Real.exp_log (expMoment_pos P 1 F)]
  simp only [expMoment,one_mul]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
open scoped BigOperators
variable {Ω Λ I : Type} [Fintype Ω] [Fintype Λ] {A : I → Type} [∀ i,Fintype (A i)]
    {k L N : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] in
lemma mark_eq_pathMap (roots : Fin k → I) (j : Fin k) (n : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) n) :
    mark j n y = pathMap (fun a : Row (A := A) roots => a j) n (pathSnd n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (y.1.2 j,mark j n y.2) = (y.1.2 j,pathMap _ n (pathSnd n y.2))
    rw [ih]

noncomputable def terminalRoot (a : Ω) (P : FiniteLaw Ω)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (E : Ω → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ) : ℝ :=
  root (terminalTower a P L) Q m (fun y => E (terminalState L y)) roots
    (fun i y z => ψ i (terminalState L y) z)

lemma terminalRoot_eq_backward (a : Ω) (P : FiniteLaw Ω)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (E : Ω → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ) :
    terminalRoot a P Q m E roots ψ =
      backwardLog (L+1) (prod (L+1) (terminalTower a P L)
        (markPrior (L+1) (fun d => FiniteLaw.pi (fun j => Q (roots j) d)))) m
        (fun y => E (terminalState L (pathFst (L+1) y))+
          ∑ j,Real.log (ψ (roots j) (terminalState L (pathFst (L+1) y))
            (pathMap (fun a : Row (A := A) roots => a j) (L+1) (pathSnd (L+1) y)))) := by
  simp only [terminalRoot,root,tower_eq_prod]
  congr 1
  funext y
  simp only [HeterogeneousMarks.logWeight,physical_eq_fst,mark_eq_pathMap]

lemma terminalRoot_marginal (a : Ω) (b : Λ) (P : FiniteLaw Ω) (R : FiniteLaw Λ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : Ω → ℝ) (G : Λ → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ)
    (φ : (i : I) → Λ → FinitePath (A i) (L+1) → ℝ)
    (h : ∀ y : FinitePath (Row (A := A) roots) (L+1),
      P.expMoment 1 (fun s => E s+∑ j, Real.log (ψ (roots j) s
        (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))) =
      R.expMoment 1 (fun s => G s+∑ j, Real.log (φ (roots j) s
        (pathMap (fun a : Row (A := A) roots => a j) (L+1) y)))) :
    terminalRoot a P Q m E roots ψ = terminalRoot b R Q m G roots φ := by
  rw [terminalRoot_eq_backward,terminalRoot_eq_backward]
  let U : KernelTower (Row (A := A) roots) (L+1) :=
    markPrior (L+1) (fun d => FiniteLaw.pi (fun j => Q (roots j) d))
  let F : Ω → FinitePath (Row (A := A) roots) (L+1) → ℝ := fun s y =>
    E s+∑ j, Real.log (ψ (roots j) s (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))
  let G' : Λ → FinitePath (Row (A := A) roots) (L+1) → ℝ := fun s y =>
    G s+∑ j, Real.log (φ (roots j) s (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))
  exact terminal_marginal_congr L a b P R U m hm F G' h

/-- Exact new-spin marginalization at the final exponent1. -/
lemma terminalRoot_spin_marginal
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ) (G : (Fin (N+1) → Spin) → ℝ)
    (roots : Fin k → I) (ψ : (i : I) → (Fin N → Spin) → FinitePath (A i) (L+1) → ℝ) :
    terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform Q m
      (fun σ => E (fun i => σ i.succ)+G σ) roots (fun i σ a => ψ i (fun j => σ j.succ) a) =
    terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform Q m
      (fun σ => E σ+(FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun ε => G (Fin.cons ε σ))) roots ψ := by
  apply terminalRoot_marginal _ _ _ _ Q m hm
  intro a
  unfold FiniteLaw.expMoment
  simp only [one_mul]
  rw [FiniteLaw.uniform_cons_expect]
  apply FiniteLaw.expect_congr
  intro σ
  simp only [Fin.cons_succ]
  let c := ∑ j,Real.log (ψ (roots j) σ (pathMap (fun a : Row (A := A) roots => a j) (L+1) a))
  change (FiniteLaw.uniform : FiniteLaw Spin).expect (fun ε => Real.exp (E σ+G (Fin.cons ε σ)+c)) =
    Real.exp (E σ+(FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun ε => G (Fin.cons ε σ))+c)
  simp_rw [Real.exp_add]
  rw [FiniteLaw.expect_mul_right,FiniteLaw.expect_mul_left,FiniteLaw.exp_logMean_one]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
