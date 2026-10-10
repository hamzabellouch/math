import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreHilbert

namespace OAI

/-! # Iterating the Laguerre differential operator on the actual slow jet -/

open Filter Topology Asymptotics Polynomial

namespace DefocusingNLS

noncomputable def laguerreJetOperator (d : ℕ → ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  -((t : ℂ) * d (n + 2) t + ((n + 1 : ℂ) - t) * d (n + 1) t - (n : ℂ) * d n t)

theorem hasDerivAt_laguerreJetOperator (d : ℕ → ℝ → ℂ)
    (hd : ∀ n t, HasDerivAt (d n) (d (n + 1) t) t) (n : ℕ) (t : ℝ) :
    HasDerivAt (laguerreJetOperator d n) (laguerreJetOperator d (n + 1) t) t := by
  have ht : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := (hasDerivAt_id (t : ℂ)).comp_ofReal
  have h := (((ht.mul (hd (n + 2) t)).add
    (((hasDerivAt_const t (n + 1 : ℂ)).sub ht).mul (hd (n + 1) t))).sub
      ((hd n t).const_mul (n : ℂ))).neg
  convert! h using 1
  simp only [laguerreJetOperator, Pi.sub_apply, one_mul, zero_sub, neg_one_mul, Nat.cast_add, Nat.cast_one,
    show n + 1 + 2 = n + 2 + 1 by omega, show n + 1 + 1 = n + 2 by omega]
  ring

theorem polynomial_mul_subexponential (f : ℝ → ℂ)
    (hf : ∀ ε : ℝ, 0 < ε → f =O[atTop] (fun t : ℝ => Real.exp (ε * t)))
    (p : ℂ[X]) (ε : ℝ) (hε : 0 < ε) :
    (fun t : ℝ => p.eval (t : ℂ) * f t) =O[atTop] (fun t : ℝ => Real.exp (ε * t)) := by
  have hp := polynomial_eval_isBigO_exp p (ε / 2) (by linarith)
  have hh := hf (ε / 2) (by linarith)
  convert! hp.mul hh using 1
  funext t
  rw [← Real.exp_add]
  congr 1
  ring

theorem laguerreJetOperator_subexponential (d : ℕ → ℝ → ℂ)
    (hd : ∀ n ε, 0 < ε → d n =O[atTop] (fun t : ℝ => Real.exp (ε * t)))
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    laguerreJetOperator d n =O[atTop] (fun t : ℝ => Real.exp (ε * t)) := by
  have h₁ := polynomial_mul_subexponential (d (n + 2)) (hd (n + 2)) X ε hε
  have h₂ := polynomial_mul_subexponential (d (n + 1)) (hd (n + 1)) (C ((n : ℂ) + 1) - X) ε hε
  have h₃ := polynomial_mul_subexponential (d n) (hd n) (C (n : ℂ)) ε hε
  convert! ((h₁.add h₂).sub h₃).neg_left using 1
  funext t
  simp only [laguerreJetOperator, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]

noncomputable def laguerreIteratedSlowJet (q : ℂ) (m : ℕ) (s : ℂ) : ℕ → ℕ → ℝ → ℂ
  | 0 => fun n => shiftedSlowDerivative n q m s
  | j + 1 => laguerreJetOperator (laguerreIteratedSlowJet q m s j)

theorem hasDerivAt_laguerreIteratedSlowJet (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.im ≠ 0) (j n : ℕ) (t : ℝ) :
    HasDerivAt (laguerreIteratedSlowJet q m s j n)
      (laguerreIteratedSlowJet q m s j (n + 1) t) t := by
  induction j generalizing n t with
  | zero => exact hasDerivAt_shiftedSlowDerivative n q m s hq hs t
  | succ j ih =>
      exact hasDerivAt_laguerreJetOperator _ ih n t

end DefocusingNLS

end OAI
