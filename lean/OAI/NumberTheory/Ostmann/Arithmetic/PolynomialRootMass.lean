import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementExpectation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialRootMass
open scoped BigOperators
open MvPolynomial ProductExpectation PolynomialFlagReplacement

theorem expectation_const_mass {K : Type*} : ∀{n : ℕ}
    (S : Fin n → Finset K) (μ : Fin n → K → ℝ) (a : ℝ),
    expectation S μ (fun _ => a) = a*∏i,∑x∈S i,μ i x
  | 0,S,μ,a => by simp [expectation]
  | n+1,S,μ,a => by
    simp only [expectation,←Finset.sum_mul]
    rw [expectation_const_mass,Fin.prod_univ_succ]
    simp only [Fin.tail_def]
    ring

theorem expectation_const_le {K : Type*} {n : ℕ}
    (S : Fin n → Finset K) (μ : Fin n → K → ℝ) {C a : ℝ}
    (hμ : ∀i x,x∈S i → 0 ≤ μ i x) (hmass : ∀i,∑x∈S i,μ i x ≤ C)
    (ha : 0 ≤ a) : expectation S μ (fun _ => a) ≤ a*C^n := by
  rw [expectation_const_mass]
  apply mul_le_mul_of_nonneg_left _ ha
  calc
    _ ≤ ∏_i:Fin n,C := Finset.prod_le_prod₀
      (fun i _ => Finset.sum_nonneg (fun x hx => hμ i x hx)) (fun i _ => hmass i)
    _ = _ := by simp

theorem weighted_zero_bound {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] :
    ∀{n : ℕ} (P : MvPolynomial (Fin n) K) (_hP : P ≠ 0)
      (S : Fin n → Finset K) (μ : Fin n → K → ℝ) (α C : ℝ)
      (_hα : 0 ≤ α) (_hC : 0 ≤ C)
      (_hμ : ∀i a,a∈S i → 0 ≤ μ i a)
      (_hmass : ∀i,∑a∈S i,μ i a ≤ C)
      (_hatom : ∀i a,a∈S i → μ i a ≤ α),
      expectation S μ (fun x => if eval x P=0 then 1 else 0) ≤
        (P.totalDegree:ℝ)*α*C^(n-1)
  | 0,P,hP,S,μ,α,C,hα,hC,hμ,hmass,hatom => by
    rw [P.eq_C_of_isEmpty] at hP ⊢
    simp only [expectation,eval_C,totalDegree_C,Nat.cast_zero,zero_mul]
    simp [C_ne_zero.mp hP]
  | n+1,P,hP,S,μ,α,C,hα,hC,hμ,hmass,hatom => by
    let P' := finSuccEquiv K n P
    let k := P'.natDegree
    let Q := P'.leadingCoeff
    have hP' : P' ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hP
    have hQ : Q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP'
    have hdegree : Q.totalDegree+k ≤ P.totalDegree := totalDegree_coeff_finSuccEquiv_add_le P k hQ
    have hfiber (x : Fin n → K) :
        (∑a∈S 0,μ 0 a*(if eval (Fin.cons a x) P=0 then 1 else 0)) ≤
          C*(if eval x Q=0 then 1 else 0)+(k:ℝ)*α := by
      by_cases hx : eval x Q=0
      · simp only [hx,ite_true,mul_one]
        calc
          _ ≤ ∑a∈S 0,μ 0 a := Finset.sum_le_sum (fun a ha => by split_ifs <;> simp [hμ 0 a ha])
          _ ≤ C := hmass 0
          _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hα)
      · simp only [hx,ite_false,mul_zero,zero_add]
        let Px := P'.map (eval x)
        have hPx : Px ≠ 0 := by
          intro h
          apply hx
          have hh := congrArg (fun f:Polynomial K => f.coeff k) h
          simpa only [Px,Polynomial.coeff_map,Polynomial.coeff_zero,k,Q,Polynomial.leadingCoeff] using hh
        have hPxdeg : Px.natDegree ≤ k := Polynomial.natDegree_map_le
        calc
          _ = ∑a∈S 0 with Px.eval a=0,μ 0 a := by
            simp only [eval_eq_eval_mv_eval',Finset.sum_filter,Px,P']
            apply Finset.sum_congr rfl
            intro a ha
            split_ifs <;> simp
          _ ≤ (Px.natDegree:ℝ)*α :=
            AccidentalDivisibility.weighted_polynomial_roots Px hPx (S 0) (μ 0) hα (hatom 0)
          _ ≤ (k:ℝ)*α := mul_le_mul_of_nonneg_right (by exact_mod_cast hPxdeg) hα
    have htail : C*((Q.totalDegree:ℝ)*α*C^(n-1))=(Q.totalDegree:ℝ)*α*C^n := by
      cases n with
      | zero =>
        have hq0 : Q.totalDegree=0 := by rw [Q.eq_C_of_isEmpty,totalDegree_C]
        simp [hq0]
      | succ n => simp only [Nat.add_sub_cancel,pow_succ]; ring
    calc
      _ ≤ expectation (Fin.tail S) (Fin.tail μ)
        (fun x => C*(if eval x Q=0 then 1 else 0)+(k:ℝ)*α) :=
        ProductExpectation.mono (Fin.tail S) (Fin.tail μ) (fun i => hμ i.succ) hfiber
      _ = C*expectation (Fin.tail S) (Fin.tail μ) (fun x => if eval x Q=0 then 1 else 0)+
          expectation (Fin.tail S) (Fin.tail μ) (fun _ => (k:ℝ)*α) := by
        rw [ProductExpectation.add,expectation_const_mul]
      _ ≤ C*((Q.totalDegree:ℝ)*α*C^(n-1))+((k:ℝ)*α)*C^n := add_le_add
        (mul_le_mul_of_nonneg_left
          (weighted_zero_bound Q hQ (Fin.tail S) (Fin.tail μ) α C hα hC
            (fun i => hμ i.succ) (fun i => hmass i.succ) (fun i => hatom i.succ)) hC)
        (expectation_const_le _ _ (fun i => hμ i.succ) (fun i => hmass i.succ) (by positivity))
      _ = ((Q.totalDegree:ℝ)+k)*α*C^n := by rw [htail]; ring
      _ ≤ _ := by
        simp only [Nat.add_sub_cancel]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) hα) (pow_nonneg hC _)

end Ostmann.Arithmetic.PolynomialRootMass

end

end OAI
