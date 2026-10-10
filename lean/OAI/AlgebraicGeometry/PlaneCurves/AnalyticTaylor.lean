import Lean.Elab.Tactic.Omega
import OAI.AlgebraicGeometry.PlaneCurves.AnalyticScaling
import OAI.AlgebraicGeometry.PlaneCurves.TaylorMultiplicity

namespace OAI

/-!
# Polynomial Taylor expansions and analytic multiplicity
-/

section

/-! Explicit genuine Taylor expansions for bivariate monomials. Each monomial
is a continuous multilinear product composed with a coordinate-repetition map,
so its expansion has only its actual total-degree term. -/

noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators

private theorem analytic_order_zero (m : ℕ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun _ : ℂ × ℂ => (0 : ℂ)) 0 m := by
  refine ⟨constFormalMultilinearSeries ℂ (ℂ × ℂ) 0, hasFPowerSeriesAt_const, ?_⟩
  intro n hn
  cases n <;> ext v <;> rfl

private theorem analytic_order_add {f g : ℂ × ℂ → ℂ} {m : ℕ}
    (hf : HasAnalyticOrderAtLeast (𝕜 := ℂ) f 0 m)
    (hg : HasAnalyticOrderAtLeast (𝕜 := ℂ) g 0 m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (f + g) 0 m := by
  obtain ⟨p, hp, hz⟩ := hf
  obtain ⟨q, hq, hqz⟩ := hg
  refine ⟨p + q, hp.add hq, ?_⟩
  intro n hn
  simp [hz n hn, hqz n hn]

theorem analytic_order_const_smul {f : ℂ × ℂ → ℂ} {m : ℕ}
    (hf : HasAnalyticOrderAtLeast (𝕜 := ℂ) f 0 m) (c : ℂ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (c • f) 0 m := by
  obtain ⟨p, hp, hz⟩ := hf
  refine ⟨c • p, hp.const_smul, ?_⟩
  intro n hn
  simp [hz n hn]

/-- A bivariate monomial has a convergent power series with every coefficient
below its total degree zero. -/
theorem monomial_hasAnalyticOrderAtLeast (a b m : ℕ) (hm : m ≤ a + b) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x : ℂ × ℂ => x.1 ^ a * x.2 ^ b) 0 m := by
  let q := ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin (a + b)) ℂ
  let u : (ℂ × ℂ) →L[ℂ] (Fin (a + b) → ℂ) :=
    ContinuousLinearMap.pi (fun i =>
      if i.val < a then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hq : HasFPowerSeriesAt q q.toFormalMultilinearSeries (u 0) := by
    simpa only [map_zero] using q.hasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hfun : (q ∘ u) = (fun x : ℂ × ℂ => x.1 ^ a * x.2 ^ b) := by
    funext x
    simp only [q, u, Function.comp_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
      ContinuousLinearMap.pi_apply]
    rw [Fin.prod_univ_add]
    simp
  refine ⟨q.toFormalMultilinearSeries.compContinuousLinearMap u, ?_, ?_⟩
  · rw [← hfun]
    exact hq.compContinuousLinearMap
  · intro n hn
    have hne : a + b ≠ n := by omega
    ext v
    simp [FormalMultilinearSeries.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.toFormalMultilinearSeries, hne]

/-- Finite sums of actual analytic Taylor expansions with the same vanishing
range retain that range. -/
theorem analytic_order_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℂ × ℂ → ℂ) (m : ℕ)
    (hf : ∀ i ∈ s, HasAnalyticOrderAtLeast (𝕜 := ℂ) (f i) 0 m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun x => ∑ i ∈ s, f i x) 0 m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analytic_order_zero m
  | @insert i s hi ih =>
      have hsum := analytic_order_add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi, Pi.add_def] using hsum

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators

/-- The actual low-degree coefficient criterion for a centered bivariate
polynomial yields a genuine convergent Taylor expansion with those terms zero. -/
theorem eval_hasAnalyticOrderAtLeast_of_coeff
    (P : MvPolynomial (Fin 2) ℂ) (m : ℕ)
    (hcoeff : ∀ ell b, ell + b < m → P.coeff (Nagata.Workers.W30.exponentPair ell b) = 0) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x : ℂ × ℂ => MvPolynomial.eval (fun i => if i = 0 then x.1 else x.2) P) 0 m := by
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support) :
      HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun x : ℂ × ℂ => P.coeff d * (x.1 ^ d 0 * x.2 ^ d 1)) 0 m := by
    have hdegree : m ≤ d 0 + d 1 := by
      have hnonzero : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      have hnot : ¬d 0 + d 1 < m := by
        intro h
        apply hnonzero
        simpa only [Nagata.Workers.W30.exponentPair_eta] using hcoeff (d 0) (d 1) h
      omega
    simpa only [Pi.smul_def, smul_eq_mul] using
      analytic_order_const_smul (monomial_hasAnalyticOrderAtLeast (d 0) (d 1) m hdegree) (P.coeff d)
  have hsum := analytic_order_finset_sum P.support
    (fun d (x : ℂ × ℂ) => P.coeff d * (x.1 ^ d 0 * x.2 ^ d 1)) m hterm
  convert hsum using 1
  funext x
  rw [MvPolynomial.eval_eq']
  simp [Fin.prod_univ_two]

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28

/-- The actual polynomial evaluated on the affine complex plane has the
analytic Taylor vanishing forced by its actual maximal-ideal-power order. -/
theorem polynomial_order_implies_analytic_order
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ) (m : ℕ)
    (hP : Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x : ℂ × ℂ => MvPolynomial.eval (fun i => if i = 0 then x.1 else x.2) P) p m := by
  let pv : Fin 2 → ℂ := fun i => if i = 0 then p.1 else p.2
  have hc := (Nagata.AffineMultiplicity.orderAtLeast_finTwo_iff_taylor_coeff pv m P).mp hP
  obtain ⟨q, hq, hz⟩ := eval_hasAnalyticOrderAtLeast_of_coeff
    (Nagata.AffineMultiplicity.translateHom pv P) m hc
  refine ⟨q, ?_, hz⟩
  have hs := hq.comp_sub p
  simp only [zero_add] at hs
  apply hs.congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [Nagata.AffineMultiplicity.eval_translate]
    apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v P)
    funext i
    by_cases hi : i = 0 <;> simp [pv, hi]

end Nagata.Workers.W28

end
end

end OAI
