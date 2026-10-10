import OAI.NumberTheory.Jacobsthal.Harmonic.RealAlgebraicFibers

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection

def realExceptionalAbscissae (Q : MV ℝ) : Set ℝ :=
  Complex.ofReal ⁻¹' exceptionalAbscissae (complexify Q)

theorem mem_realExceptionalAbscissae (Q : MV ℝ) (x y : ℝ) (hzero : peval Q x y = 0)
    (hbad : peval (partialX Q) x y = 0 ∨ peval (partialY Q) x y = 0 ∨
      peval (inflectionPolynomial Q) x y = 0) : x ∈ realExceptionalAbscissae Q := by
  have hc : complexPoint (x,y) ∈ exceptionalPoints (complexify Q) := by
    rcases hbad with hx | hy | hi
    · apply Or.inl
      apply (real_critical_iff Q (x,y)).mpr
      change MvPolynomial.eval ![x,y] Q = 0 ∧
        (MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 0 Q) = 0 ∨
         MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 1 Q) = 0)
      simpa only [← peval_eq_eval_pair,partialX,partialY] using And.intro hzero (Or.inl hx)
    · apply Or.inl
      apply (real_critical_iff Q (x,y)).mpr
      change MvPolynomial.eval ![x,y] Q = 0 ∧
        (MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 0 Q) = 0 ∨
         MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 1 Q) = 0)
      simpa only [← peval_eq_eval_pair,partialX,partialY] using And.intro hzero (Or.inr hy)
    · apply Or.inr
      change MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (complexify Q) = 0 ∧
        MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (inflection (complexify Q)) = 0
      constructor
      · rw [complexify_eval,← peval_eq_eval_pair,hzero,Complex.ofReal_zero]
      · rw [← complexify_inflection,complexify_eval,← peval_eq_eval_pair,hi,Complex.ofReal_zero]
  exact ⟨complexPoint (x,y),hc,rfl⟩

theorem divisible_critical_marks (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hdiv : complexify Q ∣ inflection (complexify Q)) :
    ∃ B : Finset ℝ, B.card ≤ 4*Q.totalDegree^2 ∧ ∀ x ∉ B, ∀ y : ℝ, peval Q x y ≠ 0 := by
  classical
  obtain ⟨hf,hc⟩ := real_critical_abscissae_bound Q hQ hdeg
  refine ⟨hf.toFinset,?_,?_⟩
  · rwa [← ncard_eq_toFinset_card _ hf]
  · intro x hx y hzero
    apply hx
    apply hf.mem_toFinset.mpr
    refine ⟨(x,y),?_,rfl⟩
    have hgrad := divisible_inflection_gradient_zero Q hQ hdeg hdiv x y hzero
    change MvPolynomial.eval ![x,y] Q = 0 ∧
      (MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 0 Q) = 0 ∨
       MvPolynomial.eval ![x,y] (MvPolynomial.pderiv 1 Q) = 0)
    simpa only [← peval_eq_eval_pair,partialX,partialY] using And.intro hzero (Or.inl hgrad.1)

theorem nondivisible_exceptional_marks (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hnd : ¬complexify Q ∣ inflection (complexify Q)) :
    ∃ B : Finset ℝ, B.card ≤ 10*Q.totalDegree^2 ∧
      ∀ x ∉ B, ∀ y : ℝ, peval Q x y = 0 →
        peval (partialX Q) x y ≠ 0 ∧ peval (partialY Q) x y ≠ 0 ∧
          peval (inflectionPolynomial Q) x y ≠ 0 := by
  classical
  have hd : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  obtain ⟨hc,hcard⟩ := exceptional_abscissae_bound (complexify Q) hQ hd hnd
  obtain ⟨hf,hpre⟩ := finite_real_preimage (exceptionalAbscissae (complexify Q)) hc
  change (realExceptionalAbscissae Q).Finite at hf
  refine ⟨hf.toFinset,?_,?_⟩
  · rw [← ncard_eq_toFinset_card _ hf]
    exact hpre.trans (by simpa only [complexify_totalDegree] using hcard)
  · intro x hx y hz
    have hn : x ∉ realExceptionalAbscissae Q := fun h => hx (hf.mem_toFinset.mpr h)
    refine ⟨?_,?_,?_⟩
    · exact fun h => hn (mem_realExceptionalAbscissae Q x y hz (Or.inl h))
    · exact fun h => hn (mem_realExceptionalAbscissae Q x y hz (Or.inr (Or.inl h)))
    · exact fun h => hn (mem_realExceptionalAbscissae Q x y hz (Or.inr (Or.inr h)))

theorem exists_bad_abscissae (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) :
    ∃ B : Finset ℝ, B.card ≤ 10*Q.totalDegree^2 ∧
      ∀ x ∉ B, ∀ y : ℝ, peval Q x y = 0 →
        peval (partialX Q) x y ≠ 0 ∧ peval (partialY Q) x y ≠ 0 ∧
          peval (inflectionPolynomial Q) x y ≠ 0 := by
  by_cases hdiv : complexify Q ∣ inflection (complexify Q)
  · obtain ⟨B,hB,hzero⟩ := divisible_critical_marks Q hQ hdeg hdiv
    exact ⟨B,hB.trans (Nat.mul_le_mul_right _ (by omega)),
      fun x hx y hy => (hzero x hx y hy).elim⟩
  · exact nondivisible_exceptional_marks Q hQ hdeg hdiv

end ErdosAlgebraicCurve

end

end Erdos970

end OAI
