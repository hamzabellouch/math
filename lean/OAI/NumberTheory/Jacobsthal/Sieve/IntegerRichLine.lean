import OAI.NumberTheory.Jacobsthal.Estimates.RichLineHeights

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors ErdosConvexGraph

noncomputable def integerComplexification (P : MV ℤ) : MV ℂ :=
  MvPolynomial.map (Int.castRingHom ℂ) P

theorem integerComplexification_degree (P : MV ℤ) :
    (integerComplexification P).totalDegree = P.totalDegree := by
  unfold integerComplexification MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective P (Int.cast_injective)]

theorem integerComplexification_eval (P : MV ℤ) (p : ℤ × ℤ) :
    MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] (integerComplexification P) =
      (MvPolynomial.eval ![p.1,p.2] P : ℂ) := by
  have he : (Int.castRingHom ℂ) ∘ (![p.1,p.2] : Fin 2 → ℤ) = ![(p.1 : ℂ),(p.2 : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.map_eval (Int.castRingHom ℂ) ![p.1,p.2] P
  rw [he] at h
  exact h.symm

theorem integer_polynomial_rich_line (P : MV ℤ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ))
    (hbox : ∀ p ∈ X, InSquare S p) (hzero : ∀ p ∈ X, MvPolynomial.eval ![p.1,p.2] P = 0)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (M : ℝ) (hM : 1 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ (l : PrimitiveIntegerLine) (Y : Finset (ℤ × ℤ)),
      Y ⊆ X ∧ M < (Y.card : ℝ) ∧ (∀ r ∈ Y, l.Contains r) ∧
      (l.denominator : ℝ) ≤ 2*S/(Y.card : ℝ) ∧
      |(l.slope : ℝ)| ≤ 2*S/(Y.card : ℝ) ∧
      |(l.intercept : ℝ)| ≤ 4*S^2/(Y.card : ℝ) := by
  have hPc : integerComplexification P ≠ 0 := by
    intro h
    apply hP
    exact MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
      (by simpa only [integerComplexification,map_zero] using h)
  have hDc : (integerComplexification P).totalDegree ≤ D := by rwa [integerComplexification_degree]
  have hX : X ⊆ complexSquarePoints (integerComplexification P) S := by
    intro p hp
    apply (mem_complexSquarePoints _ S p).mpr
    refine ⟨hbox p hp,?_⟩
    rw [integerComplexification_eval,hzero p hp,Int.cast_zero]
  obtain ⟨F,l,Y,_hF,_hFP,_hdeg,_hY,hsub,hcard,hline,hden,hslope,hinter⟩ :=
    exists_rich_line_with_heights (integerComplexification P) hPc D hDc S hS X hX hinj M hM hlarge
  exact ⟨l,Y,hsub,hcard,hline,hden,hslope,hinter⟩

end ErdosRichLine

end

end Erdos970

end OAI
