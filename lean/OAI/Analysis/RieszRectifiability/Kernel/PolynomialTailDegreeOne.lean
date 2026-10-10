import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PolynomialLeadingExterior
import OAI.Analysis.RieszRectifiability.Kernel.HomogeneousExteriorVanishing
import OAI.Analysis.RieszRectifiability.Kernel.PolynomialDegreeDrop

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem polynomial_tail_has_degree_one_representative {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ)
    (hi : IntegrableOn (fun x : Ambient d =>
      ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1)) :
    ∃ Q : MvPolynomial (Fin d) ℂ, Q.totalDegree ≤ 1 ∧
      ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) P =
        MvPolynomial.eval (fun j => (x j : ℂ)) Q := by
  have aux : ∀ N : ℕ, ∀ P : MvPolynomial (Fin d) ℂ, P.totalDegree ≤ N →
      IntegrableOn (fun x : Ambient d => ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ *
        inverseDistancePow (d + 2) 0 x) (closedExterior 0 1) →
      ∃ Q : MvPolynomial (Fin d) ℂ, Q.totalDegree ≤ 1 ∧
        ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) P =
          MvPolynomial.eval (fun j => (x j : ℂ)) Q := by
    intro N
    induction N with
    | zero =>
      intro P hP _
      exact ⟨P, by omega, fun _ => rfl⟩
    | succ N ih =>
      intro P hP htail
      by_cases hs : P.totalDegree ≤ 1
      · exact ⟨P, hs, fun _ => rfl⟩
      · have hhigh : 2 ≤ P.totalDegree := by omega
        have hz := homogeneous_polynomial_eval_zero_of_ae_exterior
          (MvPolynomial.homogeneousComponent P.totalDegree P)
          (MvPolynomial.homogeneousComponent_isHomogeneous P.totalDegree P)
          (by omega : P.totalDegree ≠ 0)
          (polynomial_leading_component_ae_zero_exterior P hhigh htail)
        let Q := P - MvPolynomial.homogeneousComponent P.totalDegree P
        have hQdeg : Q.totalDegree ≤ N := by
          have hd := polynomial_sub_top_degree_lt P (by omega)
          change (P - MvPolynomial.homogeneousComponent P.totalDegree P).totalDegree ≤ N
          omega
        have hQeval : ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) Q =
            MvPolynomial.eval (fun j => (x j : ℂ)) P := by
          intro x
          dsimp only [Q]
          rw [map_sub, hz x, sub_zero]
        have hQi : IntegrableOn (fun x : Ambient d =>
            ‖MvPolynomial.eval (fun j => (x j : ℂ)) Q‖ * inverseDistancePow (d + 2) 0 x)
            (closedExterior 0 1) := by
          apply htail.congr
          filter_upwards with x
          rw [hQeval x]
        obtain ⟨R, hR, hReq⟩ := ih Q hQdeg hQi
        exact ⟨R, hR, fun x => (hQeval x).symm.trans (hReq x)⟩
  exact aux P.totalDegree P le_rfl hi

end

end RieszRectifiability

end OAI
