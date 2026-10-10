import OAI.GroupTheory.PolycyclicRecognition.Geometry.SectionWeightedBoxes

namespace OAI

/-! # Multiplying the two ideal factors in the section error estimate -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V I J N : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  [Group N]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

omit [Fintype I] [Fintype J] in
/-- The restricted bracket has the same bound as the ambient adapted basis. -/
theorem ideal_basis_bracket_bound {C : ℝ}
    (hbr : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule bI bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule bI bQ lift hlift j⁆ k| ≤ C) :
    ∀ i j k, |bI.repr ⁅bI i, bI j⁆ k| ≤ C := by
  intro i j k
  have hh := hbr (Sum.inl i) (Sum.inl j) (Sum.inl k)
  simp only [basisWithQuotientLifts_inl] at hh
  change |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
    ((⁅bI i, bI j⁆ : U) : V) (Sum.inl k)| ≤ C at hh
  rwa [basisWithQuotientLifts_repr_inl] at hh

variable (ExpN : V → N) {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)

include hcoeff hmul in
/-- The ambient product of ideal exponentials remains in the ideal, with
an explicit polynomial coordinate bound in its own basis. -/
theorem ideal_product_coordinate_bound (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |bI.repr ⁅bI i, bI j⁆ k| ≤ C)
    {R : ℝ} (hR : 0 ≤ R) (u v : U)
    (hu : ‖bI.equivFun u‖ ≤ R) (hv : ‖bI.equivFun v‖ ≤ R) :
    ∃ w : U, ExpN (w : V) = ExpN (u : V) * ExpN (v : V) ∧
      ‖bI.equivFun w‖ ≤ sectionDynkinConstant (Fintype.card I) c C * (1 + R) ^ c := by
  let w := finiteDynkinPolynomial coeff ![u, v]
  have hvec : ∀ k : Fin 2, ‖bI.equivFun (![u, v] k)‖ ≤ R := by
    intro k
    fin_cases k
    · exact hu
    · exact hv
  refine ⟨w, ?_, ?_⟩
  · have he := finiteDynkinPolynomial_map U.incl coeff ![u, v]
    have hfun : (fun i : Fin 2 => U.incl (![u, v] i)) = ![(u : V), (v : V)] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun] at he
    change ExpN (U.incl w) = _
    rw [he, hmul]
  · exact (norm_finiteDynkinPolynomial_le bI coeff hcoeff _ hC hR hbr hvec).trans_eq
      (by dsimp [sectionDynkinConstant]; norm_num; ring)

end PolycyclicRecognition

end

end OAI
