import OAI.GroupTheory.PolycyclicRecognition.Analysis.SwitchEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RescaledLieFamily

namespace OAI

/-! # Actual group endpoints in rescaled logarithmic coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L G I : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G] {n c m : ℕ}

theorem exp_basis_listProduct (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (xs : List (Fin n → ℝ)) :
    Exp (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs)) =
      (xs.map (fun x => Exp (b.equivFun.symm x))).prod := by
  induction xs with
  | nil => simpa [polynomialListProduct] using hzero
  | cons x xs ih =>
    simp only [polynomialListProduct, List.map_cons, List.prod_cons]
    have he := basis_dynkinProduct b a (b.equivFun.symm x)
      (b.equivFun.symm (polynomialListProduct (dynkinProduct a (basisBracket b)) xs))
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm, ih]

theorem exp_rescaled_differenceWord (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (t : Fin (m + m) → ℝ) :
    Exp (b.equivFun.symm (differenceAmplitudeWordEndpoint a letters
      (basisBracket b, fun i => b.equivFun (Real.exp (r * s i) • X i)) t)) =
      (List.ofFn (fun j => Exp
        ((t (Fin.castAdd m j) - t (Fin.natAdd m j)) •
          (Real.exp (r * s (letters j)) • X (letters j))))).prod := by
  unfold differenceAmplitudeWordEndpoint amplitudeWordEndpoint
  rw [exp_basis_listProduct b Exp hzero a hm, List.map_ofFn]
  simp only [Function.comp_def, differenceParameters_apply, map_smul, LinearEquiv.symm_apply_apply]

theorem sampled_rescaled_endpoint_eq (b : Basis (Fin n) ℝ L) (Exp : L → G)
    (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (sample : ℕ → ℝ → G)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ j : Fin m, ∀ u, sample j.val u =
      Exp (u • (Real.exp (r * s (letters j)) • X (letters j))))
    (x : G) (t : Fin (m + m) → ℝ) :
    switchEndpoint m x (sampledSwitchParameters sample m t) =
      x * Exp (b.equivFun.symm (differenceAmplitudeWordEndpoint a letters
        (basisBracket b, fun i => b.equivFun (Real.exp (r * s i) • X i)) t)) := by
  rw [sampledSwitchEndpoint_eq sample m hsub, exp_rescaled_differenceWord b Exp hzero a hm]
  simp only [hsample]

end PolycyclicRecognition

end

end OAI
