import OAI.AlgebraicGeometry.AbhyankarSathaye.CriticalPoint

namespace OAI

/-!
# Critical points obstruct polynomial coordinates

The polynomial chain rule shows that a coordinate polynomial over a nontrivial
commutative ring cannot have a point where every partial derivative vanishes.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

theorem polynomial_chain_rule {σ τ B : Type*} [Fintype σ] [CommRing B]
    (φ : MvPolynomial σ B →ₐ[B] MvPolynomial τ B)
    (f : MvPolynomial σ B) (j : τ) :
    pderiv j (φ f) = ∑ i, φ (pderiv i f) * pderiv j (φ (X i)) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [algHom_C]
  | add f g hf hg =>
      simp only [map_add, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f a hf =>
      have hite (p : Prop) [Decidable p] (A D : MvPolynomial τ B) :
          (if p then A+D else A) = A+(if p then D else 0) := by
        split_ifs <;> simp
      simp only [map_mul, pderiv_mul, map_add, hf]
      simp [pderiv_X, Pi.single_apply, apply_ite, add_mul,
        Finset.mul_sum, mul_comm, mul_assoc]
      simp only [hite, Finset.sum_add_distrib]
      simp

theorem no_coordinate_of_critical {σ B : Type*} [Fintype σ] [CommRing B]
    [Nontrivial B] (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) :
    ¬ ∃ (e : MvPolynomial σ B ≃ₐ[B] MvPolynomial σ B) (i : σ), e (X i) = f := by
  rintro ⟨e, i, he⟩
  have hchain := polynomial_chain_rule e.symm.toAlgHom f i
  change pderiv i (e.symm f) =
    ∑ j, e.symm (pderiv j f) * pderiv i (e.symm (X j)) at hchain
  have hinv : e.symm f = X i := by rw [← he, e.symm_apply_apply]
  rw [hinv, pderiv_X_self] at hchain
  have hz := congrArg (fun q => eval point (e q)) hchain
  simp [map_sum, hc] at hz

theorem F_not_coordinate : ¬ ∃ (e : R ≃ₐ[ℂ] R) (i : Fin 4), e (X i) = F :=
  no_coordinate_of_critical F criticalPoint critical_derivatives

end AbhyankarSathaye

end

end OAI
