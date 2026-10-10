import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisPolynomialMaps

namespace OAI

/-! # Transporting polynomial lattice parameters through an added real coordinate -/

noncomputable section
namespace PolycyclicRecognition
open Module

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {d e k n : ℕ}

theorem IsPolynomialInBasis.add {b : Basis (Fin d) ℝ U} {c : Basis (Fin e) ℝ V}
    {f g : U → V} (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b c g) :
    IsPolynomialInBasis b c (fun x => f x + g x) := by
  simpa only [IsPolynomialInBasis, map_add] using IsCoordinatePolynomial.add hf hg

theorem IsPolynomialInBasis.prod {b : Basis (Fin d) ℝ U}
    {c : Basis (Fin e) ℝ V} {a : Basis (Fin k) ℝ W}
    (q : Basis (Fin n) ℝ (V × W))
    {f : U → V} {g : U → W}
    (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b a g) :
    IsPolynomialInBasis b q (fun x => (f x, g x)) := by
  have hl := (IsPolynomialInBasis.linear (b := c) (c := q) (LinearMap.inl ℝ V W)).comp hf
  have hr := (IsPolynomialInBasis.linear (b := a) (c := q) (LinearMap.inr ℝ V W)).comp hg
  simpa only [Function.comp_def, LinearMap.inl_apply, LinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using hl.add hr

theorem polynomial_product_parameter (b : Basis (Fin d) ℝ V)
    (c : Basis (Fin e) ℝ (V × ℝ)) (p : V ≃ V)
    (hp : IsPolynomialInBasis b b p) :
    IsPolynomialInBasis c c (p.prodCongr (Equiv.refl ℝ)) := by
  have hf := hp.comp (IsPolynomialInBasis.linear (b := c) (c := b) (LinearMap.fst ℝ V ℝ))
  have hg := IsPolynomialInBasis.linear (b := c) (c := Module.finBasis ℝ ℝ)
    (LinearMap.snd ℝ V ℝ)
  exact hf.prod c hg

def transportedProductParameter (p : V ≃ V) (s : W ≃ₗ[ℝ] (V × ℝ))
    (E : W ≃ (V × ℝ)) : W ≃ W :=
  s.toEquiv.trans ((p.prodCongr (Equiv.refl ℝ)).trans E.symm)

theorem polynomial_transported_product_parameter
    (b : Basis (Fin d) ℝ V) (c : Basis (Fin e) ℝ (V × ℝ))
    (a : Basis (Fin k) ℝ W)
    (p : V ≃ V) (s : W ≃ₗ[ℝ] (V × ℝ)) (E : W ≃ (V × ℝ))
    (hp : IsPolynomialInBasis b b p) (hq : IsPolynomialInBasis b b p.symm)
    (hE : IsPolynomialInBasis a c E) (hEi : IsPolynomialInBasis c a E.symm) :
    IsPolynomialInBasis a a (transportedProductParameter p s E) ∧
      IsPolynomialInBasis a a (transportedProductParameter p s E).symm := by
  constructor
  · exact (hEi.comp (polynomial_product_parameter b c p hp)).comp
      (IsPolynomialInBasis.linear s.toLinearMap)
  · exact ((IsPolynomialInBasis.linear s.symm.toLinearMap).comp
      (polynomial_product_parameter b c p.symm hq)).comp hE

end PolycyclicRecognition

end

end OAI
