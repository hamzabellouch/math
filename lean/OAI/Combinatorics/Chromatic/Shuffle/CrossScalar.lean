import Mathlib
import OAI.Combinatorics.Chromatic.Histories.KernelEvaluation
import OAI.Combinatorics.Chromatic.Walls.EulerFiniteProduct

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma prod_packVariables {M : Type*} [CommMonoid M] (T : SplitTree I)
    (f : T.Centers → I → M) :
    (∏ i, ∏ x : Fin (T.dim i),f (T.centerOfVar (T.varEquiv.symm ⟨i,x⟩)) i)=
      ∏ z : T.Centers,∏ i,∏ _x : Fin (T.leafDimension z i),f z i := by
  classical
  have h:=Equiv.prod_comp (T.varEquiv.symm.trans T.leafVarsEquiv)
    (fun p : Σ z : T.Centers,Σ i,Fin (T.leafDimension z i)=>f p.1 p.2.1)
  simpa only [Fintype.prod_sigma,Equiv.trans_apply,leafVarsEquiv_center,
    leafVarsEquiv_pack,varEquiv_symm_packIndex] using h

noncomputable def scalarCrossKernel (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) : (LaurentSeries ℚ)ˣ :=
  ∏ z : L.Centers, ∏ t : R.Centers,
    affineUnit (w t-v z) ^ eulerForm a (L.leafDimension z) (R.leafDimension t)

lemma packProduct_eq_scalarCrossKernel (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    (∏ i, ∏ j, ∏ x : Fin (L.dim i), ∏ y : Fin (R.dim j),
      affineUnit (w (R.centerOfVar (R.varEquiv.symm ⟨j,y⟩))-
        v (L.centerOfVar (L.varEquiv.symm ⟨i,x⟩))) ^ SeparationInfinity.inverseExponent a i j)=
      scalarCrossKernel a L R v w := by
  classical
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.prod_comm]
  rw [prod_packVariables L (fun z i=>∏ j,∏ y : Fin (R.dim j),
    affineUnit (w (R.centerOfVar (R.varEquiv.symm ⟨j,y⟩))-v z) ^ SeparationInfinity.inverseExponent a i j)]
  conv_lhs =>
    arg 2
    ext z
    arg 2
    ext i
    arg 2
    ext x
    rw [prod_packVariables R (fun t j=>affineUnit (w t-v z)^SeparationInfinity.inverseExponent a i j)]
  unfold scalarCrossKernel
  apply Finset.prod_congr rfl
  intro z hz
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.prod_comm]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro t ht
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.prod_comm]
  exact ElementaryPositivity.inverseEuler_unit_product a (L.leafDimension z) (R.leafDimension t) _
end ElementaryPositivity.RawShuffle.SplitTree

namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity SplitTree
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
lemma crossPointEval_inverseKernel_scalar (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    Units.map (mapRing (crossPointEval L R v w)).toMonoidHom
      (rawInverseKernelUnit a L.dim R.dim)=scalarCrossKernel a L R v w := by
  rw [crossPointEval_inverseKernel,packProduct_eq_scalarCrossKernel]
end ElementaryPositivity.RawShuffle.SeparationInfinity

end
section
namespace ElementaryPositivity.CoefficientIdeals
open MvPolynomial
variable {R σ : Type*} [CommRing R]

lemma map_quotient_eq_zero_iff (J : Ideal R) (p : MvPolynomial σ R) :
    MvPolynomial.map (Ideal.Quotient.mk J) p=0 ↔ ∀ z,p.coeff z∈J := by
  constructor
  · intro hp z
    have h:=congrArg (fun polynomial=>AddMonoidAlgebra.coeff polynomial z) hp
    simpa only [coeff_map,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using h
  · intro hp
    ext z
    simpa only [coeff_map,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using hp z

lemma coeff_mul_mem (J : Ideal R) (p q : MvPolynomial σ R)
    (hp : ∀ z,p.coeff z∈J) (z : σ →₀ ℕ) : (p*q).coeff z∈J := by
  apply (map_quotient_eq_zero_iff J (p*q)).mp _ z
  rw [map_mul,(map_quotient_eq_zero_iff J p).mpr hp,zero_mul]

end ElementaryPositivity.CoefficientIdeals

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CoefficientIdeals
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma sourceFiltration_mul_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (x y : B a (SlopeArithmetic.slope c η) d)
    (hx : x∈sourceFiltration a c η hc θ d W) :
    x*y∈sourceFiltration a c η hc θ d W := by
  intro T hT hs hd k z hw
  subst d
  let ρ:=SplitTree.centeredRestrictionB a c η hc θ T hs
  let J:=SplitTree.degreeCutIdeal a (SlopeArithmetic.slope c η) T W
  have hxc : ∀ m,(ρ x).coeff m∈J := by
    intro m j hj
    exact hx T hT hs rfl j m hj
  have hxy:=coeff_mul_mem J (ρ x) (ρ y) hxc z
  change SplitTree.componentTensor a (SlopeArithmetic.slope c η) T k ((ρ (x*y)).coeff z)=0
  rw [map_mul]
  exact hxy k hw

noncomputable def sourceFiltrationIdeal (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Ideal (B a (SlopeArithmetic.slope c η) d) where
  __ := (sourceFiltration a c η hc θ d W).toAddSubmonoid
  smul_mem' r x hx := by
    change r*x∈sourceFiltration a c η hc θ d W
    rw [mul_comm]
    exact sourceFiltration_mul_mem a c η hc θ d W x r hx

end ElementaryPositivity.RawShuffle

end

end OAI
