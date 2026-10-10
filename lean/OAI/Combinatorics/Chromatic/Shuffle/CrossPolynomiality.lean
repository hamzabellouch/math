import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CrossScalar
import OAI.Combinatorics.Chromatic.Walls.CenterLineSpecialization
import OAI.Combinatorics.Chromatic.Shuffle.SymbolDetection
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentAffineCancellation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def crossPairs (L R : SplitTree I) : Finset ((L.node R).Centers×(L.node R).Centers) :=
  Finset.univ.image (fun p : L.Centers×R.Centers=>(Sum.inl p.1,Sum.inr p.2))

omit [Fintype I] [DecidableEq I] in
lemma crossPairs_injective (L R : SplitTree I) :
    Function.Injective (fun p : L.Centers×R.Centers=>((Sum.inl p.1,Sum.inr p.2) : (L.node R).Centers×(L.node R).Centers)) := by
  intro p q h
  exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h)) (Sum.inr.inj (congrArg Prod.snd h))

omit [Fintype I] [DecidableEq I] in
lemma crossPairs_ne (L R : SplitTree I) (p : (L.node R).Centers×(L.node R).Centers)
    (hp : p∈crossPairs L R) : p.1≠p.2 := by
  obtain ⟨⟨x,y⟩,_,rfl⟩:=Finset.mem_image.mp hp
  exact Sum.inl_ne_inr

omit [Fintype I] [DecidableEq I] in
lemma crossPairs_norev (L R : SplitTree I) (p : (L.node R).Centers×(L.node R).Centers)
    (hp : p∈crossPairs L R) : (p.2,p.1)∉crossPairs L R := by
  obtain ⟨⟨x,y⟩,_,rfl⟩:=Finset.mem_image.mp hp
  intro h
  obtain ⟨⟨z,t⟩,_,h⟩:=Finset.mem_image.mp h
  exact Sum.inl_ne_inr (congrArg Prod.fst h)

omit [DecidableEq I] in
lemma crossPairs_symmetric (a : I → I → ℕ) (c η : I → ℝ) (θ : ℝ)
    (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (p : (L.node R).Centers×(L.node R).Centers) (hp : p∈crossPairs L R) :
    eulerForm a ((L.node R).leafDimension p.1) ((L.node R).leafDimension p.2)=
      eulerForm a ((L.node R).leafDimension p.2) ((L.node R).leafDimension p.1) := by
  obtain ⟨⟨x,y⟩,_,rfl⟩:=Finset.mem_image.mp hp
  obtain ⟨hx,hsx⟩:=L.leafDimension_onSlope c η θ hL x
  obtain ⟨hy,hsy⟩:=R.leafDimension_onSlope c η θ hR y
  exact hχ _ _ hx hy hsx hsy

noncomputable def crossPolynomial (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) (e : ℤ → ℕ) : Polynomial ℚ :=
  ∏ z : L.Centers,∏ t : R.Centers,
    affinePolynomial (w t-v z) ^ e (eulerForm a (L.leafDimension z) (R.leafDimension t))

omit [DecidableEq I] in
lemma centerDenominator_crossPairs_line (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    lineSpecialization (Sum.elim v w) (Sum.elim (fun _=>1) (fun _=>0))
      (centerDenominator a (L.node R) (crossPairs L R))=
      crossPolynomial a L R v w (fun e=>(-e).toNat) := by
  classical
  unfold centerDenominator crossPairs
  rw [Finset.prod_image (fun p _ q _ h=>crossPairs_injective L R h)]
  simp only [map_prod,map_pow]
  rw [Fintype.prod_prod_type]
  unfold crossPolynomial
  apply Finset.prod_congr rfl
  intro z hz
  apply Finset.prod_congr rfl
  intro t ht
  congr 1
  simp only [diagonal,map_sub,lineSpecialization_X,Sum.elim_inl,Sum.elim_inr,
    _root_.map_zero,_root_.map_one,zero_mul,one_mul,add_zero,Algebra.algebraMap_self_apply,
    affinePolynomial]
  ring

omit [DecidableEq I] in
lemma scalarCrossKernel_denominator (a : I → I → ℕ) (L R : SplitTree I)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    (scalarCrossKernel a L R v w : LaurentSeries ℚ)*
      polynomial (crossPolynomial a L R v w (fun e=>(-e).toNat))=
      polynomial (crossPolynomial a L R v w Int.toNat) := by
  unfold scalarCrossKernel crossPolynomial
  simp only [map_prod,Units.coe_prod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro z hz
  rw [←Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t ht=>affineUnit_zpow_cancel _ _

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
