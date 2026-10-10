import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentMapNaturality
import OAI.Combinatorics.Chromatic.Shuffle.TensorColumnSeriesFiltration

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
variable {K A B C D A' B' C' D' : Type*} [Field K]
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [CommRing A'] [CommRing B'] [CommRing C'] [CommRing D']
  [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D]
  [Algebra K A'] [Algebra K B'] [Algebra K C'] [Algebra K D']

lemma map_first (f : A →ₐ[K] A') (g : B →ₐ[K] B') (h : C →ₐ[K] C') (k : D →ₐ[K] D')
    (x : A⊗[K]B) :
    Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      (first x)=first (Algebra.TensorProduct.map f g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b => simp only [first_tmul,Algebra.TensorProduct.map_tmul,map_one]

lemma map_second (f : A →ₐ[K] A') (g : B →ₐ[K] B') (h : C →ₐ[K] C') (k : D →ₐ[K] D')
    (x : C⊗[K]D) :
    Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      (second x)=second (Algebra.TensorProduct.map h k x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul c d => simp only [second_tmul,Algebra.TensorProduct.map_tmul,map_one]

lemma map_middle (f : A →ₐ[K] A') (g : B →ₐ[K] B') (h : C →ₐ[K] C') (k : D →ₐ[K] D')
    (x : C⊗[K]B) :
    Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      (ElementaryPositivity.LinearDetection.middleEmbedding x)=
    ElementaryPositivity.LinearDetection.middleEmbedding (Algebra.TensorProduct.map h g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul c b =>
    change Algebra.TensorProduct.map (Algebra.TensorProduct.map f h) (Algebra.TensorProduct.map g k)
      ((1⊗ₜ[K]c)⊗ₜ[K](b⊗ₜ[K]1))=(1⊗ₜ[K]h c)⊗ₜ[K](g b⊗ₜ[K]1)
    simp only [Algebra.TensorProduct.map_tmul,map_one]

end ElementaryPositivity.TensorColumns

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

noncomputable local instance quotientFourSemiring (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ) :
    Semiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (braidFourRing a μ d₁ e₁ d₂ e₂).toSemiring
noncomputable local instance quotientFourNonAssoc (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonAssocSemiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (braidFourRing a μ d₁ e₁ d₂ e₂).toNonAssocSemiring

noncomputable def firstColumnBAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    B a μ d₁⊗[ℚ]B a μ d₂ →ₐ[ℚ](B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  ElementaryPositivity.TensorColumns.first
noncomputable def secondColumnBAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    B a μ e₁⊗[ℚ]B a μ e₂ →ₐ[ℚ](B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  ElementaryPositivity.TensorColumns.second

lemma fourQuotient_firstColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S d₁⊗[ℚ]S d₂) :
    fourQuotient a μ d₁ e₁ d₂ e₂ (firstColumnAlg d₁ e₁ d₂ e₂ x)=
    firstColumnBAlg a μ d₁ e₁ d₂ e₂ (quotientTensor a μ d₁ d₂ x) :=
  ElementaryPositivity.TensorColumns.map_first
    (quotientAlg a μ d₁) (quotientAlg a μ d₂) (quotientAlg a μ e₁) (quotientAlg a μ e₂) x

lemma fourQuotient_secondColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S e₁⊗[ℚ]S e₂) :
    fourQuotient a μ d₁ e₁ d₂ e₂ (secondColumnAlg d₁ e₁ d₂ e₂ x)=
    secondColumnBAlg a μ d₁ e₁ d₂ e₂ (quotientTensor a μ e₁ e₂ x) :=
  ElementaryPositivity.TensorColumns.map_second
    (quotientAlg a μ d₁) (quotientAlg a μ d₂) (quotientAlg a μ e₁) (quotientAlg a μ e₂) x

lemma fourQuotient_crossingColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : S e₁⊗[ℚ]S d₂) :
    fourQuotient a μ d₁ e₁ d₂ e₂ (crossingColumnAlg d₁ e₁ d₂ e₂ x)=
    crossingColumnBAlg a μ d₁ e₁ d₂ e₂ (quotientTensor a μ e₁ d₂ x) :=
  ElementaryPositivity.TensorColumns.map_middle
    (quotientAlg a μ d₁) (quotientAlg a μ d₂) (quotientAlg a μ e₁) (quotientAlg a μ e₂) x

lemma fourSeriesQuotient_firstColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (F : LaurentSeries (S d₁⊗[ℚ]S d₂)) :
    mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom F)=
    mapRing (firstColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (quotientTensor a μ d₁ d₂).toRingHom F) := by
  apply HahnSeries.ext
  funext j
  exact fourQuotient_firstColumn a μ d₁ e₁ d₂ e₂ (F.coeff j)

lemma fourSeriesQuotient_secondColumn (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (F : LaurentSeries (S e₁⊗[ℚ]S e₂)) :
    mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom F)=
    mapRing (secondColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom
      (mapRing (quotientTensor a μ e₁ e₂).toRingHom F) := by
  apply HahnSeries.ext
  funext j
  exact fourQuotient_secondColumn a μ d₁ e₁ d₂ e₂ (F.coeff j)

lemma fourSeriesQuotient_crossingUnit (a b : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (mappedInverseKernel b e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂))=
    Units.map (mapRing (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom).toMonoidHom
      (mixedInverseKernelUnit a b μ e₁ d₂) :=
  mapUnit_square (crossingColumnAlg d₁ e₁ d₂ e₂).toRingHom
    (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom
    (quotientTensor a μ e₁ d₂).toRingHom (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
    (fourQuotient_crossingColumn a μ d₁ e₁ d₂ e₂) (inverseKernelUnit b e₁ d₂)

lemma unit_map_ratio_square {R S T : Type*} [Ring R] [Ring S] [Ring T]
    (f : R →+* T) (g : S →+* T) (x y : Rˣ) (x' y' : Sˣ)
    (hx : Units.map f.toMonoidHom x=Units.map g.toMonoidHom x')
    (hy : Units.map f.toMonoidHom y=Units.map g.toMonoidHom y') :
    f (x*y⁻¹).val=g (x'*y'⁻¹).val := by
  have h : Units.map f.toMonoidHom (x*y⁻¹)=Units.map g.toMonoidHom (x'*y'⁻¹) := by
    rw [map_mul,map_inv,map_mul,map_inv,hx,hy]
  exact congrArg Units.val h

lemma fourSeriesQuotient_crossingRatio (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom
      (mappedInverseKernel a e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂) *
        (mappedInverseKernel (fun i j=>a j i) e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂))⁻¹).val=
    mapRing (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom (braidingRatioUnit a μ e₁ d₂).val := by
  exact unit_map_ratio_square
    (mapRing (fourQuotient a μ d₁ e₁ d₂ e₂).toRingHom)
    (mapRing (crossingColumnBAlg a μ d₁ e₁ d₂ e₂).toRingHom) _ _ _ _
    (fourSeriesQuotient_crossingUnit a a μ d₁ e₁ d₂ e₂)
    (fourSeriesQuotient_crossingUnit a (fun i j=>a j i) μ d₁ e₁ d₂ e₂)

lemma fourInputSeriesB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    mapRing (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      (fourInputSeries a d₁ e₁ d₂ e₂ f g)=
    fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he
      (quotientAlg a (slope c η) (d₁+d₂) f) (quotientAlg a (slope c η) (e₁+e₂) g) := by
  rewrite [fourInputSeries,map_mul,map_mul,
    fourSeriesQuotient_firstColumn a (slope c η) d₁ e₁ d₂ e₂ (tensorSeparationSeries a d₁ d₂ f),
    fourSeriesQuotient_secondColumn a (slope c η) d₁ e₁ d₂ e₂ (tensorSeparationSeries a e₁ e₂ g),
    fourSeriesQuotient_crossingRatio a (slope c η) d₁ e₁ d₂ e₂,
    fourInputSeriesB,unitalSeparationSeries_mk a c η hc d₁ d₂ hd f,
    unitalSeparationSeries_mk a c η hc e₁ e₂ he g]
  dsimp only [ElementaryPositivity.TensorColumns.seriesProduct,firstColumnBAlg,secondColumnBAlg]
  exact mul_comm _ _

end ElementaryPositivity.RawShuffle

end

end OAI
