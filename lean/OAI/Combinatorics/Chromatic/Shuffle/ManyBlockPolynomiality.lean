import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.AllPairDiagonal
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalPolynomialDivisibility

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus ElementaryPositivity.ShufflePolynomiality
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def centerDenominator (a : I → I → ℕ) (T : SplitTree I)
    (s : Finset (T.Centers × T.Centers)) : MvPolynomial T.Centers ℚ :=
  ∏ ij ∈ s, diagonal ij.1 ij.2 ^
    (-eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2)).toNat

theorem leadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (k : T.Degrees) (W : ℤ) (hw : 2*T.totalDegree k+T.doubleShift a=W)
    (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W)
    (s : Finset (T.Centers × T.Centers))
    (hs : ∀ ij∈s, ij.1≠ij.2) (hrev : ∀ ij∈s, (ij.2,ij.1)∉s)
    (hsym : ∀ ij∈s, eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2) =
      eulerForm a (T.leafDimension ij.2) (T.leafDimension ij.1)) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerDenominator a T s) ∣ leadingPolynomial a c η hc θ T hT k f := by
  classical
  apply product_dvd_of_scalar_factors
  · intro ij hij kl hkl hne
    apply (independent_diagonals (hs ij hij) (hs kl hkl) hne _).pow
    intro hr
    apply hrev ij hij
    have heq : (ij.2,ij.1)=kl := by
      simpa only [Prod.swap,Prod.eta] using congrArg Prod.swap hr
    rwa [heq]
  · intro ij hij
    have h := leadingPolynomial_diagonal_divisible a c η hc θ T hT k W hw f hf
      ij.2 ij.1 (hs ij hij).symm (hsym ij hij).symm
    simpa only [diagonal,map_pow,map_sub,map_X,hsym ij hij] using h

end ElementaryPositivity.RawShuffle.SplitTree

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def componentFinsupp (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) : tensor (quotientFamily a μ) T →ₗ[ℚ]
      (T.Degrees →₀ tensor (quotientFamily a μ) T) where
  toFun x := Finsupp.ofSupportFinite (fun k=>componentTensor a μ T k x) (by
    obtain ⟨s,hs,_⟩ := componentTensor_finite_decomposition a μ T x
    apply s.finite_toSet.subset
    intro k hk
    by_contra hn
    exact hk (hs k hn))
  map_add' x y := by
    ext k
    change componentTensor a μ T k (x+y)=componentTensor a μ T k x+componentTensor a μ T k y
    exact map_add _ x y
  map_smul' r x := by
    ext k
    change componentTensor a μ T k (r • x)=r • componentTensor a μ T k x
    exact map_smul _ r x

@[simp] lemma componentFinsupp_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) (k : T.Degrees) :
    componentFinsupp a μ T x k = componentTensor a μ T k x := rfl

lemma componentTensor_sum (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (x : tensor (quotientFamily a μ) T) (s : Finset T.Degrees)
    (hs : ∀ k∉s, componentTensor a μ T k x=0) :
    (∑ k∈s,componentTensor a μ T k x)=x := by
  classical
  apply sub_eq_zero.mp
  apply componentTensor_detect a μ T
  intro k
  rw [map_sub,map_sum]
  simp only [componentTensor_componentTensor]
  by_cases hk : k∈s
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hne
      simp [Ne.symm hne]
    · exact fun h=>False.elim (h hk)
  · simp only [hs k hk]
    rw [sub_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : k≠j := fun h=>hk (h ▸ hj)
    simp [hne]

noncomputable def weightComponent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) :
    tensor (quotientFamily a μ) T →ₗ[ℚ] tensor (quotientFamily a μ) T := by
  classical
  exact (Finsupp.lsum ℚ (fun k : T.Degrees=>
    if 2*T.totalDegree k+T.doubleShift a=W then LinearMap.id else 0)).comp
    (componentFinsupp a μ T)

lemma weightComponent_eq_sum (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x : tensor (quotientFamily a μ) T) (s : Finset T.Degrees)
    (hs : ∀ k∉s, componentTensor a μ T k x=0) :
    weightComponent a μ T W x = ∑ k∈s,
      if 2*T.totalDegree k+T.doubleShift a=W then componentTensor a μ T k x else 0 := by
  classical
  unfold weightComponent
  rw [LinearMap.comp_apply,Finsupp.lsum_apply]
  have hsub : (componentFinsupp a μ T x).support ⊆ s := by
    intro k hk
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hk) (hs k hn)
  rw [Finsupp.sum_of_support_subset _ hsub _ (by intro k hk; split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> rfl

lemma componentTensor_weightComponent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (x : tensor (quotientFamily a μ) T) (k : T.Degrees) :
    componentTensor a μ T k (weightComponent a μ T W x) =
      if 2*T.totalDegree k+T.doubleShift a=W then componentTensor a μ T k x else 0 := by
  classical
  obtain ⟨s,hs,he⟩ := componentTensor_finite_decomposition a μ T x
  rw [weightComponent_eq_sum a μ T W x s hs,map_sum]
  simp only [apply_ite,componentTensor_componentTensor,map_zero]
  by_cases hk : k∈s
  · rw [Finset.sum_eq_single k]
    · by_cases hw : 2*T.totalDegree k+T.doubleShift a=W <;> simp [hw]
    · intro j hj hne
      simp [Ne.symm hne]
    · exact fun h=>False.elim (h hk)
  · rw [hs k hk]
    simp only [ite_self]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : k≠j := fun h=>hk (h ▸ hj)
    simp [hne]

lemma polynomial_component_finite (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (p : MvPolynomial T.Centers (tensor (quotientFamily a μ) T)) :
    ∃ s : Finset T.Degrees, ∀ k∉s, mapLinear (componentTensor a μ T k) p=0 := by
  classical
  let s := p.support.biUnion (fun z=>(componentFinsupp a μ T (p.coeff z)).support)
  refine ⟨s,?_⟩
  intro k hk
  ext z
  simp only [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  by_cases hz : z∈p.support
  · have hnot : k∉(componentFinsupp a μ T (p.coeff z)).support := fun h=>
      hk (Finset.mem_biUnion.mpr ⟨z,hz,h⟩)
    exact Finsupp.notMem_support_iff.mp hnot
  · rw [notMem_support_iff.mp hz,map_zero]

lemma mapLinear_weightComponent_eq_sum (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (T : SplitTree I) (W : ℤ) (p : MvPolynomial T.Centers (tensor (quotientFamily a μ) T))
    (s : Finset T.Degrees) (hs : ∀ k∉s, mapLinear (componentTensor a μ T k) p=0) :
    mapLinear (weightComponent a μ T W) p = ∑ k∈s,
      if 2*T.totalDegree k+T.doubleShift a=W then mapLinear (componentTensor a μ T k) p else 0 := by
  classical
  ext z
  simp only [coeff_mapLinear,coeff_sum,apply_ite,AddMonoidAlgebra.coeff_zero,
    DFunLike.ite_apply,Finsupp.zero_apply]
  apply weightComponent_eq_sum
  intro k hk
  have h := congrArg (fun polynomial => AddMonoidAlgebra.coeff polynomial z) (hs k hk)
  simpa only [coeff_mapLinear,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using h

noncomputable def totalLeadingPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim) :=
  mapLinear (weightComponent a (SlopeArithmetic.slope c η) T W)
    (centeredRestrictionB a c η hc θ T hT f)

theorem totalLeadingPolynomial_denominator_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W)
    (s : Finset (T.Centers × T.Centers))
    (hs : ∀ ij∈s, ij.1≠ij.2) (hrev : ∀ ij∈s, (ij.2,ij.1)∉s)
    (hsym : ∀ ij∈s, eulerForm a (T.leafDimension ij.1) (T.leafDimension ij.2) =
      eulerForm a (T.leafDimension ij.2) (T.leafDimension ij.1)) :
    map (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) T))
      (centerDenominator a T s) ∣ totalLeadingPolynomial a c η hc θ T hT W f := by
  classical
  obtain ⟨t,ht⟩ := polynomial_component_finite a (SlopeArithmetic.slope c η) T
    (centeredRestrictionB a c η hc θ T hT f)
  unfold totalLeadingPolynomial
  rw [mapLinear_weightComponent_eq_sum a (SlopeArithmetic.slope c η) T W _ t ht]
  apply Finset.dvd_sum
  intro k hk
  split_ifs with hw
  · exact leadingPolynomial_denominator_divisible a c η hc θ T hT k W hw f hf s hs hrev hsym
  · exact dvd_zero _

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
