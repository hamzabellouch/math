import Mathlib
import OAI.Combinatorics.Chromatic.Histories.TwoLeafDiagonal

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
open ElementaryPositivity.RawShuffle.SplitTree
variable {A D α β : Type*} [CommRing A] [CommRing D] [Algebra ℚ A] [Algebra ℚ D]

lemma mapLinear_extendPolynomial (f : A →ₐ[ℚ] D) (e : α ≃ β)
    (l : A →ₗ[ℚ] A) (m : D →ₗ[ℚ] D) (h : ∀ x, m (f x) = f (l x))
    (p : MvPolynomial α A) :
    mapLinear m (extendPolynomial f e p) = extendPolynomial f e (mapLinear l p) := by
  ext z
  obtain ⟨z,rfl⟩ := Finsupp.mapDomain_surjective e.surjective z
  simp only [coeff_mapLinear,Regroup.extendPolynomial_coeff]
  exact h _

lemma extendPolynomial_symm (f : A ≃ₐ[ℚ] D) (e : α ≃ β) (p : MvPolynomial α A) :
    extendPolynomial f.symm.toAlgHom e.symm (extendPolynomial f.toAlgHom e p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [extendPolynomial_C,AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,hp,extendPolynomial_X,Equiv.symm_apply_apply]

end ElementaryPositivity.CenterCalculus

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.CenterCalculus
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma dimensionEquivB_mem_sourceFiltration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    dimensionEquivB a (SlopeArithmetic.slope c η) h f ∈ sourceFiltration a c η hc θ e W := by
  subst e
  exact hf

namespace SplitTree

noncomputable def leadingPolynomial (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (k : T.Degrees) (f : B a (SlopeArithmetic.slope c η) T.dim) :=
  mapLinear (componentTensor a (SlopeArithmetic.slope c η) T k)
    (centeredRestrictionB a c η hc θ T hT f)

lemma Regroup.leadingPolynomial_natural (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {T U : SplitTree I} (e : Regroup T U)
    (hT : T.OnSlope c η θ) (hU : U.OnSlope c η θ) (k : T.Degrees)
    (f : B a (SlopeArithmetic.slope c η) T.dim) :
    leadingPolynomial a c η hc θ U hU (e.degrees k)
      (dimensionEquivB a (SlopeArithmetic.slope c η) e.dimension f) =
    extendPolynomial (e.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).toAlgHom
      e.centers (leadingPolynomial a c η hc θ T hT k f) := by
  unfold leadingPolynomial
  rw [e.centeredRestrictionB_natural a c η hc θ hT hU]
  apply mapLinear_extendPolynomial
  intro x
  exact (e.componentTensor_natural a (SlopeArithmetic.slope c η) k x).symm

theorem leadingPolynomial_diagonal_divisible (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ)
    (k : T.Degrees) (W : ℤ) (hw : 2*T.totalDegree k+T.doubleShift a=W)
    (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W)
    (i j : T.Centers) (hij : i≠j)
    (hsym : eulerForm a (T.leafDimension i) (T.leafDimension j) =
      eulerForm a (T.leafDimension j) (T.leafDimension i)) :
    (X i - X j)^(-eulerForm a (T.leafDimension i) (T.leafDimension j)).toNat ∣
      leadingPolynomial a c η hc θ T hT k f := by
  rcases Regroup.isolate_pair T i j hij with ⟨d,e,g,hi,hj⟩ | ⟨d,e,U,g,hi,hj⟩
  · have hdi : d=T.leafDimension i := by simpa only [hi,leafDimension] using g.leafDimension i
    have hej : e=T.leafDimension j := by simpa only [hj,leafDimension] using g.leafDimension j
    have hU := g.onSlope c η θ hT
    have h := twoLeading_diagonal_divisible a c η hc θ hU.1 hU.2
      (by simpa only [hdi,hej] using hsym) (g.degrees k).1 (g.degrees k).2 W
      (by have hw' := hw
          rw [← g.totalDegree k, ← g.doubleShift a] at hw'
          change 2*((g.degrees k).1+(g.degrees k).2)+(eulerForm a d d+eulerForm a e e)=W at hw'
          simpa only [add_assoc] using hw')
      (dimensionEquivB a (SlopeArithmetic.slope c η) g.dimension f)
      (dimensionEquivB_mem_sourceFiltration a c η hc θ g.dimension W f hf)
    change _ ∣ leadingPolynomial a c η hc θ _ hU (g.degrees k) _ at h
    rw [g.leadingPolynomial_natural a c η hc θ hT hU k f] at h
    have hh := map_dvd (extendPolynomial
      (g.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).symm.toAlgHom
      g.centers.symm) h
    rw [extendPolynomial_symm] at hh
    have hi' : g.centers.symm (Sum.inl ())=i := g.centers.symm_apply_eq.mpr hi.symm
    have hj' : g.centers.symm (Sum.inr ())=j := g.centers.symm_apply_eq.mpr hj.symm
    simpa only [map_pow,map_sub,extendPolynomial_X,hi',hj',hdi,hej] using hh
  · have hdi : d=T.leafDimension i := by simpa only [hi,leafDimension] using g.leafDimension i
    have hej : e=T.leafDimension j := by simpa only [hj,leafDimension] using g.leafDimension j
    have hU := g.onSlope c η θ hT
    have h := pairLeading_diagonal_divisible a c η hc θ hU.1.1 hU.1.2
      (by simpa only [hdi,hej] using hsym) U hU.2
      (g.degrees k).1.1 (g.degrees k).1.2 W (g.degrees k).2
      (by have h1 := g.totalDegree k; have h2 := g.doubleShift a
          change 2*((g.degrees k).1.1+(g.degrees k).1.2+U.totalDegree (g.degrees k).2)+
            eulerForm a d d+eulerForm a e e+U.doubleShift a=W
          have hw' : 2*(SplitTree.node (.node (.leaf d) (.leaf e)) U).totalDegree (g.degrees k)+
            (SplitTree.node (.node (.leaf d) (.leaf e)) U).doubleShift a=W := by rw [h1,h2]; exact hw
          change 2*((g.degrees k).1.1+(g.degrees k).1.2+U.totalDegree (g.degrees k).2)+
            ((eulerForm a d d+eulerForm a e e)+U.doubleShift a)=W at hw'
          simpa only [add_assoc] using hw')
      (dimensionEquivB a (SlopeArithmetic.slope c η) g.dimension f)
      (dimensionEquivB_mem_sourceFiltration a c η hc θ g.dimension W f hf)
    change _ ∣ leadingPolynomial a c η hc θ _ hU (g.degrees k) _ at h
    rw [g.leadingPolynomial_natural a c η hc θ hT hU k f] at h
    have hh := map_dvd (extendPolynomial
      (g.equivalence (quotientFamily a (SlopeArithmetic.slope c η))).symm.toAlgHom
      g.centers.symm) h
    rw [extendPolynomial_symm] at hh
    have hi' : g.centers.symm (Sum.inl (Sum.inl ()))=i := g.centers.symm_apply_eq.mpr hi.symm
    have hj' : g.centers.symm (Sum.inl (Sum.inr ()))=j := g.centers.symm_apply_eq.mpr hj.symm
    simpa only [map_pow,map_sub,extendPolynomial_X,hi',hj',hdi,hej] using hh

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
