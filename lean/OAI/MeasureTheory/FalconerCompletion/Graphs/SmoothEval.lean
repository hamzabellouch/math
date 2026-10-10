import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularDerivativeStar
import OAI.MeasureTheory.FalconerCompletion.Graphs.SphereAxisSmoothIntegrable
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasureTransport2

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open scoped ComplexConjugate
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable {ι : Type*} [DecidableEq ι]

noncomputable def smoothEvalND (x : V) : SmoothFunctionND V →ₗ[ℂ] ℂ where
  toFun f := f.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq ι] in
lemma smoothPullND_product (e : V ≃ₗᵢ[ℝ] W) (S : Finset ι) (f : ι → SmoothFunctionND W) :
    smoothPullND e (smoothFinsetProductND S f) =
      smoothFinsetProductND S (fun i => smoothPullND e (f i)) := by
  apply Subtype.ext
  rfl

lemma smoothPullND_star (e : V ≃ₗᵢ[ℝ] W) (f : SmoothFunctionND W) :
    smoothPullND e (smoothStarND f) = smoothStarND (smoothPullND e f) := by
  apply Subtype.ext
  rfl

variable {n : ℕ}

noncomputable def euclideanAngularWordND (D : ℝ)
    (L : List (SphereAmbientND n →L[ℝ] SphereAmbientND n))
    (f : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) :=
  smoothPullND (sphereEuclideanIsoND n).symm
    (normalizedAngularWordND D L (smoothPullND (sphereEuclideanIsoND n) f))

lemma euclideanAngularWordND_star (D : ℝ)
    (L : List (SphereAmbientND n →L[ℝ] SphereAmbientND n))
    (f : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    euclideanAngularWordND D L (smoothStarND f)=smoothStarND (euclideanAngularWordND D L f) := by
  simp only [euclideanAngularWordND,smoothPullND_star,normalizedAngularWordND_star]

lemma euclideanSphereBND_product (j : ℕ) (S : Finset ι)
    (f : ι → SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (D : ι → ℝ) (hD : ∀ i ∈ S, D i ≠ 0) (w : EuclideanSpace ℝ (Fin (n+1))) :
    (euclideanSphereBND j (smoothFinsetProductND S f)).1 w =
      ((inverseAngularTermsND j S).map (fun a =>
        (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ)) *
          (∏ i ∈ S, (euclideanAngularWordND (D i) (a.2 i) (f i)).1 w))).sum := by
  have hh := congrArg (smoothEvalND ((sphereEuclideanIsoND n).symm w))
    (inverseAngularTermsND_normalized_expansion j S
      (fun i => smoothPullND (sphereEuclideanIsoND n) (f i)) D hD)
  simp only [map_list_sum,List.map_map,Function.comp_def,map_smul,smul_eq_mul] at hh
  simpa only [euclideanSphereBND,smoothPullND_product,smoothEvalND,smoothPullND,
    smoothFinsetProductND,euclideanAngularWordND,Function.comp_def,LinearMap.coe_mk,AddHom.coe_mk] using hh

variable {κ : Type*} [DecidableEq κ]

lemma euclideanSphereBND_endpoints (j : ℕ) (S : Finset ι) (T : Finset κ)
    (f : ι → SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (g : κ → SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (D : ι → ℝ) (E : κ → ℝ) (hD : ∀ i ∈ S, D i ≠ 0) (hE : ∀ k ∈ T, E k ≠ 0)
    (w : EuclideanSpace ℝ (Fin (n+1))) :
    (euclideanSphereBND j (smoothFinsetProductND (S.disjSum T)
      (Sum.elim f (fun k => smoothStarND (g k))))).1 w =
    ((inverseAngularTermsND j (S.disjSum T)).map (fun a =>
      (a.1*((((∏ i ∈ S, D i^(a.2 (Sum.inl i)).length)*
        (∏ k ∈ T, E k^(a.2 (Sum.inr k)).length)):ℝ):ℂ)) *
      ((∏ i ∈ S, (euclideanAngularWordND (D i) (a.2 (Sum.inl i)) (f i)).1 w) *
        conj (∏ k ∈ T, (euclideanAngularWordND (E k) (a.2 (Sum.inr k)) (g k)).1 w)))).sum := by
  have hDE : ∀ i ∈ S.disjSum T, Sum.elim D E i ≠ 0 := by
    intro i hi
    cases i with
    | inl i => exact hD i (Finset.inl_mem_disjSum.mp hi)
    | inr k => exact hE k (Finset.inr_mem_disjSum.mp hi)
  rw [euclideanSphereBND_product j _ _ (Sum.elim D E) hDE]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr,euclideanAngularWordND_star]
  simp only [smoothStarND,map_prod]
  rfl

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
open scoped ComplexConjugate
variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

lemma euclideanSphereBND_product_smooth (j : ℕ) (S : Finset ι)
    (f : ι → SmoothFunctionND V) (D : ι → ℝ) (hD : ∀ i ∈ S, D i ≠ 0) :
    euclideanSphereBND j (smoothFinsetProductND S f) =
      ((inverseAngularTermsND j S).map (fun a =>
        (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ)) •
          smoothFinsetProductND S (fun i => euclideanAngularWordND (D i) (a.2 i) (f i)))).sum := by
  apply Subtype.ext
  funext w
  change (euclideanSphereBND j (smoothFinsetProductND S f)).1 w = smoothEvalND w _
  rw [map_list_sum]
  simp only [List.map_map,Function.comp_def,map_smul,smul_eq_mul]
  exact euclideanSphereBND_product j S f D hD w

lemma euclideanAxisInverse_productND (j : ℕ) (S : Finset ι)
    (f : ι → SmoothFunctionND V) (D : ι → ℝ) (hD : ∀ i ∈ S, D i ≠ 0)
    (r : ℝ) (z : V) (ψ : V → ℂ) (hψ : Continuous ψ) :
    sphereAxisIntegralND r z (fun w => ψ w*(euclideanSphereBND j (smoothFinsetProductND S f)).1 w) =
      ((inverseAngularTermsND j S).map (fun a =>
        (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ)) *
          sphereAxisIntegralND r z (fun w => ψ w*
            (smoothFinsetProductND S (fun i => euclideanAngularWordND (D i) (a.2 i) (f i))).1 w))).sum := by
  have hh := congrArg (sphereAxisFunctionalND r z ψ hψ)
    (euclideanSphereBND_product_smooth j S f D hD)
  simpa only [map_list_sum,List.map_map,Function.comp_def,map_smul,smul_eq_mul,
    sphereAxisFunctionalND_apply] using hh

lemma euclideanAxisInverse_endpointsND (j : ℕ) (S : Finset ι) (T : Finset κ)
    (f : ι → SmoothFunctionND V) (g : κ → SmoothFunctionND V)
    (D : ι → ℝ) (E : κ → ℝ) (hD : ∀ i ∈ S, D i ≠ 0) (hE : ∀ k ∈ T, E k ≠ 0)
    (r : ℝ) (z : V) (ψ : V → ℂ) (hψ : Continuous ψ) :
    sphereAxisIntegralND r z (fun w => ψ w*(euclideanSphereBND j (smoothFinsetProductND (S.disjSum T)
      (Sum.elim f (fun k => smoothStarND (g k))))).1 w) =
    ((inverseAngularTermsND j (S.disjSum T)).map (fun a =>
      (a.1*((((∏ i ∈ S, D i^(a.2 (Sum.inl i)).length)*
        (∏ k ∈ T, E k^(a.2 (Sum.inr k)).length)):ℝ):ℂ)) *
      (∫ w, ψ w*spherePlaneWaveND r z w*
        (∏ i ∈ S, (euclideanAngularWordND (D i) (a.2 (Sum.inl i)) (f i)).1 w) *
        conj (∏ k ∈ T, (euclideanAngularWordND (E k) (a.2 (Sum.inr k)) (g k)).1 w)
          ∂canonicalSphereMeasureND V))).sum := by
  have hDE : ∀ i ∈ S.disjSum T, Sum.elim D E i ≠ 0 := by
    intro i hi
    cases i with
    | inl i => exact hD i (Finset.inl_mem_disjSum.mp hi)
    | inr k => exact hE k (Finset.inr_mem_disjSum.mp hi)
  rw [euclideanAxisInverse_productND j _ _ (Sum.elim D E) hDE r z ψ hψ]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr]
  apply congrArg (fun t : ℂ => (a.1 * (((∏ i ∈ S, D i^(a.2 (Sum.inl i)).length) *
    (∏ k ∈ T, E k^(a.2 (Sum.inr k)).length):ℝ):ℂ)) * t)
  apply integral_congr_ae
  filter_upwards with w
  simp only [smoothFinsetProductND,Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr]
  simp only [euclideanAngularWordND_star]
  simp only [smoothStarND,map_prod]
  simp only [spherePlaneWaveND,Complex.star_def]
  ring
end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
