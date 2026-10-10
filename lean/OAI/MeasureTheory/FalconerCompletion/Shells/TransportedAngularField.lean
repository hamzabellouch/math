import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Recursion.PrefixDescriptors

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ContDiff

section Transport
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

noncomputable def transportedAngularField (e : V ≃ₗᵢ[ℝ] W) (A : V →L[ℝ] V) : W →L[ℝ] W :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma angularWord_pull_exact (e : V ≃ₗᵢ[ℝ] W) (L : List (V →L[ℝ] V))
    (b : SmoothFunctionND W) (u : V) :
    (Attempt4PrefixShell.angularWordOperatorND L (Attempt4PrefixShell.smoothPullND e b)).1 u=
      (angularWordOperatorND (L.map (transportedAngularField e)) b).1 (e u) := by
  induction L generalizing u with
  | nil => rfl
  | cons A L ih =>
    have heq : (Attempt4PrefixShell.angularWordOperatorND L
        (Attempt4PrefixShell.smoothPullND e b)).1=
        (angularWordOperatorND (L.map (transportedAngularField e)) b).1 ∘ e := by
      funext z
      exact ih (u:=z)
    change fderiv ℝ (Attempt4PrefixShell.angularWordOperatorND L
      (Attempt4PrefixShell.smoothPullND e b)).1 u (A u)=
      fderiv ℝ (angularWordOperatorND (L.map (transportedAngularField e)) b).1 (e u)
        (transportedAngularField e A (e u))
    rw [heq,fderiv_comp u
      ((smoothFunctionND_contDiff _).differentiable (by simp) (e u))
      (e.toContinuousLinearEquiv.differentiableAt)]
    simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.fderiv,
      transportedAngularField,ContinuousLinearEquiv.coe_coe]
    congr 2
    exact congrArg A (e.symm_apply_apply u).symm

lemma normalizedAngularWord_pull_exact (e : V ≃ₗᵢ[ℝ] W) (D : ℝ)
    (L : List (V →L[ℝ] V)) (b : SmoothFunctionND W) (u : V) :
    (Attempt4PrefixShell.normalizedAngularWordND D L
      (Attempt4PrefixShell.smoothPullND e b)).1 u=
      (normalizedAngularWordND D (L.map (transportedAngularField e)) b).1 (e u) := by
  change ((D:ℂ)^L.length)⁻¹*(Attempt4PrefixShell.angularWordOperatorND L
    (Attempt4PrefixShell.smoothPullND e b)).1 u=
    ((D:ℂ)^(L.map (transportedAngularField e)).length)⁻¹*
      (angularWordOperatorND (L.map (transportedAngularField e)) b).1 (e u)
  rw [List.length_map,angularWord_pull_exact]
end Transport

variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma prefixEndpoint_word_exact (x : EuclideanSpace ℝ (Fin (n+1)))
    (b : PolicyDescriptor)
    (L : List (Attempt4PrefixShell.SphereAmbientND n →L[ℝ] Attempt4PrefixShell.SphereAmbientND n))
    (w : EuclideanSpace ℝ (Fin (n+1))) :
    (Attempt4PrefixShell.euclideanAngularWordND
      (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig) L (e.prefixEndpointSmooth x b)).1 w=
      (actualEndpointAngular
        (L.map (transportedAngularField (Attempt4PrefixShell.sphereEuclideanIsoND n)))
        e.ρ e.mass e.N e.sig e.C e.J e.i b x).1 w := by
  change (Attempt4PrefixShell.normalizedAngularWordND _ L
    (Attempt4PrefixShell.smoothPullND (Attempt4PrefixShell.sphereEuclideanIsoND n)
      (e.prefixEndpointSmooth x b))).1 ((Attempt4PrefixShell.sphereEuclideanIsoND n).symm w)=_
  simpa only [LinearIsometryEquiv.apply_symm_apply,actualEndpointAngular,
    actualEndpointSmooth,prefixEndpointSmooth,CurrentFalconer.smoothFunctionSpaceND,
    Attempt4PrefixShell.smoothFunctionSpaceND] using
    normalizedAngularWord_pull_exact (Attempt4PrefixShell.sphereEuclideanIsoND n)
      (sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig) L
      (actualEndpointSmooth e.ρ e.mass e.N e.sig e.C e.J e.i b x)
      ((Attempt4PrefixShell.sphereEuclideanIsoND n).symm w)

end PositiveDistanceState

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ContDiff
variable {n : ℕ}
abbrev PrefixAssignment (n : ℕ) := ℂ × ((PolicyDescriptor ⊕ PolicyDescriptor) →
  List (Attempt4PrefixShell.SphereAmbientND n →L[ℝ] Attempt4PrefixShell.SphereAmbientND n))

noncomputable def prefixLeftWords (p : PrefixAssignment n) (b : PolicyDescriptor) :
    List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :=
  (p.2 (Sum.inl b)).map (transportedAngularField (Attempt4PrefixShell.sphereEuclideanIsoND n))
noncomputable def prefixRightWords (p : PrefixAssignment n) (b : PolicyDescriptor) :
    List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :=
  (p.2 (Sum.inr b)).map (transportedAngularField (Attempt4PrefixShell.sphereEuclideanIsoND n))

namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

noncomputable def prefixInverseLeft (p : PrefixAssignment n) :
    EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ :=
  Attempt4PrefixShell.inverseLeftEndpointND e.prefixDescriptors
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    e.prefixEndpointSmooth (fun _ => 1) p
noncomputable def prefixInverseRight (p : PrefixAssignment n) :
    EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ :=
  Attempt4PrefixShell.inverseRightEndpointND e.prefixDescriptors
    (fun b => sourceMaskScaleND (descriptorLength b) ((2:ℝ)^e.N) e.sig)
    e.prefixEndpointSmooth (fun _ => 1) p

lemma prefixInverseLeft_eq (p : PrefixAssignment n) (x w : EuclideanSpace ℝ (Fin (n+1))) :
    e.prefixInverseLeft p x w=
      (actualAngularProduct e.prefixDescriptors id (prefixLeftWords p)
        e.ρ e.mass e.N e.sig e.C e.J e.i x).1 w := by
  classical
  simp only [prefixInverseLeft,Attempt4PrefixShell.inverseLeftEndpointND,one_mul,
    actualAngularProduct,smoothFinsetProductND]
  apply Finset.prod_congr rfl
  intro b hb
  exact e.prefixEndpoint_word_exact x b (p.2 (Sum.inl b)) w

lemma prefixInverseRight_eq (p : PrefixAssignment n) (x w : EuclideanSpace ℝ (Fin (n+1))) :
    e.prefixInverseRight p x w=
      (actualAngularProduct e.prefixDescriptors id (prefixRightWords p)
        e.ρ e.mass e.N e.sig e.C e.J e.i x).1 w := by
  classical
  simp only [prefixInverseRight,Attempt4PrefixShell.inverseRightEndpointND,one_mul,
    actualAngularProduct,smoothFinsetProductND]
  apply Finset.prod_congr rfl
  intro b hb
  exact e.prefixEndpoint_word_exact x b (p.2 (Sum.inr b)) w

lemma prefixInverseLeft_measurable (p : PrefixAssignment n) :
    Measurable (Function.uncurry (e.prefixInverseLeft p)) := by
  simpa only [Function.uncurry_def,e.prefixInverseLeft_eq] using
    actualAngularProduct_measurable e.prefixDescriptors id (prefixLeftWords p)
      e.ρ e.mass e.N e.sig e.C e.J e.i

lemma prefixInverseRight_measurable (p : PrefixAssignment n) :
    Measurable (Function.uncurry (e.prefixInverseRight p)) := by
  simpa only [Function.uncurry_def,e.prefixInverseRight_eq] using
    actualAngularProduct_measurable e.prefixDescriptors id (prefixRightWords p)
      e.ρ e.mass e.N e.sig e.C e.J e.i

lemma prefixInverseWord_total (j : ℕ) {p : PrefixAssignment n}
    (hp : p ∈ Attempt4PrefixShell.inverseAngularTermsND j (e.prefixDescriptors.disjSum e.prefixDescriptors)) :
    (∑ b ∈ e.prefixDescriptors, (prefixLeftWords p b).length)+
      (∑ b ∈ e.prefixDescriptors, (prefixRightWords p b).length) ≤ 2*j := by
  have h := Attempt4PrefixShell.inverseAngularTermsND_budget j _ hp
  simpa only [Finset.sum_disjSum,prefixLeftWords,prefixRightWords,List.length_map] using h

end PositiveDistanceState

lemma uniform_prefixInverse_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)), N₀ ≤ e.N → e.sig=sig → e.J=J →
      IsFiniteMeasure e.ρ → 0 < e.q → e.t ≤ e.N → ∀ (p : PrefixAssignment n) (k : ℕ)
        (x w : EuclideanSpace ℝ (Fin (n+1))), ‖w‖=1 →
      (w∈tsupport (iteratedFDeriv ℝ k (e.prefixInverseLeft p x)) →
        ∀ b∈e.prefixDescriptors, (x,w)∈endpointGood e.ρ e.mass e.N e.sig e.C e.J (e.i+1) b) ∧
      (w∈tsupport (iteratedFDeriv ℝ k (e.prefixInverseRight p x)) →
        ∀ b∈e.prefixDescriptors, (x,w)∈endpointGood e.ρ e.mass e.N e.sig e.C e.J (e.i+1) b) := by
  obtain ⟨N₀,h⟩ := uniform_actualAngularProduct_support (d:=n+1) (ι:=PolicyDescriptor) hsig hJ
  refine ⟨N₀,?_⟩
  intro e he hse hJe hf hq ht p k x w hw
  have hv : ∀ b∈e.prefixDescriptors, ValidDescriptor e.N (id b) :=
    fun b hb => policyDescriptor_valid _ hq ht hb
  have hleft := h e.N he e.ρ hf e.mass e.C e.i e.prefixDescriptors id hv
    (prefixLeftWords p) k x w hw
  have hright := h e.N he e.ρ hf e.mass e.C e.i e.prefixDescriptors id hv
    (prefixRightWords p) k x w hw
  rw [← hse,← hJe] at hleft hright
  have hl : e.prefixInverseLeft p x=
      (actualAngularProduct e.prefixDescriptors id (prefixLeftWords p)
        e.ρ e.mass e.N e.sig e.C e.J e.i x).1 := funext (e.prefixInverseLeft_eq p x)
  have hr : e.prefixInverseRight p x=
      (actualAngularProduct e.prefixDescriptors id (prefixRightWords p)
        e.ρ e.mass e.N e.sig e.C e.J e.i x).1 := funext (e.prefixInverseRight_eq p x)
  rw [hl,hr]
  exact ⟨hleft,hright⟩

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer Filter
open scoped ContDiff
variable {n : ℕ}

noncomputable def prefixInverseVocabulary (n J : ℕ) :
    Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))) := by
  classical
  exact ((Finset.range (J+1)).biUnion (fun j =>
    Attempt4PrefixShell.polynomialAngularSubwordsND (Attempt4PrefixShell.sphereBasisND n)
      (Attempt4PrefixShell.sphereBPolynomialND n j))).image
    (List.map (transportedAngularField (Attempt4PrefixShell.sphereEuclideanIsoND n)))

lemma prefixInverseVocabulary_budget (J : ℕ) {L : List
    (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))}
    (hL : L ∈ prefixInverseVocabulary n J) : L.length ≤ 2*J := by
  classical
  obtain ⟨L',hL',rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨j,hj,hL'⟩ := Finset.mem_biUnion.mp hL'
  rw [List.length_map]
  exact (Attempt4PrefixShell.polynomialAngularSubwordsND_budget _ _ hL').trans
    ((Nat.mul_le_mul_left 2 (Attempt4PrefixShell.sphereBPolynomialND_degree n j)).trans
      (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))

lemma prefixInverseVocabulary_mem (J j : ℕ) (hj : j ≤ J)
    (S : Finset (PolicyDescriptor ⊕ PolicyDescriptor)) {p : PrefixAssignment n}
    (hp : p ∈ Attempt4PrefixShell.inverseAngularTermsND j S)
    (b : PolicyDescriptor ⊕ PolicyDescriptor) :
    (p.2 b).map (transportedAngularField (Attempt4PrefixShell.sphereEuclideanIsoND n)) ∈
      prefixInverseVocabulary n J := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨p.2 b,Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le hj),?_⟩,rfl⟩
  exact Attempt4PrefixShell.polynomialLeibnizTermsND_subword _ _ S hp b

lemma uniform_prefixInverse_derivatives (M J : ℕ) {sig : ℝ} (hsig : 0 < sig) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ N : ℕ in atTop, ∀ (e : PositiveDistanceState (n+1)),
      e.N=N → e.sig=sig → 0 < e.q → ∀ j ≤ J, ∀ p ∈
        Attempt4PrefixShell.inverseAngularTermsND j (e.prefixDescriptors.disjSum e.prefixDescriptors),
      ∀ (x : EuclideanSpace ℝ (Fin (n+1))), ∀ r ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ r (e.prefixInverseLeft p x) w‖ ≤
        D^(2*J)*((((2:ℝ)^N)^sig)*sourceMaskScaleND ((e.t-e.a)/2) ((2:ℝ)^N) sig)^r ∧
      ‖iteratedFDeriv ℝ r (e.prefixInverseRight p x) w‖ ≤
        D^(2*J)*((((2:ℝ)^N)^sig)*sourceMaskScaleND ((e.t-e.a)/2) ((2:ℝ)^N) sig)^r := by
  classical
  obtain ⟨D,hD,h⟩ := uniform_actualAngularProduct_derivatives
    (ι:=PolicyDescriptor) (prefixInverseVocabulary n J) M (2*J) (2*J) 3
    (fun _ hL => prefixInverseVocabulary_budget J hL) 8 sig hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [h,eventually_ge_atTop 1] with N hN hN₁
  intro e he hse hq j hj p hp x r hr w hw
  subst N
  rw [← hse] at hN ⊢
  have hc : (e.prefixDescriptors.card:ℝ) ≤ 8*(e.N:ℝ)^3 := by
    exact actualPolicy_card_bound (adjustedProfile (d:=n+1) e.mass e.N) hN₁ hq
  have hl : ∀ b ∈ e.prefixDescriptors, descriptorLength (id b) ≤ (e.t-e.a)/2 :=
    fun b hb => policyDescriptor_length_le_half _ hq hb
  have ht := (e.prefixInverseWord_total j hp).trans (Nat.mul_le_mul_left 2 hj)
  have hleft := hN e.prefixDescriptors id (prefixLeftWords p) e.ρ e.mass e.C e.J e.i
    ((e.t-e.a)/2) hc
    (fun b _ => prefixInverseVocabulary_mem J j hj _ hp (Sum.inl b))
    ((Nat.le_add_right _ _).trans ht) hl x r hr w hw
  have hright := hN e.prefixDescriptors id (prefixRightWords p) e.ρ e.mass e.C e.J e.i
    ((e.t-e.a)/2) hc
    (fun b _ => prefixInverseVocabulary_mem J j hj _ hp (Sum.inr b))
    ((Nat.le_add_left _ _).trans ht) hl x r hr w hw
  have hleftEq : e.prefixInverseLeft p x =
      (actualAngularProduct e.prefixDescriptors id (prefixLeftWords p)
        e.ρ e.mass e.N e.sig e.C e.J e.i x).1 := funext (e.prefixInverseLeft_eq p x)
  have hrightEq : e.prefixInverseRight p x =
      (actualAngularProduct e.prefixDescriptors id (prefixRightWords p)
        e.ρ e.mass e.N e.sig e.C e.J e.i x).1 := funext (e.prefixInverseRight_eq p x)
  rw [hleftEq,hrightEq]
  exact ⟨hleft,hright⟩

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
