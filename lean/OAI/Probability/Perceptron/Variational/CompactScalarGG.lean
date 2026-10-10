import Mathlib
import OAI.Probability.Perceptron.Variational.CompactGGDensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def compactScalarMonomial (p : ℕ) : CompactOverlap →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x : CompactOverlap => (x:ℝ)^p,by fun_prop⟩

@[simp] lemma compactScalarMonomial_apply (p : ℕ) (x : CompactOverlap) :
    compactScalarMonomial p x = (x:ℝ)^p := rfl

lemma compactScalarMonomial_add (p q : ℕ) :
    compactScalarMonomial (p+q)=compactScalarMonomial p*compactScalarMonomial q := by
  ext x
  simp only [compactScalarMonomial_apply,BoundedContinuousFunction.mul_apply,pow_add]

lemma compactScalar_monomials_total (L : (CompactOverlap →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ p, L (compactScalarMonomial p)=0) : L=0 := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact CompactOverlap ℝ ℝ
  let L' := L.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let m (a : ℕ) : C(CompactOverlap,ℝ) := (compactScalarMonomial a).toContinuousMap
  have hm0 : m 0=1 := by ext x; simp [m,compactScalarMonomial_apply]
  have hmadd (a b : ℕ) : m (a+b)=m a*m b := by
    ext x
    exact congrArg (fun f : CompactOverlap →ᵇ ℝ => f x) (compactScalarMonomial_add _ _)
  let M : Submonoid C(CompactOverlap,ℝ) :=
    { carrier := Set.range m
      one_mem' := ⟨0,hm0⟩
      mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,hmadd a b⟩ }
  let A := Algebra.adjoin ℝ (M : Set C(CompactOverlap,ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have hpd : compactScalarMonomial 1 x ≠ compactScalarMonomial 1 y := by
      simpa only [compactScalarMonomial_apply,pow_one] using (Subtype.val_injective.ne hxy)
    have hmem : m 1 ∈ A :=
      Algebra.subset_adjoin (show m 1 ∈ M from ⟨1,rfl⟩)
    exact ⟨m 1,⟨m 1,hmem,rfl⟩,hpd⟩
  have hA : (A : Set C(CompactOverlap,ℝ)) ⊆ (L'.ker : Set C(CompactOverlap,ℝ)) := by
    have hspan : Submodule.span ℝ (M : Set C(CompactOverlap,ℝ)) ≤ L'.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨p,rfl⟩
      change L (e ((compactScalarMonomial p).toContinuousMap)) = 0
      have he : e ((compactScalarMonomial p).toContinuousMap) = compactScalarMonomial p := by
        ext x; rfl
      rw [he]
      exact hL p
    intro f hf
    apply hspan
    change f ∈ A.toSubmodule at hf
    simpa only [A,Algebra.adjoin_eq_span,Submonoid.closure_eq] using hf
  have hclosed := L'.isClosed_ker
  have hc := closure_minimal hA hclosed
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hall (f : C(CompactOverlap,ℝ)) : L' f=0 := by
    apply hc
    change f ∈ A.topologicalClosure
    rw [htop]
    trivial
  ext g
  have h := hall (e.symm g)
  simpa [L'] using h

lemma compactGG_of_scalar_monomials (μ : ProbabilityMeasure (CompactArray CompactOverlap))
    (n : ℕ) (i : Fin n) (f : CompactBlock CompactOverlap n →ᵇ ℝ)
    (h : ∀ p, compactGGDefect μ n i f (compactScalarMonomial p)=0)
    (g : CompactOverlap →ᵇ ℝ) : compactGGDefect μ n i f g=0 := by
  have hz := compactScalar_monomials_total (compactGGTestCLM μ n i f)
    (fun p => (compactGGTestCLM_apply μ n i f _).trans (h p))
  rw [← compactGGTestCLM_apply,hz]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
