import OAI.Analysis.KadisonKastler.CyclicAbelianExpectation
import OAI.Analysis.KadisonKastler.FaithfulCyclicConstruction
import OAI.Analysis.KadisonKastler.PublishedCenterInjectivity
import OAI.Analysis.KadisonKastler.InjectivityTransport

namespace OAI

/-! # Injectivity of separably acting commutative algebras

Compress the countable amplification to the faithful cyclic space,
apply the abelian unitary average, then use the inverse star isomorphism.
This is the center-injectivity specialization used by the separable
reduction in the universal stability theorem.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [SeparableSpace H]

omit [Nontrivial H] in
theorem faithfulCyclicHom_eq_compression (M : VonNeumannAlgebra H) (a : Algebra M) :
    faithfulCyclicHom M a =
      cornerCompression (faithfulCyclicSpace M) (l2Diagonal a.val) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  rw [faithfulCyclicHom_apply]
  exact (cornerCompression_coe_of_invariant (faithfulCyclicSpace M) (l2Diagonal a.val)
    (fun _ hy => Generator.vectorOrbitClosure_invariant _ _
      ((countableDiagonalHom M).rangeRestrict a) hy) x).symm

theorem isInjective_of_commutative_separable (M : VonNeumannAlgebra H)
    (hcomm : ∀ a b : Algebra M, a * b = b * a) : IsInjective M := by
  let K := faithfulCyclicSpace M
  let A := faithfulCyclicAlgebra M
  let e : Algebra M ≃⋆ₐ[ℂ] Algebra A := faithfulCyclicEquiv M
  have hcommA (a b : Algebra A) : a * b = b * a := by
    apply e.symm.injective
    let e' : Algebra A →⋆ₐ[ℂ] Algebra M := e.symm.toStarAlgHom
    change e' (a * b) = e' (b * a)
    calc
      e' (a * b) = e' a * e' b := map_mul e' a b
      _ = e' b * e' a := hcomm _ _
      _ = e' (b * a) := (map_mul e' b a).symm
  obtain ⟨E, hE, hEA, hfix⟩ := isInjective_of_commutative_cyclic A
    (faithfulCyclicVector M) hcommA (by
      apply (faithfulCyclicHom_cyclic M).mono
      rintro _ ⟨a, rfl⟩
      exact ⟨⟨faithfulCyclicHom M a, subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩⟩, rfl⟩)
  let R : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K) :=
    (cornerCompression K).comp (l2DiagonalHom (E := H)).toAlgHom.toLinearMap
  apply isInjective_of_contracting_extension M A e R
    (fun T => (norm_cornerCompression_le K _).trans (norm_l2Diagonal_le T))
    (fun a => (faithfulCyclicHom_eq_compression M a).symm)
  exact ⟨E, hE, hEA, hfix⟩

end

section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]

/-- Blackadar's center-injectivity input, specialized to the separable
representations in which the center-alignment reduction uses it. -/
theorem publishedCenterInjectivity_separable : PublishedCenterInjectivity (H := H) := by
  intro M
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    refine ⟨ContinuousLinearMap.id ℂ (H →L[ℂ] H), ?_, ?_, ?_⟩
    · exact ContinuousLinearMap.norm_id_le
    · intro T
      have : T = 0 := Subsingleton.elim _ _
      simpa only [ContinuousLinearMap.id_apply, this] using (zero_mem (concreteCenter M))
    · intro T _
      rfl
  · let := hH
    apply isInjective_of_commutative_separable
    intro a b
    apply Subtype.ext
    exact (VonNeumannAlgebra.mem_commutant_iff.mp a.property.2 b.val b.property.1).symm

end

end KadisonKastler

end OAI
