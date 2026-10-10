import OAI.Analysis.KadisonKastler.TracialCoreCenter
import OAI.Analysis.KadisonKastler.TraceRepresentationNormal
import OAI.Analysis.KadisonKastler.NormalCoreIsomorphism
import OAI.Analysis.KadisonKastler.FactorIsomorphism

namespace OAI

/-! # Every faithful-state core of a finite diffuse factor is nonfactorial -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem regularCore_not_factor_of_II1 (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (Ω : H) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  let hf := traceHilbert_factor hM
  let hu := traceHilbert_nonzero hM
  let K := TraceFreeHilbert hf hM.diffuse hM.finite hu
  let N := traceFreeHilbertClosure hf hM.diffuse hM.finite hu
  let τ := traceFreeHilbertClosureTrace hf hM.diffuse hM.finite hu
  let e := traceFreeHilbertEquiv hf hM.diffuse hM.finite hu
  let : Nontrivial K := nontrivial_of_ne τ.vector 0 (by
    intro he
    have hh := τ.norm_vector
    rw [he, norm_zero] at hh
    exact zero_ne_one hh)
  let : TopologicalSpace.SeparableSpace K := concreteTraceHilbert_separable hM
  have hc : DenseRange (algebraVectorMap N τ.vector) :=
    traceFreeHilbertClosureTrace_cyclic hf hM.diffuse hM.finite hu
  have hs : Function.Injective (algebraVectorMap N τ.vector) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply τ.separating
    change a.val τ.vector - b.val τ.vector = 0
    exact sub_eq_zero.mpr hab
  obtain ⟨J, _⟩ := exists_hilbert_conjugation (H := K)
  have ht : ∀ a b : Algebra N, inner ℂ τ.vector ((a.val * b.val) τ.vector) =
      inner ℂ τ.vector ((b.val * a.val) τ.vector) := τ.cyclic
  let m := tracialModularSpectralResolution J τ.vector hs hc ht
  have hnN : ∀ t a, a ∈ N → unitaryConj (m.group t) a ∈ N := by
    intro t a ha
    change unitaryConj (m.group t) a ∈ (N : Set (K →L[ℂ] K))
    rw [← m.normalizes t]
    exact Set.mem_image_of_mem _ ha
  obtain ⟨E⟩ := modularCore_equiv_of_normal e (traceFreeHilbertEquiv_boundedWeakNormal hM)
    Ω τ.vector hcyc hc hsep hs U hU hn hm m.group m.continuous hnN m.isModular
  intro hfactor
  exact regularCore_not_factor_of_tracial_vector τ.vector hs hc ht
    m.group m.continuous hnN m.isModular (hfactor.of_starAlgEquiv E)

end

end KadisonKastler

end OAI
