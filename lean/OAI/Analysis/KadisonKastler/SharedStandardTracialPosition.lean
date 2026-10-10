import OAI.Analysis.KadisonKastler.SharedTracialRightAction
import OAI.Analysis.KadisonKastler.PreparedPairCyclicity

namespace OAI

/-! # Constructing the neighboring standard trace from common module actions -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_neighbor_standardTracialPosition
    {M N R : VonNeumannAlgebra H} (p : StandardTracialPosition M)
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (hirr : ∀ T ∈ N, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (hirrRight : ∀ T ∈ N.commutant,
      (∀ r ∈ conjugateRightAlgebra p.conjugation p.conjugation_involutive R,
        r * T = T * r) → ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) :
    ∃ q : StandardTracialPosition N, q.vector = p.vector := by
  let S := conjugateRightAlgebra p.conjugation p.conjugation_involutive R
  have hn : p.vector ≠ 0 := by
    intro h
    have he := p.vector_norm
    rw [h, norm_zero] at he
    exact zero_ne_one he
  have hc (r : H →L[ℂ] H) (hr : r ∈ R.toStarSubalgebra) :
      r p.vector = conjugationOperator p.conjugation (star r) p.vector := by
    change r p.vector = p.conjugation (star r (p.conjugation p.vector))
    rw [p.conjugation_vector]
    have he := p.conjugation_algebraVector (star (⟨r, hRM hr⟩ : Algebra M))
    change p.conjugation (star r p.vector) = star (star r) p.vector at he
    simpa only [star_star] using he.symm
  obtain ⟨hcyclic, _, _, _⟩ := preparedPair_cyclic_separating_of_conjugate_algebra
    N R.toStarSubalgebra S.toStarSubalgebra hRN hright p.conjugation
    (conjugateRightAlgebra_coe p.conjugation p.conjugation_involutive R)
    p.vector hn hirr hirrRight hc
  have hi (a : Algebra N) (ha : a.val ∈ R.commutant) : ∃ c : ℂ, a = c • 1 := by
    obtain ⟨c, hc⟩ := hirr a.val a.property
      (fun r hr => VonNeumannAlgebra.mem_commutant_iff.mp ha r hr)
    exact ⟨c, Subtype.ext hc⟩
  refine ⟨{ trace := concreteFactorTrace hN
            vector := p.vector
            trace_eq := fun x => (p.neighbor_trace hRM hRN hN hi hright x).symm
            cyclic := hcyclic }, rfl⟩

end

end KadisonKastler

end OAI
