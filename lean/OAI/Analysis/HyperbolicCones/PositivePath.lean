import OAI.Analysis.HyperbolicCones.PencilTopology

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256

/-- A continuous symmetric matrix path with no singularities at positive times
cannot change from indefinite to positive definite. -/
theorem posSemidef_of_nonsingular_path {n : ℕ} (F : ℝ → Sym n)
    (hF : ContinuousOn F (Ici 0)) (hF0 : ContinuousAt F 0)
    (hunit : ∀ t : ℝ, 0 < t → IsUnit (F t : Mat n ℝ))
    (hpos : ∃ t : ℝ, 0 < t ∧ (F t : Mat n ℝ).PosDef) :
    (F 0 : Mat n ℝ).PosSemidef := by
  let : PreconnectedSpace (Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  have hc : Continuous (fun t : Ioi (0 : ℝ) => F t) :=
    continuousOn_iff_continuous_domRestrict.mp (hF.mono Ioi_subset_Ici_self)
  let S : Set (Ioi (0 : ℝ)) := {t | (F t : Mat n ℝ).PosSemidef}
  have hclosed : IsClosed S := (isClosed_posSemidef n).preimage hc
  have heq : S = {t : Ioi (0 : ℝ) | (F t : Mat n ℝ).PosDef} := by
    ext t
    constructor
    · intro ht
      exact ht.posDef_iff_isUnit.mpr (hunit t t.property)
    · exact fun ht => ht.posSemidef
  have hopen : IsOpen S := by
    rw [heq]
    exact (isOpen_posDef n).preimage hc
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, hFt⟩ := hpos
    exact ⟨⟨t, ht⟩, hFt.posSemidef⟩
  have hSuniv : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hSne
  have hall : ∀ t : ℝ, 0 < t → (F t : Mat n ℝ).PosSemidef := by
    intro t ht
    have hm : (⟨t, ht⟩ : Ioi (0 : ℝ)) ∈ S := by rw [hSuniv]; trivial
    exact hm
  apply posSemidef_of_tendsto (f := 𝓝[Ioi (0 : ℝ)] 0)
    (hF0.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hall t ht

end Paper256

end

end OAI
