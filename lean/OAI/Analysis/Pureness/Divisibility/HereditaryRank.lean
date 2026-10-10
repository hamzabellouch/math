import OAI.Analysis.Pureness.Divisibility.HereditaryApproximateUnit

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_mul_contraction_le (τ : TracialState A) (e c : A)
    (he : 0 ≤ e) (hc : c ≤ 1) : τ.functional (e * c) ≤ τ.functional e := by
  have heq : τ.functional (e * c) =
      τ.functional (CFC.sqrt e * c * CFC.sqrt e) := by
    calc
      _ = τ.functional ((CFC.sqrt e * CFC.sqrt e) * c) := by
        rw [CFC.sqrt_mul_sqrt_self e he]
      _ = τ.functional ((CFC.sqrt e * c) * CFC.sqrt e) := by
        rw [mul_assoc, τ.tracial (CFC.sqrt e) (CFC.sqrt e * c)]
  rw [heq]
  apply τ.functional.monotone
  simpa only [(CFC.sqrt_nonneg e).star_eq, mul_one, CFC.sqrt_mul_sqrt_self e he] using
    star_left_conjugate_le_conjugate hc (CFC.sqrt e)

lemma trace_le_rank_of_mem_hereditary (τ : TracialState A) (h c : A)
    (hh : 0 ≤ h) (hc : c ∈ hereditaryCarrier h) (hc1 : c ≤ 1) :
    ENNReal.ofReal (τ.functional c).re ≤ normalizedRootRank τ h := by
  have ht : Tendsto (fun j => ENNReal.ofReal (τ.functional (normalizedRoot h j * c)).re)
      atTop (𝓝 (ENNReal.ofReal (τ.functional c).re)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp
        ((map_continuous τ.functional).continuousAt.tendsto.comp
          (normalizedRoot_mul_hereditary_tendsto h hh c hc)))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  calc
    _ ≤ ENNReal.ofReal (τ.functional (normalizedRoot h j)).re :=
      ENNReal.ofReal_le_ofReal (Complex.le_def.mp
        (trace_mul_contraction_le τ _ c (normalizedRoot_nonneg h j) hc1)).1
    _ ≤ normalizedRootRank τ h :=
      le_iSup (fun j => ENNReal.ofReal (τ.functional (normalizedRoot h j)).re) j

theorem hereditary_rank_domination (τ : TracialState A) (h c : A)
    (hh : 0 ≤ h) (hc : 0 ≤ c) (hcmem : c ∈ hereditaryCarrier h) :
    normalizedRootRank τ c ≤ normalizedRootRank τ h := by
  apply iSup_le
  intro j
  exact trace_le_rank_of_mem_hereditary τ h (normalizedRoot c j) hh
    (normalizedRoot_mem_hereditary hh hcmem hc j) (normalizedRoot_le_one c hc j)

theorem exists_rank_dominated_trace_transfer (hsimple : TopologicallySimple A)
    (h p : A) (hh : 0 ≤ h) (hne : h ≠ 0) (hp : 0 ≤ p) :
    ∃ c : A, 0 ≤ c ∧ c ∈ hereditaryCarrier h ∧
      (∀ τ : TracialState A, τ.functional c = τ.functional p) ∧
      (∀ τ : TracialState A, normalizedRootRank τ c ≤ normalizedRootRank τ h) := by
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hne
  let c := traceTransfer Finset.univ (CFC.sqrt h) p s
  have hc : 0 ≤ c := traceTransfer_nonneg _ _ _ _ (CFC.sqrt_nonneg h).star_eq hp
  have hcm : c ∈ hereditaryCarrier h := by
    dsimp [c]
    rw [traceTransfer_eq_sandwich]
    exact sqrt_sandwich_mem_hereditary h _ hh
  refine ⟨c, hc, hcm, ?_, fun τ => hereditary_rank_domination τ h c hh hc hcm⟩
  intro τ
  apply trace_transfer_identity τ.functional.toLinearMap.toAddMonoidHom τ.tracial
  simpa only [CFC.sqrt_mul_sqrt_self h hh] using hs
end CuntzPureness

end OAI
