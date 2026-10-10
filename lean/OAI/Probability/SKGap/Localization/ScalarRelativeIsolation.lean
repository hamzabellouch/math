import Mathlib
import OAI.Probability.SKGap.Localization.CompactTube
import OAI.Probability.SKGap.Localization.ScalarClosedIsolation

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

def scalarRelativeForbidden {R t0 T : ℝ} (U : Set (ScalarTimeDomain R t0 T)) : Set ScalarPoint :=
  (fun p : ScalarPoint => (p.1,p.2.1)) ⁻¹'
    ((fun x : ScalarTimeDomain R t0 T => ((x.1 : ProbabilityMeasure ℝ),(x.2 : ℝ))) '' Uᶜ)

lemma isClosed_scalarRelativeForbidden {R t0 T : ℝ} {U : Set (ScalarTimeDomain R t0 T)}
    (hU : IsOpen U) : IsClosed (scalarRelativeForbidden U) := by
  let : CompactSpace (momentBall R) := isCompact_iff_compactSpace.mp (isCompact_momentBall R)
  let : CompactSpace (Icc t0 T) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hc : IsCompact ((fun x : ScalarTimeDomain R t0 T =>
      ((x.1 : ProbabilityMeasure ℝ),(x.2 : ℝ))) '' Uᶜ) :=
    hU.isClosed_compl.isCompact.image (by fun_prop)
  exact hc.isClosed.preimage (by fun_prop)

lemma scalarRelativeForbidden_curve {j R t0 T : ℝ} {U : Set (ScalarTimeDomain R t0 T)}
    (hK : scalarEqualitySet j R t0 T ⊆ U) {p : ScalarPoint}
    (hp : p ∈ scalarRelativeForbidden U) : p.1 ≠ scalarCurve j p.2.1 := by
  intro he
  obtain ⟨x,hx,hxe⟩ := hp
  have hP := congrArg Prod.fst hxe
  have ht := congrArg Prod.snd hxe
  dsimp only at hP ht
  have hxK : x ∈ scalarEqualitySet j R t0 T := by
    change (x.1 : ProbabilityMeasure ℝ)=scalarCurve j (x.2:ℝ)
    rw [hP,ht,he]
  exact hx (hK hxK)

theorem scalar_relative_neighborhood_rate {j R t0 T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (ht0 : 0 < t0) (hT : t0 ≤ T) {U : Set (ScalarTimeDomain R t0 T)}
    (hU : IsOpen U) (hK : scalarEqualitySet j R t0 T ⊆ U) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ t ∈ Icc t0 T, ∀ σ ∈ Icc 0 (min δ 1),
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y ∈ momentBall R) →
      (∀ y ∈ E, ∀ x ∈ U, @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y ≠ (x.1:ProbabilityMeasure ℝ) ∨ t ≠ (x.2:ℝ)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨a,ha,δ,hδ,N,hbound⟩ := scalar_closed_isolation hj hj1 (ht0.le.trans hT) ht0
    (isClosed_scalarRelativeForbidden hU) (fun p hp _ _ => scalarRelativeForbidden_curve hK hp)
  refine ⟨a,ha,δ,hδ,N,?_⟩
  intro n hn hn' t ht σ hσ E hE hmom hnot
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  apply hbound n hn hn' t ⟨ht0.le.trans ht.1,ht.2⟩ σ hσ E hE
  · intro y hy
    let x : ScalarTimeDomain R t0 T := (⟨empiricalLaw y,hmom y hy⟩,⟨t,ht⟩)
    refine ⟨x,?_,rfl⟩
    intro hx
    rcases hnot y hy x hx with hh | hh <;> exact hh rfl
  · intro y _
    have hq := (scalarQMoment_bounds (empiricalLaw y)).1
    change t0 ≤ t+σ^2+j*scalarQMoment (empiricalLaw y)
    linarith [ht.1,sq_nonneg σ,mul_nonneg hj.le hq]
end SKGap
end
end

end OAI
