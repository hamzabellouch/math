import OAI.Analysis.BoundedHochschild.NormalMultiplication

namespace OAI

/-!
# Suprema of chains of central projections

A nonempty chain of central projections has a central projection supremum.
A bounded weak-star cluster point is a projection because multiplication by
each member of the chain eventually stabilizes. The same limiting argument
preserves annihilation of any fixed element. No trace is used.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A chain of central projections has a least projection upper bound, preserving
any common right annihilator. -/
theorem exists_central_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) ∧
      ∃ U : Ultrafilter S, (U : Filter S) ≤ atTop ∧
        PredualTendsto e (fun q : S => (q : M)) (U : Filter S) p := by
  classical
  let : Nonempty S := hne.to_subtype
  let : IsDirectedOrder S := ⟨fun a b => by
    rcases hchain.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter S := Ultrafilter.of atTop
  have hU : (U : Filter S) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨p, _hpnorm, ht⟩ := exists_predual_ultralimit e U
    (fun q : S => (q : M)) 1 (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ hr => congrArg (fun a : M => e.symm a z) hr.symm)
  have hpcentral (a : M) : p * a = a * p := by
    have hl := HochschildSakai.predual_tendsto_mul_left e a ht
    have hr := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => a * (q : M)) = (fun q : S => (q : M) * a) := by
      funext q
      exact (hcentral q q.property a).symm
    rw [heq] at hl
    exact predual_tendsto_unique e hr hl
  have hp : IsStarProjection p := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e p ht
      have heq : (fun q : S => (q : M) * p) = (fun q : S => (q : M)) :=
        funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun q : S => star (q : M)) = (fun q : S => (q : M)) := by
        funext q
        exact (hproj q q.property).isSelfAdjoint.star_eq
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨p, hp, hpcentral, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hub
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hub q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) := by
      funext q
      exact ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))

/-- A chain of central projections has a least projection upper bound, preserving
any common right annihilator. -/
theorem exists_central_projection_chain_supremum
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) := by
  obtain ⟨p, hp, hc, hu, hl, ha, _⟩ :=
    exists_central_projection_chain_supremum_with_limit e S hne hchain hproj hcentral
  exact ⟨p, hp, hc, hu, hl, ha⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
