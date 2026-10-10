import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss

namespace OAI

/-! # A canonical representative above each cold color -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotCanonical

variable {I : Type*} [Countable I]

def familyReplacement (F : ℝ × JetPrototype.Phase → ℝ)
    (c : I → ℝ × JetPrototype.Phase → ℝ) : ℝ × JetPrototype.Phase → ℝ :=
  replacement F (fun u => ∑' i, c i u)

theorem family_properties {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} {R : ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hcs : ∀ u, Summable (fun i => c i u)) (hcF : ∀ u, (∑' i, c i u) ≤ F u)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p)))) :
    Measurable (familyReplacement F c) ∧
      (∀ u, 0 ≤ familyReplacement F c u ∧ familyReplacement F c u ≤ R) ∧
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ familyReplacement F c u) ∧
      (∀ u, familyReplacement F c u-∑' i, c i u ≤
        PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p))) ∧
      familyReplacement F c =ᵐ[WeightedLocal.spacetimeVolume] F := by
  have hC (u) : 0 ≤ (∑' i, c i u) ∧ (∑' i, c i u) ≤ F u :=
    ⟨tsum_nonneg (fun i => hcn i u),hcF u⟩
  have hb := replacement_bounds hC
  refine ⟨measurable_replacement hFm (Measurable.tsum hcm) hnorm,?_,?_,?_,
    replacement_ae hFm (Measurable.tsum hcm) hF hC hnorm⟩
  · intro u
    exact ⟨(hC u).1.trans (hb u).1,(hb u).2.1.trans (hF u)⟩
  · intro s u
    exact (Summable.sum_le_tsum s (fun i _ => hcn i u) (hcs u)).trans (hb u).1
  · exact fun u => (hb u).2.2

end BoltzmannNonuniqueness.HotCanonical

end

end OAI
