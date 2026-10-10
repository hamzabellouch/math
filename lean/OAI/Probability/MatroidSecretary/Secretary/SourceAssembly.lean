import OAI.Probability.MatroidSecretary.Secretary.Assembly
import OAI.Probability.MatroidSecretary.Secretary.Seed
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The actual hidden-vector performance theorem supplies the secretary bound.
The finite coupling laws below are internal inputs; the final endpoint discharges
them with the concrete source-prefix/table construction. -/

open MeasureTheory ProbabilityTheory

namespace MatroidProphet.SecretaryReplay

theorem reconstructed_source_guarantee.{u} {n : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed (mainSeedBits n))
    (νQ : Measure Q)
    (hproductLaw : (νQ.prod (Secretary.uniformArrivalLaw n)).map
      (fun z => decode z.1 (orderPrefix z.2 (K z.1).val)) = sourceSeedLaw n)
    (hproductMask : ∀ᵐ z ∂νQ.prod (Secretary.uniformArrivalLaw n),
      (completeHiddenRule M hE).mask (decode z.1 (orderPrefix z.2 (K z.1).val)) =
        orderPrefix z.2 (K z.1).val) :
    SecretaryGuarantee.{u} M (reconstructedRule (completeHiddenRule M hE) K decode)
      νQ (((2 : ℝ) ^ 293)⁻¹) := by
  intro w hw Ω mΩ μ hμ q σ π hq hσ hπ hqlaw hσlaw hind hprefix
  obtain ⟨hi, hl⟩ := reconstructed_product_lower (completeHiddenRule M hE) K decode
    νQ (Secretary.uniformArrivalLaw n) (sourceSeedLaw n) hproductLaw hproductMask
    w μ q σ π hq hσ hπ hqlaw hσlaw hind hprefix
  exact ⟨hi, (complete_hidden_guarantee M hE w hw).trans hl⟩

/-- A concrete finite coupling completes the entire existential for one matroid,
including pointwise feasibility even at null seeds and the full adversary clause. -/
theorem reconstructed_source_witness.{u} {n : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed (mainSeedBits n))
    (νQ : Measure Q) [IsProbabilityMeasure νQ]
    (hproductLaw : (νQ.prod (Secretary.uniformArrivalLaw n)).map
      (fun z => decode z.1 (orderPrefix z.2 (K z.1).val)) = sourceSeedLaw n)
    (hproductMask : ∀ᵐ z ∂νQ.prod (Secretary.uniformArrivalLaw n),
      (completeHiddenRule M hE).mask (decode z.1 (orderPrefix z.2 (K z.1).val)) =
        orderPrefix z.2 (K z.1).val) :
    ∃ (q : ℕ) (ν : Measure (Fin q)), IsProbabilityMeasure ν ∧
      ∃ (A : SecretaryRule n (Fin q)), SecretaryFeasible M A ∧
        SecretaryGuarantee.{u} M A ν (((2 : ℝ) ^ 293)⁻¹) := by
  exact secretaryFinSeed_witness (reconstructedRule (completeHiddenRule M hE) K decode)
    M νQ (((2 : ℝ) ^ 293)⁻¹)
    (reconstructed_feasible M (completeHiddenRule M hE) K decode
      (completeHiddenRule_feasible M hE))
    (reconstructed_source_guarantee M hE K decode νQ hproductLaw hproductMask)

end MatroidProphet.SecretaryReplay

end OAI
