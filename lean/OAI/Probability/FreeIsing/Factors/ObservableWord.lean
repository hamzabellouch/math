import OAI.Probability.FreeIsing.Estimates.CenteredWordAction
import OAI.Probability.FreeIsing.Factors.Observable

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FactorObservable

variable {d : ℕ}
variable {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}

lemma wordOperator_spinLp_root (hPhi : Measurable Phi)
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (v : TreeVertex d) :
    RadialWalk.wordOperator TreeKoopman.generatorOperator v
      (spinLp hPhi (ConnectedHull.root d)) = spinLp hPhi v :=
  TreeKoopman.wordOperator_toLp_root (field Phi) (equivariant_field heq)
    (fun v => memLp_field hPhi v 2) v

lemma wordOperator_centeredSpinLp_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (v : TreeVertex d) :
    RadialWalk.wordOperator TreeKoopman.centeredGenerator v
      (centeredSpinLp hPhi hlaw (ConnectedHull.root d)) = centeredSpinLp hPhi hlaw v := by
  apply Subtype.ext
  rw [TreeKoopman.centered_wordOperator_apply_coe]
  exact wordOperator_spinLp_root hPhi heq v

lemma inner_centeredWordOperator_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    inner ℝ (centeredSpinLp hPhi hlaw (ConnectedHull.root d))
      (RadialWalk.wordOperator TreeKoopman.centeredGenerator v
        (centeredSpinLp hPhi hlaw (ConnectedHull.root d))) = theta ^ v.1.length := by
  rw [wordOperator_centeredSpinLp_root hPhi hlaw heq]
  exact inner_centeredSpinLp_root hPhi hlaw hlo hhi v

end Problem367.FactorObservable

namespace Problem367

theorem IsFactorOfIID.exists_centered_word_observable {d : ℕ} {theta : ℝ}
    (hfactor : IsFactorOfIID d theta) (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    ∃ f : centeredL2 (labelMeasure d), ‖f‖ = 1 ∧
      ∀ v : TreeVertex d,
        inner ℝ f (RadialWalk.wordOperator TreeKoopman.centeredGenerator v f) =
          theta ^ v.1.length := by
  obtain ⟨Phi, hPhi, hlaw, heq⟩ := hfactor
  refine ⟨FactorObservable.centeredSpinLp hPhi hlaw (ConnectedHull.root d),
    FactorObservable.norm_centeredSpinLp hPhi hlaw _, ?_⟩
  intro v
  exact FactorObservable.inner_centeredWordOperator_root hPhi hlaw heq hlo hhi v

end Problem367

end

end OAI
