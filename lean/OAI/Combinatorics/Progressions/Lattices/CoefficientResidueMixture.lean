import OAI.Combinatorics.Progressions.Probability.RawWeightCellMixture
import OAI.Combinatorics.Progressions.Probability.RefinedSliceLaws

namespace OAI

section

namespace Erdos3.FiniteCoefficientSlice

open scoped BigOperators Classical

theorem refineResidues_mixture (s : FiniteCoefficientSlice)
    (n : ℕ) (hdvd : s.modulus ∣ n) (w : ℤ → ℝ) (hw : ∀ z, 0 ≤ w z)
    (htotal : 0 < ∑ x : s.Domain, w (s.value x))
    (S : Finset (s.ResidueLabel n))
    (hchild : ∀ r : S, 0 < ∑ x : (s.refineResidues n r.val).Domain,
      w ((s.refineResidues n r.val).value x)) (f : ℤ → ℂ) :
    let p := FiniteProbabilityWeights.ofPositiveWeights
      (fun x : s.Domain => w (s.value x)) (fun x => hw (s.value x)) htotal
    (∑ r : S, (p.mass (Finset.univ.filter (fun x => s.residueLabelMap n x = r.val)) : ℂ) *
      (FiniteProbabilityWeights.ofPositiveWeights
        (fun x : (s.refineResidues n r.val).Domain => w ((s.refineResidues n r.val).value x))
        (fun x => hw ((s.refineResidues n r.val).value x)) (hchild r)).complexMean
          (fun x => f ((s.refineResidues n r.val).value x))) =
      p.complexMean (fun x => if s.residueLabelMap n x ∈ S then f (s.value x) else 0) := by
  exact FiniteProbabilityWeights.embedded_cell_mixture
    (fun x : s.Domain => w (s.value x)) (fun x => hw (s.value x)) htotal
    (s.residueLabelMap n) S (fun r => (s.refineResidues n r.val).Domain)
    (fun r => s.refineResiduesEmbedding n hdvd r.val)
    (fun r => s.refineResiduesEmbedding_range n hdvd r.val) hchild (fun x => f (s.value x))

noncomputable def retainedRefinementLaw (s : FiniteCoefficientSlice) [Nonempty s.Domain]
    (n : ℕ) (hdvd : s.modulus ∣ n) (w : ℤ → ℝ) (hw : ∀ z, 0 ≤ w z) {η : ℝ} (hη : 0 < η)
    (r : s.ResidueLabel n) (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.value x)) η) :
    FiniteProbabilityWeights (s.refineResidues n r).Domain :=
  FiniteProbabilityWeights.ofPositiveWeights
    (fun x => w ((s.refineResidues n r).value x))
    (fun x => hw ((s.refineResidues n r).value x))
    (s.retained_refineResidues_total_pos n hdvd r w hη hr)

theorem retainedRefinementLaw_mixture_error (s : FiniteCoefficientSlice) [Nonempty s.Domain]
    (n : ℕ) (hdvd : s.modulus ∣ n) (w : ℤ → ℝ) (hw : ∀ z, 0 ≤ w z)
    (htotal : 0 < ∑ x : s.Domain, w (s.value x))
    (hm : 0 < (FiniteProbabilityWeights.uniform s.Domain).mean (fun x => w (s.value x)))
    {η : ℝ} (hη : 0 < η) (f : ℤ → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    let S := Finset.univ \ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.value x)) η
    let p := FiniteProbabilityWeights.ofPositiveWeights
      (fun x : s.Domain => w (s.value x)) (fun x => hw (s.value x)) htotal
    ‖p.complexMean (fun x => f (s.value x)) -
      ∑ r : S, (p.mass (Finset.univ.filter (fun x => s.residueLabelMap n x = r.val)) : ℂ) *
        (s.retainedRefinementLaw n hdvd w hw hη r.val (Finset.mem_sdiff.mp r.property).2).complexMean
          (fun x => f ((s.refineResidues n r.val).value x))‖ ≤
      η / (FiniteProbabilityWeights.uniform s.Domain).mean (fun x => w (s.value x)) := by
  dsimp only
  exact FiniteProbabilityWeights.embedded_lowWeight_cell_mixture_error
    (fun x : s.Domain => w (s.value x)) (fun x => hw (s.value x)) htotal hm
    (s.residueLabelMap n) hη.le _ rfl (fun r => (s.refineResidues n r.val).Domain)
    (fun r => s.refineResiduesEmbedding n hdvd r.val)
    (fun r => s.refineResiduesEmbedding_range n hdvd r.val)
    (fun r => s.retained_refineResidues_total_pos n hdvd r.val w hη (Finset.mem_sdiff.mp r.property).2)
    (fun x => f (s.value x)) (fun x => hf (s.value x))

end Erdos3.FiniteCoefficientSlice

end

end OAI
