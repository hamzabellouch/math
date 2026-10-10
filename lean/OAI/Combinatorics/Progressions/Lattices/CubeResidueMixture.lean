import OAI.Combinatorics.Progressions.Probability.RawWeightCellMixture
import OAI.Combinatorics.Progressions.Probability.RefinedSliceLaws

namespace OAI

section

namespace Erdos3.FiniteCubeSlice

open scoped BigOperators Classical

theorem refineResidues_mixture {q : ℕ} (s : FiniteCubeSlice q)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i)
    (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (htotal : 0 < ∑ x : s.Domain, w (s.coordinates x))
    (S : Finset (s.ResidueLabel n))
    (hchild : ∀ r : S, 0 < ∑ x : (s.refineResidues n r.val).Domain,
      w ((s.refineResidues n r.val).coordinates x)) (f : (Option (Fin q) → ℤ) → ℂ) :
    let p := FiniteProbabilityWeights.ofPositiveWeights
      (fun x : s.Domain => w (s.coordinates x)) (fun x => hw (s.coordinates x)) htotal
    (∑ r : S, (p.mass (Finset.univ.filter (fun x => s.residueLabelMap n x = r.val)) : ℂ) *
      (FiniteProbabilityWeights.ofPositiveWeights
        (fun x : (s.refineResidues n r.val).Domain => w ((s.refineResidues n r.val).coordinates x))
        (fun x => hw ((s.refineResidues n r.val).coordinates x)) (hchild r)).complexMean
          (fun x => f ((s.refineResidues n r.val).coordinates x))) =
      p.complexMean (fun x => if s.residueLabelMap n x ∈ S then f (s.coordinates x) else 0) := by
  exact FiniteProbabilityWeights.embedded_cell_mixture
    (fun x : s.Domain => w (s.coordinates x)) (fun x => hw (s.coordinates x)) htotal
    (s.residueLabelMap n) S (fun r => (s.refineResidues n r.val).Domain)
    (fun r => s.refineResiduesEmbedding n hdvd r.val)
    (fun r => s.refineResiduesEmbedding_range n hdvd r.val) hchild (fun x => f (s.coordinates x))

noncomputable def retainedRefinementLaw {q : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i)
    (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z) {η : ℝ} (hη : 0 < η)
    (r : s.ResidueLabel n) (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.coordinates x)) η) :
    FiniteProbabilityWeights (s.refineResidues n r).Domain :=
  FiniteProbabilityWeights.ofPositiveWeights
    (fun x => w ((s.refineResidues n r).coordinates x))
    (fun x => hw ((s.refineResidues n r).coordinates x))
    (s.retained_refineResidues_total_pos n hdvd r w hη hr)

theorem retainedRefinementLaw_mixture_error {q : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i)
    (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (htotal : 0 < ∑ x : s.Domain, w (s.coordinates x))
    (hm : 0 < (FiniteProbabilityWeights.uniform s.Domain).mean (fun x => w (s.coordinates x)))
    {η : ℝ} (hη : 0 < η) (f : (Option (Fin q) → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    let S := Finset.univ \ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.coordinates x)) η
    let p := FiniteProbabilityWeights.ofPositiveWeights
      (fun x : s.Domain => w (s.coordinates x)) (fun x => hw (s.coordinates x)) htotal
    ‖p.complexMean (fun x => f (s.coordinates x)) -
      ∑ r : S, (p.mass (Finset.univ.filter (fun x => s.residueLabelMap n x = r.val)) : ℂ) *
        (s.retainedRefinementLaw n hdvd w hw hη r.val (Finset.mem_sdiff.mp r.property).2).complexMean
          (fun x => f ((s.refineResidues n r.val).coordinates x))‖ ≤
      η / (FiniteProbabilityWeights.uniform s.Domain).mean (fun x => w (s.coordinates x)) := by
  dsimp only
  exact FiniteProbabilityWeights.embedded_lowWeight_cell_mixture_error
    (fun x : s.Domain => w (s.coordinates x)) (fun x => hw (s.coordinates x)) htotal hm
    (s.residueLabelMap n) hη.le _ rfl (fun r => (s.refineResidues n r.val).Domain)
    (fun r => s.refineResiduesEmbedding n hdvd r.val)
    (fun r => s.refineResiduesEmbedding_range n hdvd r.val)
    (fun r => s.retained_refineResidues_total_pos n hdvd r.val w hη (Finset.mem_sdiff.mp r.property).2)
    (fun x => f (s.coordinates x)) (fun x => hf (s.coordinates x))

end Erdos3.FiniteCubeSlice

end

end OAI
