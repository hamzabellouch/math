import OAI.Combinatorics.ProgressionColoring.OuterColoring
import OAI.Combinatorics.ProgressionColoring.FiniteLocalLemma

namespace OAI

universe uOmega uI uLabel

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem outer_exists_avoiding_from_incidence
    {Ω : Type uOmega} {I : Type uI} {Label : Type uLabel} [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]
    [DecidableEq Label]
    (P : FiniteLocalLemma.Probability Ω) (bad : I → Finset Ω)
    (support : I → Finset Label)
    (hsize : ∀ i, (100 : ℝ) ≤ (support i).card)
    (htail : ∀ i, P.mass (bad i) ≤ 2 * Real.exp (-((support i).card : ℝ) / 8))
    (hindependent : ∀ i T, i ∉ T → Disjoint T (outerNeighbors support i) →
      P.mass (bad i ∩ FiniteLocalLemma.avoid bad T) =
        P.mass (bad i) * P.mass (FiniteLocalLemma.avoid bad T))
    (hincident : ∀ b,
      ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j),
        Real.exp (-((support j).card : ℝ) / 32) ≤ 1 / 500) :
    ∃ ω, ∀ i, ω ∉ bad i := by
  classical
  let z : I → ℝ := fun i => Real.exp (-((support i).card : ℝ) / 32)
  have hzpos : ∀ i, 0 < z i := fun _ => Real.exp_pos _
  have hzhalf : ∀ i, z i < 1 / 2 := fun i => outer_weight_lt_half (hsize i)
  apply FiniteLocalLemma.exists_avoiding P bad (outerNeighbors support) z hzpos
    (fun i => lt_trans (hzhalf i) (by norm_num)) hindependent
  intro i
  have hsum : ∑ j ∈ outerNeighbors support i, z j ≤ (support i).card / 500 := by
    have h := outer_neighbor_weight_bound support z (fun j => (hzpos j).le)
      (1 / 500) hincident i
    simpa only [div_eq_mul_inv, one_mul] using h
  exact (htail i).trans
    (outer_local_criterion (outerNeighbors support i) z ((support i).card : ℝ)
      (hsize i) (fun j _ => (hzpos j).le) (fun j _ => (hzhalf j).le) hsum)

end QuantitativeVanDerWaerden

end OAI
