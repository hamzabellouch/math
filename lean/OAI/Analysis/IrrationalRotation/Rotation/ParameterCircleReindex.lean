import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleCocycle
import OAI.Analysis.IrrationalRotation.Rotation.CircleFlattenedCosts

namespace OAI

open Function

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coord_to_nat_bijective :
    Bijective (fun i : p.Coord => (i.2 : ℕ) - 1) := by
  have hpos (a : p.Coord) : 1 ≤ (a.2 : ℕ) := by
    have h := (p.mem_block_iff (a.1 + 1) a.2).mp a.2.property
    omega
  constructor
  · rintro ⟨j, i, hi⟩ ⟨k, l, hl⟩ h
    have hip := hpos ⟨j, i, hi⟩
    have hlp := hpos ⟨k, l, hl⟩
    change 1 ≤ i at hip
    change 1 ≤ l at hlp
    have hil : i = l := by change i - 1 = l - 1 at h; omega
    subst l
    have hjk := p.block_index_unique hp.m_pos hi hl
    have hjk' : j = k := by omega
    subst k
    rfl
  · intro n
    obtain ⟨j, hj, hn⟩ := p.exists_mem_block hp.m_pos (n + 1) (by omega)
    refine ⟨⟨j - 1, ⟨n + 1, ?_⟩⟩, by simp⟩
    simpa only [Nat.sub_add_cancel hj] using hn

theorem parameter_cocycle_eq_flattened (k : ℤ) (x : Circle) :
    p.floorCocycle θ k x =
      CircleWeights.cocycle θ p.flattenedFrequency p.flattenedCost k x := by
  let e : p.Coord ≃ ℕ := Equiv.ofBijective _ hp.coord_to_nat_bijective
  have hindex (i : p.Coord) : e i + 1 = (i.2 : ℕ) := by
    have hi := (p.mem_block_iff (i.1 + 1) i.2).mp i.2.property
    change (i.2 : ℕ) - 1 + 1 = (i.2 : ℕ)
    omega
  have hfreq (i : p.Coord) : p.flattenedFrequency (e i) = p.coordFrequency i := by
    simp only [CircleParameterData.flattenedFrequency, CircleParameterData.coordFrequency,
      hindex i]
  have hcost (i : p.Coord) : p.flattenedCost (e i) = p.coordCost i := by
    apply p.flattenedCost_eq_of_mem hp.m_pos
    simpa only [hindex i] using i.2.property
  unfold CircleParameterData.floorCocycle CircleWeights.cocycle CircleWeights.floorCost
  congr 2
  calc
    (∑' i : p.Coord, p.coordCost i *
        (Int.floor (CircleWeights.coordinate p.coordFrequency i x +
          (k : ℝ) * CircleWeights.phase θ p.coordFrequency i) : ℝ)) =
        ∑' i : p.Coord, p.flattenedCost (e i) *
          (Int.floor (CircleWeights.coordinate p.flattenedFrequency (e i) x +
            (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency (e i)) : ℝ) := by
      apply tsum_congr
      intro i
      simp only [hcost, CircleWeights.coordinate, CircleWeights.phase, hfreq]
    _ = ∑' n : ℕ, p.flattenedCost n *
        (Int.floor (CircleWeights.coordinate p.flattenedFrequency n x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency n) : ℝ) :=
      e.tsum_eq (fun n : ℕ => p.flattenedCost n *
        (Int.floor (CircleWeights.coordinate p.flattenedFrequency n x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency n) : ℝ))

theorem parameter_weight_eq_flattened :
    p.measurableWeight θ = CircleWeights.weight θ p.flattenedFrequency p.flattenedCost := by
  funext x
  exact hp.parameter_cocycle_eq_flattened 1 x

end Invariant233.CircleParameterLaws

end OAI
