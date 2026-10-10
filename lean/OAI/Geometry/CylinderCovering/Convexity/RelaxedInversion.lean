import OAI.Geometry.CylinderCovering.Convexity.ThresholdInversion

namespace OAI

open Set
open scoped NNReal

namespace CylinderCovering.ThresholdInversion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem existsUnique_inverse_on_convex {S : Set E} (hS : IsComplete S)
    (hconv : Convex ℝ S) {g : E → E} {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1)
    (hlip : ∀ p ∈ S, ∀ q ∈ S, ‖g p - g q‖ ≤ c * ‖p - q‖)
    (hreverse : MapsTo (fun p => p - g p) S S)
    {y : E} (hy : y ∈ S) : ∃! p : E, p ∈ S ∧ p + g p = y := by
  let f : E → E := fun p => (1 / 2 : ℝ) • (y + (p - g p))
  let k : ℝ≥0 := ⟨(1 + c) / 2, by positivity⟩
  have hmap : MapsTo f S S := by
    intro p hp
    have h := hconv hy (hreverse hp) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simpa only [f, smul_add] using h
  have hcontract : ContractingWith k (hmap.restrict f S S) := by
    refine ⟨by change (1 + c) / 2 < 1; linarith, LipschitzWith.of_dist_le_mul ?_⟩
    intro p q
    change dist (f p) (f q) ≤ ((1 + c) / 2) * dist (p : E) (q : E)
    rw [dist_eq_norm, dist_eq_norm]
    have heq : f p - f q = (1 / 2 : ℝ) • ((p - q) - (g p - g q)) := by
      dsimp [f]
      rw [← smul_sub]
      congr 1
      abel
    rw [heq, norm_smul, Real.norm_eq_abs]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have htri := norm_sub_le ((p : E) - q) (g p - g q)
    have h := hlip p p.property q q.property
    nlinarith
  obtain ⟨p, hp, hfix, _⟩ :=
    ContractingWith.exists_fixedPoint' hS hmap hcontract hy (edist_ne_top _ _)
  have hpeq : p + g p = y := by
    have heq : y + (p - g p) = p + p := by
      calc
        y + (p - g p) = (2 : ℝ) • f p := by simp [f, smul_smul]
        _ = (2 : ℝ) • p := congrArg (fun z => (2 : ℝ) • z) hfix
        _ = p + p := two_smul ℝ p
    have heq' := congrArg (fun z => z - p + g p) heq
    convert heq'.symm using 1 <;> abel
  refine ⟨p, ⟨hp, hpeq⟩, ?_⟩
  intro q hq
  exact inverse_unique hc hq.2 hpeq (hlip p hp q hq.1)

end CylinderCovering.ThresholdInversion

end OAI
