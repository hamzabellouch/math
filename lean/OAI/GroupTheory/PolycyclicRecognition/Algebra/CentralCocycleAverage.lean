import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianReducedCohomology
import Mathlib.GroupTheory.Subgroup.Center

namespace OAI

/-! # Central averaging of a cocycle

The orthogonal complement of the central fixed subspace has no central
invariants. Averaging over the center makes a cocycle uniformly small on
compact sets in that summand, without requiring the whole group to commute.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E]

omit [CompleteSpace E] in
theorem IsCocycle.finite_central_average {b : G → E} (hb : IsCocycle b)
    (A : FiniteOrbitAverage (Subgroup.center G)) (g : G) :
    A.onVector ((isometricLinearAction (G := G) (E := E)).comp (Subgroup.center G).subtype) (b g) =
      b g + g • (∑ i, A.weight i • b (A.element i)) - ∑ i, A.weight i • b (A.element i) := by
  have he (h : Subgroup.center G) : (h : G) • b g = b g + g • b h - b h := by
    calc
      (h : G) • b g = b ((h : G) * g) - b h := by rw [hb]; abel
      _ = b g + g • b h - b h := by
        rw [← Subgroup.mem_center_iff.mp h.property g, hb g h]
  change (∑ i, A.weight i • ((A.element i : G) • b g)) = _
  simp_rw [he, smul_sub, smul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, A.mass, one_smul]
  rw [Finset.smul_sum]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => (smul_comm g (A.weight i) (b (A.element i))).symm)

variable [TopologicalSpace G]

theorem exists_small_correction_of_no_central_invariants
    (hcenter : ∀ v : E, (∀ z : Subgroup.center G, (z : G) • v = v) → v = 0)
    (b : G → E) (hbcont : Continuous b) (hb : IsCocycle b)
    (Q : Set G) (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : E, ∀ q ∈ Q, ‖b q + q • φ - φ‖ ≤ ε := by
  let ρ := (isometricLinearAction (G := G) (E := E)).comp (Subgroup.center G).subtype
  have hfix : ∀ v : E, (∀ z, ρ z v = v) → v = 0 := hcenter
  obtain ⟨A, hA⟩ := exists_unitaryAverage_small_compact ρ hfix (b '' Q) (hQ.image hbcont) hε
  refine ⟨∑ i, A.weight i • b (A.element i), fun q hq => ?_⟩
  rw [← hb.finite_central_average A q]
  exact (hA (b q) ⟨q, hq, rfl⟩).le

end PolycyclicRecognition

end

end OAI
