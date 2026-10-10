import OAI.GroupTheory.PolycyclicRecognition.Analysis.UnitaryCompactAverage
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ReducedCohomologyInput

namespace OAI

/-! # Reduced first cohomology for abelian unitary actions

For commuting group elements, a convex average of translated cocycle values
is exactly a coboundary correction. The simultaneous unitary averaging lemma
makes this correction uniformly small on each compact set.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {G E : Type*} [CommGroup G] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  [DistribMulAction G E] [IsIsometricSMul G E] [SMulCommClass G ℝ E]

omit [CompleteSpace E] in
theorem IsCocycle.finite_average_commutative {b : G → E} (hb : IsCocycle b)
    (A : FiniteOrbitAverage G) (g : G) :
    A.onVector (isometricLinearAction (G := G) (E := E)) (b g) =
      b g + g • (∑ i, A.weight i • b (A.element i)) - ∑ i, A.weight i • b (A.element i) := by
  have he (h : G) : h • b g = b g + g • b h - b h := by
    calc
      h • b g = b (h * g) - b h := by rw [hb h g]; abel
      _ = b g + g • b h - b h := by rw [mul_comm h g, hb g h]
  change (∑ i, A.weight i • (A.element i • b g)) = _
  simp_rw [he, smul_sub, smul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, A.mass, one_smul]
  rw [Finset.smul_sum]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => (smul_comm g (A.weight i) (b (A.element i))).symm)

variable [TopologicalSpace G]

theorem reducedCohomologyInput_of_commutative : ReducedCohomologyInput G E := by
  intro hfixed _hact b hbcont hb Q hQ ε hε
  let ρ := isometricLinearAction (G := G) (E := E)
  have hfix : ∀ x : E, (∀ g, ρ g x = x) → x = 0 := hfixed
  obtain ⟨A, hA⟩ := exists_unitaryAverage_small_compact ρ hfix (b '' Q) (hQ.image hbcont) hε
  refine ⟨∑ i, A.weight i • b (A.element i), fun q hq => ?_⟩
  rw [← hb.finite_average_commutative A q]
  exact (hA (b q) ⟨q, hq, rfl⟩).le

end PolycyclicRecognition

end

end OAI
