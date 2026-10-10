import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceInitialSums

namespace OAI

namespace Balanced.CandidateIncidenceSums

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev TargetPrescription (F : Type*) := Σ g : Direction F, RootPrescription g

def rootCodes (D : Finset (Direction F)) (j : ℕ) : Finset (TargetPrescription F) :=
  Finset.univ.filter (fun r => (exposedTupleIndices r.2.tuple D).card = j)

def rootCode (r : TargetPrescription F) : IncidenceCode F :=
  ((r.2.tuple.generator,r.2.tuple.side),r.1)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem rootCode_injective : Function.Injective (rootCode (F := F)) := by
  rintro ⟨g,a⟩ ⟨h,b⟩ hab
  have ht : g = h := congrArg Prod.snd hab
  cases ht
  apply congrArg (Sigma.mk g)
  apply Prod.ext
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrFun (congrArg (fun z : IncidenceCode F => z.1.1) hab) i
  · exact congrArg (fun z : IncidenceCode F => z.1.2) hab

omit [Field F] in
theorem rootCode_mem {D : Finset (Direction F)} {j : ℕ}
    {r : TargetPrescription F} (hr : r ∈ rootCodes D j) :
    rootCode r ∈ admissibleCodes D j := by
  have hc := (Finset.mem_filter.mp hr).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩,
    r.2.injective, fun i => (r.2.1 i).2⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
    Finset.mem_univ _⟩
  exact hc

omit [Field F] in
theorem rootCode_surjective_on {D : Finset (Direction F)} {j : ℕ}
    {z : IncidenceCode F} (hz : z ∈ admissibleCodes D j) :
    ∃ r ∈ rootCodes D j, rootCode r = z := by
  have hz' := mem_admissibleCodes hz
  let a : RootPrescription z.2 :=
    (⟨fun i => ⟨z.1.1 i,hz'.2.1 i⟩,
      fun i k h => hz'.1 (congrArg Subtype.val h)⟩,z.1.2)
  refine ⟨⟨z.2,a⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · exact hz'.2.2
  · rfl

def rootIncidenceSum (D : Finset (Direction F)) (a : MergedPairs F) (j : ℕ)
    (P : Direction F → (Fin 4 → Point F) → Prop) : ℝ :=
  ∑ r ∈ rootCodes D j, probability D a
    {M | SuccessfulPositions (tuplePoint M r.2.tuple) r.1 ∧
      P r.1 (tuplePoint M r.2.tuple)}

theorem rootIncidenceSum_eq_incidenceSum (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    rootIncidenceSum D a j P = incidenceSum D a j P := by
  unfold rootIncidenceSum incidenceSum
  apply Finset.sum_bij (fun r _ => rootCode r)
  · intro r hr
    exact rootCode_mem hr
  · intro r hr s hs h
    exact rootCode_injective h
  · intro z hz
    obtain ⟨r,hr,heq⟩ := rootCode_surjective_on hz
    exact ⟨r,hr,heq⟩
  · intro r hr
    rfl

theorem rootIncidenceSum_eq_iterated (D : Finset (Direction F))
    (a : MergedPairs F) (j : ℕ) (P : Direction F → (Fin 4 → Point F) → Prop) :
    rootIncidenceSum D a j P = ∑ g : Direction F, ∑ r : RootPrescription g,
      if (exposedTupleIndices r.tuple D).card = j then probability D a
        {M | SuccessfulPositions (tuplePoint M r.tuple) g ∧
          P g (tuplePoint M r.tuple)} else 0 := by
  unfold rootIncidenceSum rootCodes
  rw [Finset.sum_filter, Fintype.sum_sigma]

theorem root_point_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) : rootIncidenceSum D a 0 (designatesPoint y) ≤ 2048 := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact point_sum_zero_le D a y

theorem root_point_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) : rootIncidenceSum D a 1 (designatesPoint y) ≤ 1024 * (D.card : ℝ) := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact point_sum_one_le D a y

theorem root_point_line_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    rootIncidenceSum D a 0 (throughPointHitsLine y K) ≤ 2048 := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact point_line_sum_zero_le D a y K hyK

theorem root_point_line_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (y : Point F) (K : Line F) :
    rootIncidenceSum D a 1 (throughPointHitsLine y K) ≤ 1024 * (D.card : ℝ) := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact point_line_sum_one_le D a y K

theorem root_two_lines_sum_zero_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (hLK : L ≠ K) :
    rootIncidenceSum D a 0 (hitsTwoLines L K) ≤ 6144 := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact two_lines_sum_zero_le D a L K hLK

theorem root_two_lines_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (L K : Line F) (havoid : ∀ d ∈ D, ∀ b, constituent a d b ≠ L) :
    rootIncidenceSum D a 1 (hitsTwoLines L K) ≤ 4096 * (D.card : ℝ) := by
  rw [rootIncidenceSum_eq_incidenceSum]
  exact two_lines_sum_one_le D a L K havoid

end
end Balanced.CandidateIncidenceSums

end OAI
