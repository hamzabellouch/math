import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness
import OAI.Combinatorics.BalancedRyser.Candidates.FreshExternalWitness

namespace OAI

namespace Balanced.FreshExternalWitness

noncomputable section
open scoped Classical BigOperators
open FreshTupleWitness TupleAlignment CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def freshPairs (D : Finset (Direction F)) (T : FourTuple F) :
    Finset (Direction F × Direction F) :=
  Finset.univ.filter (fun de => de.1 ≠ de.2 ∧ de.1 ∉ D ∧ de.2 ∉ D ∧
    (∀ k, T.generator k ≠ de.1) ∧ (∀ k, T.generator k ≠ de.2))

omit [Field F] in
@[simp] theorem mem_freshPairs (D : Finset (Direction F)) (T : FourTuple F)
    (de : Direction F × Direction F) :
    de ∈ freshPairs D T ↔ de.1 ≠ de.2 ∧ de.1 ∉ D ∧ de.2 ∉ D ∧
      (∀ k, T.generator k ≠ de.1) ∧ (∀ k, T.generator k ≠ de.2) := by
  simp only [freshPairs, Finset.mem_filter, Finset.mem_univ, true_and]

def probabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (i j : Fin 4) : ℝ :=
  ∑ r : RootPrescription g, ∑ de ∈ freshPairs D r.tuple,
    ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
      conditionalProbability D a {M | orientedEvent g r.tuple de.1 de.2 i j σ τ z M}

theorem orientedEvent_conditional_probability_eq
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (T : FourTuple F) (de : Direction F × Direction F)
    (hde : de ∈ freshPairs D T) (i j : Fin 4) (σ τ : Bool) (z : F) :
    conditionalProbability D a {M | orientedEvent g T de.1 de.2 i j σ τ z M} =
      fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by
  obtain ⟨hne, hdD, heD, hd, he⟩ := (mem_freshPairs D T de).mp hde
  have h := orientedEvent_probability_eq (fixedValues D a) g T de.1 de.2 hne hd he
    (fixed_coordinates_update_invariant (fun d => d ∈ D) a de.1 hdD)
    (fixed_coordinates_update_invariant (fun d => d ∈ D) a de.2 heD) i j σ τ z
  calc
    _ = ((PMF.uniformOfFintype {M : MergedPairs F // fixedValues D a M}).toOuterMeasure
        {M | M.1 ∈ {N | orientedEvent g T de.1 de.2 i j σ τ z N}}).toReal :=
      (fixedFiber_probability_eq D a _).symm
    _ = _ := by
      convert h using 1
      exact FiniteUniformFibers.probability_fintype_congr _ _ rfl

theorem tuple_probabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (T : FourTuple F) (i j : Fin 4) :
    (∑ de ∈ freshPairs D T, ∑ σ : Bool, ∑ τ : Bool, ∑ z : F,
      conditionalProbability D a {M | orientedEvent g T de.1 de.2 i j σ τ z M}) ≤
      (16 / Fintype.card F : ℝ) * fiberSuccessProbability (fixedValues D a) g T := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hUcard : ((freshPairs D T).card : ℝ) ≤ ((Fintype.card F : ℝ) + 1)^2 := by
    have h := Finset.card_le_univ (freshPairs D T)
    simp only [Fintype.card_prod, Direction, Fintype.card_option] at h
    rw [pow_two]
    exact_mod_cast h
  have hUm : ((freshPairs D T).card : ℝ) ≤ 4 * (Fintype.card F : ℝ)^2 := by
    nlinarith [sq_nonneg ((Fintype.card F : ℝ) - 1)]
  have hp : 0 ≤ fiberSuccessProbability (fixedValues D a) g T := ENNReal.toReal_nonneg
  calc
    _ = ∑ _de ∈ freshPairs D T, ∑ _σ : Bool, ∑ _τ : Bool, ∑ _z : F,
        fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by
      apply Finset.sum_congr rfl
      intro de hde
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro z _
      exact orientedEvent_conditional_probability_eq g D a T de hde i j σ τ z
    _ = 4 * ((freshPairs D T).card : ℝ) * Fintype.card F *
        fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
      ring
    _ ≤ 4 * (4 * (Fintype.card F : ℝ)^2) * Fintype.card F *
        fiberSuccessProbability (fixedValues D a) g T / (Fintype.card F : ℝ)^4 := by gcongr
    _ = _ := by field_simp; ring

theorem probabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) (i j : Fin 4) :
    probabilitySum g D a i j ≤ (327680 * (m + 1)^4 : ℝ) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ ∑ r : RootPrescription g,
        (16 / Fintype.card F : ℝ) *
          fiberSuccessProbability (fixedValues D a) g r.tuple := by
      apply Finset.sum_le_sum
      intro r _
      exact tuple_probabilitySum_le g D a r.tuple i j
    _ = (16 / Fintype.card F : ℝ) * successProbabilitySum g D a := by
      rw [← Finset.mul_sum, sum_fiberSuccessProbability_eq]
    _ ≤ (16 / Fintype.card F : ℝ) *
        ((20480 * (m + 1)^4 : ℝ) * Fintype.card F) := by
      apply mul_le_mul_of_nonneg_left (successProbabilitySum_le g D a m hD)
      positivity
    _ = _ := by field_simp; ring

theorem all_positions_probabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ i : Fin 4, ∑ j : Fin 4, probabilitySum g D a i j) ≤
      (5242880 * (m + 1)^4 : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, (327680 * (m + 1)^4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact probabilitySum_le g D a m hD i j
    _ = _ := by simp; ring

theorem source_witness_has_orientedEvent
    (g : Direction F) (c : F) (T : FourTuple F) (M : MergedPairs F)
    (hs : CandidateValidityWitness.SuccessfulOn M T (g,c))
    (D : Finset (Direction F)) (x : Point F)
    (hx : OnLine x (g,c)) (hex : x ∉ designated M ⟨(g,c), T⟩)
    (i j : Fin 4) (hij : i ≠ j) (d e : Direction F)
    (hd : d ≠ g) (hdD : d ∉ D) (heD : e ∉ D)
    (hdi : CandidateValidityWitness.PairWitness M d x (tuplePoint M T i))
    (hej : CandidateValidityWitness.PairWitness M e x (tuplePoint M T j)) :
    ∃ de ∈ freshPairs D T, ∃ σ τ z, orientedEvent g T de.1 de.2 i j σ τ z M := by
  have hde := CandidateValidityWitness.external_witness_directions_distinct
    hs hx hex hij hd hdi hej
  have hdused := CandidateValidityWitness.external_witness_not_generator hs hx hex hdi
  have heused := CandidateValidityWitness.external_witness_not_generator hs hx hex hej
  have hdf : ∀ k, T.generator k ≠ d := by
    intro k hk
    exact hdused (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  have hef : ∀ k, T.generator k ≠ e := by
    intro k hk
    exact heused (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  have hc : lineEval g (tuplePoint M T 0) = c := hs.2.2.2 0
  have hx' : OnLine x (g, lineEval g (tuplePoint M T 0)) := by
    simpa only [hc] using hx
  obtain ⟨z, hz⟩ := exists_targetPoint g T M x hx'
  obtain ⟨σ, hσ⟩ := hdi
  obtain ⟨τ, hτ⟩ := hej
  refine ⟨(d,e), (mem_freshPairs D T (d,e)).mpr ⟨hde, hdD, heD, hdf, hef⟩,
    σ, τ, z, ?_⟩
  change (((∃ c, ∀ k, OnLine (tuplePoint M T k) (g,c)) ∧
      Function.Injective (tuplePoint M T)) ∧
    (OnLine (targetPoint g T z M) (constituent M d σ) ∧
      OnLine (tuplePoint M T i) (constituent M d (!σ)))) ∧
    (OnLine (targetPoint g T z M) (constituent M e τ) ∧
      OnLine (tuplePoint M T j) (constituent M e (!τ)))
  rw [hz]
  exact ⟨⟨⟨⟨c, hs.2.2.2⟩, hs.2.2.1⟩, hσ⟩, hτ⟩

end
end Balanced.FreshExternalWitness

end OAI
