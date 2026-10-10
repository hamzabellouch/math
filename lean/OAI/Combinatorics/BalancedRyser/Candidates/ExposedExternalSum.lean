import OAI.Combinatorics.BalancedRyser.Candidates.ExposedExternalFresh
import OAI.Combinatorics.BalancedRyser.Candidates.ExposedOppositeSum

namespace OAI

namespace Balanced.ExposedExternalSum

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable
open CandidateValidityWitness FreshWitnessProbability ExposedOppositeSum
open ExposedWitnessProbability ExposedExternalFresh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def externalEvent (T : FourTuple F) (S : Line F) (d e : Direction F)
    (i j : Fin 4) : Set (MergedPairs F) := {M | SuccessfulOn M T S ∧
  ∃ x, OnLine x S ∧ PairWitness M d x (tuplePoint M T i) ∧
    PairWitness M e x (tuplePoint M T j)}

def oldOldSum (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) : ℝ :=
  ∑ T ∈ freshTuples D, ∑ c : F, ∑ d ∈ D.erase g, ∑ e ∈ D.erase g,
    ∑ i : Fin 4, ∑ j : Fin 4,
      ((exposedLaw D a).toOuterMeasure (externalEvent T (g,c) d e i j)).toReal

theorem oldOldSum_le (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    oldOldSum g D a ≤ 8192 * (D.card : ℝ)^2 := by
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
    exact_mod_cast freshTuples_card_le D
  have hd : ((D.erase g).card : ℝ) ≤ D.card := by
    exact_mod_cast Finset.card_erase_le (s := D) (a := g)
  calc
    _ ≤ ∑ _T ∈ freshTuples D, ∑ _c : F, ∑ _d ∈ D.erase g, ∑ _e ∈ D.erase g,
        ∑ _i : Fin 4, ∑ _j : Fin 4, 2 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hinj, hfresh⟩ := (Finset.mem_filter.mp hT).2
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro d hdD
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact successful_external_probability_le D a T hinj hfresh (g,c) d
        (Finset.mem_erase.mp hdD).2 (Finset.mem_erase.mp hdD).1 i
        (fun M x => PairWitness M e x (tuplePoint M T j))
    _ = ((freshTuples D).card : ℝ) * Fintype.card F *
        ((D.erase g).card : ℝ)^2 * (32 * (Fintype.card F : ℝ)⁻¹ ^ 5) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * Fintype.card F *
        (D.card : ℝ)^2 * (32 * (Fintype.card F : ℝ)⁻¹ ^ 5) := by gcongr
    _ = _ := by field_simp; ring

def freshDirections (D : Finset (Direction F)) (T : FourTuple F) : Finset (Direction F) :=
  Finset.univ.filter (fun e => e ∉ D ∧ e ∉ generatorSet T)

theorem freshDirections_card_le (D : Finset (Direction F)) (T : FourTuple F) :
    (freshDirections D T).card ≤ 2 * Fintype.card F := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hc := Finset.card_le_univ (freshDirections D T)
  simp only [Direction, Fintype.card_option] at hc
  omega

def oldFreshSum (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) : ℝ :=
  ∑ T ∈ freshTuples D, ∑ c : F, ∑ d ∈ D.erase g, ∑ e ∈ freshDirections D T,
    ∑ i : Fin 4, ∑ j : Fin 4,
      ((exposedLaw D a).toOuterMeasure (externalEvent T (g,c) d e i j)).toReal

theorem oldFreshSum_le_div (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) :
    oldFreshSum g D a ≤ 32768 * (D.card : ℝ) / Fintype.card F := by
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
    exact_mod_cast freshTuples_card_le D
  have hd : ((D.erase g).card : ℝ) ≤ D.card := by
    exact_mod_cast Finset.card_erase_le (s := D) (a := g)
  calc
    _ ≤ ∑ T ∈ freshTuples D, ∑ _c : F, ∑ _d ∈ D.erase g,
        ∑ _e ∈ freshDirections D T, ∑ _i : Fin 4, ∑ _j : Fin 4,
          4 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hinj, hfresh⟩ := (Finset.mem_filter.mp hT).2
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro d hdD
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨heD, heT⟩ := (Finset.mem_filter.mp he).2
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact successful_external_fresh_probability_le D a T hinj hfresh (g,c) d
        (Finset.mem_erase.mp hdD).2 (Finset.mem_erase.mp hdD).1 e heD heT i j
    _ = ∑ T ∈ freshTuples D, (Fintype.card F : ℝ) *
        ((D.erase g).card : ℝ) * ((freshDirections D T).card : ℝ) *
        (64 * (Fintype.card F : ℝ)⁻¹ ^ 7) := by
      apply Finset.sum_congr rfl
      intro T _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring
    _ ≤ ∑ _T ∈ freshTuples D, (Fintype.card F : ℝ) *
        (D.card : ℝ) * (2 * Fintype.card F) *
        (64 * (Fintype.card F : ℝ)⁻¹ ^ 7) := by
      apply Finset.sum_le_sum
      intro T _
      have he : ((freshDirections D T).card : ℝ) ≤ 2 * Fintype.card F := by
        exact_mod_cast freshDirections_card_le D T
      gcongr
    _ = ((freshTuples D).card : ℝ) * ((Fintype.card F : ℝ) *
        (D.card : ℝ) * (2 * Fintype.card F) *
        (64 * (Fintype.card F : ℝ)⁻¹ ^ 7)) := by simp
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * ((Fintype.card F : ℝ) *
        (D.card : ℝ) * (2 * Fintype.card F) *
        (64 * (Fintype.card F : ℝ)⁻¹ ^ 7)) := by gcongr
    _ = _ := by field_simp; ring

theorem oldFreshSum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : oldFreshSum g D a ≤ 32768 * (D.card : ℝ) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  exact (oldFreshSum_le_div g D a).trans (div_le_self (by positivity) hq)

theorem old_external_total_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    oldOldSum g D a + oldFreshSum g D a ≤
      8192 * (m : ℝ)^2 + 32768 * m := by
  have hm : (D.card : ℝ) ≤ m := by exact_mod_cast hD
  apply (add_le_add (oldOldSum_le g D a) (oldFreshSum_le g D a)).trans
  gcongr

end
end Balanced.ExposedExternalSum

end OAI
