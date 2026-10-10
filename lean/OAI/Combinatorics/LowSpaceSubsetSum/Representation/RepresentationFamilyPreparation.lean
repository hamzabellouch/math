import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPreparedFields
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.ComputedSeparatorFamilies

namespace OAI

/-! # Separator-family generation at the stored guessed cardinality -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationFamilyPreparation

variable {n : ℕ}

abbrev width (n : ℕ) := StoredTopCoordinates.width n

def parameters (I : Instance n) (hn : 10000 ≤ n)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :=
  RepresentationFromFamilies.parameters (canonicalRepresentationData I) hn
    (((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).ideal s)

theorem guess_ideal (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    d.residues.primes.stored.stored.guesses[0] =
      ((((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).ideal s).1.1.1.1.2 0).val := by
  let R := (canonicalRepresentationData I).zeroSetup
  obtain ⟨_, _, hr, _⟩ := RepresentationExtraPreparation.source I hn hlog s d h
  obtain ⟨_, _, hp, _⟩ := RepresentationResiduePreparation.source I hn hlog s.1 d.residues hr
  obtain ⟨_, _, hs, _, _⟩ := RepresentationPrimePreparation.source I hn hlog s.1.1 d.residues.primes hp
  obtain ⟨part, ht, _, _, hg, _, _, _⟩ :=
    RepresentationStoredPreparation.source I s.1.1.1 d.residues.primes.stored hs hn hlog
  have hi := R.partitionHistoryExecution.ideal_eq_of_some s.1.1.1 part
    ((R.partitionHistoryExecution.value_eq s.1.1.1).trans ht)
  rw [← hi] at hg
  exact hg 0

theorem size_source (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) (i : Fin 4) :
    (SeparatorParameterExecution.run (width n) d.residues.primes.stored.stored.guesses[0]).1.size =
      (parameters I hn s).e i := by
  rw [guess_ideal I hn hlog s d h]
  rw [SeparatorParameterExecution.size_value]
  rfl

theorem guess_upper (guesses : RepresentationSetup.Guesses n) : (guesses 0).val ≤ width n := by
  have h := (Finset.mem_Icc.mp (guesses 0).property).2
  change (guesses 0).val ≤ mixerSize n / 4 at h
  simp only [width, StoredTopCoordinates.width, RepresentationSetup.blockHalf, mixerSize,
    Matrix.cons_val_zero] at *
  omega

theorem guess_lower (guesses : RepresentationSetup.Guesses n) : 2 * width n ≤ 3 * (guesses 0).val := by
  have h := (Finset.mem_Icc.mp (guesses 0).property).1
  change (mixerSize n + 5) / 6 ≤ (guesses 0).val at h
  simp only [width, StoredTopCoordinates.width, RepresentationSetup.blockHalf, mixerSize,
    Matrix.cons_val_zero] at *
  omega

theorem counts_source (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) (i : Fin 4) :
    (SeparatorParameterExecution.run (width n) d.residues.primes.stored.stored.guesses[0]).1.counts[i.val] =
      (parameters I hn s).counts i := by
  rw [guess_ideal I hn hlog s d h]
  exact SeparatorParameterExecution.rounded_counts (width n) _
    (by simp only [width, StoredTopCoordinates.width, RepresentationSetup.blockHalf,
      Matrix.cons_val_zero]; omega)
    (by simp only [width, StoredTopCoordinates.width]; exact dvd_mul_right 2 _)
    (guess_upper _) (guess_lower _) i

def actualParameters (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    ComputedSeparatorFamilies.Parameters (width n) :=
  ComputedSeparatorFamilies.ofData
    (SeparatorParameterExecution.run (width n) d.residues.primes.stored.stored.guesses[0]).1 (by
      rw [size_source I hn hlog s d h 0]
      exact (parameters I hn s).size_le 0)

theorem actualParameters_eq (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    actualParameters I hn hlog s d h = ComputedSeparatorFamilies.source (parameters I hn s) :=
  ComputedSeparatorFamilies.ofData_eq _ _ _
    (size_source I hn hlog s d h) (counts_source I hn hlog s d h)

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (t : ((parameters I hn s).samplerCoupling n).Seed) :
    Option (Fin 4 → Array (Fin (2 ^ width n))) × ℕ :=
  let prepared := SeparatorParameterExecution.run (width n) d.residues.primes.stored.stored.guesses[0]
  let out := ComputedSeparatorFamilies.draw (parameters I hn s) n
    (ComputedSeparatorFamilies.ofData prepared.1 (by
      rw [size_source I hn hlog s d h 0]
      exact (parameters I hn s).size_le 0)) (actualParameters_eq I hn hlog s d h) t
  (out.1, prepared.2 + out.2 + 1)

theorem value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (t : ((parameters I hn s).samplerCoupling n).Seed) :
    (run I hn hlog s d h t).1 = (SeparatorFamilyExecution.Application.run (parameters I hn s) n t).1 := by
  change (ComputedSeparatorFamilies.draw _ n _ _ t).1 = _
  exact congrArg Prod.fst (ComputedSeparatorFamilies.draw_pair _ _ _ _ t)

theorem work (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (t : ((parameters I hn s).samplerCoupling n).Seed) :
    (run I hn hlog s d h t).2 ≤ 60 * width n + 51 +
      44 * 2 ^ width n * (width n * n ^ 3 + 32 * (width n + 1) ^ 3 + 4) + 22 := by
  have hp := SeparatorParameterExecution.work (width n) d.residues.primes.stored.stored.guesses[0]
  have hf := SeparatorFamilyExecution.Application.work (parameters I hn s) n t
  change (SeparatorFamilyExecution.Application.run (parameters I hn s) n t).2 ≤
    44 * 2 ^ width n * (width n * n ^ 3 + 32 * (width n + 1) ^ 3 + 4) + 21 at hf
  have he := congrArg Prod.snd (ComputedSeparatorFamilies.draw_pair (parameters I hn s) n
    (actualParameters I hn hlog s d h) (actualParameters_eq I hn hlog s d h) t)
  dsimp only [actualParameters] at he
  change _ + _ + 1 ≤ _
  rw [he]
  omega

end LowSpaceSubsetSum.RepresentationFamilyPreparation

end

end OAI
