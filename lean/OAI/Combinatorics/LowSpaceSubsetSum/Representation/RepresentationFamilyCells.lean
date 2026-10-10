import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFamilyPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplerBounds

namespace OAI

/-! # Stored integer parameters and live separator-family sampling

The five binomial computations and the power/log loops have constant-size
states. The four resulting counts remain live through the family draw.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationFamilyCells

open ComputedSeparatorFamilies
variable {n g : ℕ}

def execute (n : ℕ) (P : Parameters g) (s : Seed n P) :=
  SeparatorSamplerCells.run n g 4 P.sizes P.counts P.size_le s

theorem execute_value (n : ℕ) (P : Parameters g) (s : Seed n P) :
    (execute n P s).1 = ComputedSeparatorFamilies.execute n P s :=
  SeparatorSamplerCells.run_value n g 4 P.sizes P.counts P.size_le s

def draw (S : SeparatorExpectation.RoundedParameters g) (n : ℕ)
    (P : Parameters g) (h : P = source S) (s : (S.samplerCoupling n).Seed) :=
  execute n P (transport h s)

theorem draw_value (S : SeparatorExpectation.RoundedParameters g) (n : ℕ)
    (P : Parameters g) (h : P = source S) (s : (S.samplerCoupling n).Seed) :
    (draw S n P h s).1 = ComputedSeparatorFamilies.draw S n P h s := execute_value _ _ _

theorem draw_source (S : SeparatorExpectation.RoundedParameters g) (n : ℕ)
    (P : Parameters g) (h : P = source S) (s : (S.samplerCoupling n).Seed) :
    draw S n P h s = SeparatorSamplerBounds.application S n s := by
  subst P
  rfl

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (t : ((RepresentationFamilyPreparation.parameters I hn s).samplerCoupling n).Seed) :=
  let p := SeparatorParameterExecution.run (StoredTopCoordinates.width n)
    d.residues.primes.stored.stored.guesses[0]
  let out := draw (RepresentationFamilyPreparation.parameters I hn s) n
    (RepresentationFamilyPreparation.actualParameters I hn hlog s d h)
    (RepresentationFamilyPreparation.actualParameters_eq I hn hlog s d h) t
  ((out.1.1, p.2+out.1.2+1), out.2+64)

theorem value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (t : ((RepresentationFamilyPreparation.parameters I hn s).samplerCoupling n).Seed) :
    (run I hn hlog s d h t).1 = RepresentationFamilyPreparation.run I hn hlog s d h t := by
  have hv := draw_value (RepresentationFamilyPreparation.parameters I hn s) n
    (RepresentationFamilyPreparation.actualParameters I hn hlog s d h)
    (RepresentationFamilyPreparation.actualParameters_eq I hn hlog s d h) t
  exact congrArg (fun out =>
    (out.1, (SeparatorParameterExecution.run (StoredTopCoordinates.width n)
      d.residues.primes.stored.stored.guesses[0]).2+out.2+1)) hv

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (t : ((RepresentationFamilyPreparation.parameters I hn s).samplerCoupling n).Seed) :
    (run I hn hlog s d h t).2 ≤ inputScale I^7*(compressionDictionaryCapacity n+1) := by
  have hg : StoredTopCoordinates.width n ≤ n := by
    unfold StoredTopCoordinates.width RepresentationSetup.blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  have hC : 2 ^ StoredTopCoordinates.width n ≤ compressionDictionaryCapacity n := by
    exact (Nat.pow_le_pow_right (by decide) (show StoredTopCoordinates.width n ≤
      2*StoredTopCoordinates.width n by omega)).trans RepresentationSetup.separator_table_rate_le_capacity
  have hp := SeparatorSamplerBounds.application_cells I
    (RepresentationFamilyPreparation.parameters I hn s) hn hg _ hC t
  have he := draw_source (RepresentationFamilyPreparation.parameters I hn s) n
    (RepresentationFamilyPreparation.actualParameters I hn hlog s d h)
    (RepresentationFamilyPreparation.actualParameters_eq I hn hlog s d h) t
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have h64 : 64 ≤ inputScale I^6 := by
    have h1 : inputScale I ≤ inputScale I^6 := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 6)
    omega
  have hc : 2*inputScale I^6 ≤ inputScale I^7 := by
    calc
      _ ≤ inputScale I*inputScale I^6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hm := Nat.mul_le_mul_right (compressionDictionaryCapacity n+1) hc
  change _ + 64 ≤ _
  rw [congrArg Prod.snd he]
  nlinarith only [hp, h64, hm]

end LowSpaceSubsetSum.RepresentationFamilyCells

end

end OAI
