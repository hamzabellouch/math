import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerProductCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScalarDraws

namespace OAI

/-! # Actual bounded scalar draws with live candidate storage

Each factor uses the explicit finite candidate vector and scalar trial
division cursor. Products retain their earlier scalar values and reserve
unread random-word tails on failure. The final arrays contain three words.
-/

noncomputable section
namespace LowSpaceSubsetSum.ScalarSamplerCells

def primeFactor {ell : ℕ} (h : 4 ≤ ell) (n : ℕ)
    (s : (primeCoupling h n).Seed) : SamplerExecution.Trace ↥(factorRange ell) × ℕ :=
  let r := SamplerVectorCells.primeSeed h n s
  (⟨r.1.value.map (factorPrimeEquiv h), r.1.reads, r.1.tests⟩, r.2+8)

theorem primeFactor_value {ell : ℕ} (h : 4 ≤ ell) (n : ℕ)
    (s : (primeCoupling h n).Seed) :
    (primeFactor h n s).1 =
      (SamplerExecution.map (SamplerExecution.prime h n) (factorPrimeEquiv h)).run s := by
  simp only [primeFactor, SamplerVectorCells.primeSeed_value, SamplerExecution.map]

theorem primeFactor_cells {ell : ℕ} (h : 4 ≤ ell) (n : ℕ)
    (s : (primeCoupling h n).Seed) : (primeFactor h n s).2 ≤ 3*n^3+88 := by
  have hp := SamplerVectorCells.primeSeed_cells h n s
  change _+8 ≤ _
  omega

def factor (n ell : ℕ) : (factorCoupling n ell).Seed →
    SamplerExecution.Trace ↥(factorRange ell) × ℕ :=
  if h : ell < 4 then
    SamplerFinCells.cast (S := (SamplerCoupling.pure ()).map (factorOneEquiv h))
      (by simp only [factorCoupling, dite_eq_left h])
      (fun _ => (⟨some (factorOneEquiv h ()), 0, 0⟩, 8))
  else SamplerFinCells.cast
    (S := (primeCoupling (show 4 ≤ ell by omega) n).map (factorPrimeEquiv (show 4 ≤ ell by omega)))
    (by simp only [factorCoupling, dite_eq_right h]) (primeFactor (ell := ell) (by omega) n)

theorem factor_value (n ell : ℕ) (s : (factorCoupling n ell).Seed) :
    (factor n ell s).1 = (SamplerExecution.factor n ell).run s := by
  by_cases h : ell < 4
  · simp only [factor, SamplerExecution.factor, dite_eq_left h]
    exact SamplerFinCells.cast_value _ _
      (SamplerExecution.map (SamplerExecution.pure ()) (factorOneEquiv h)) (fun _ => rfl) s
  · simp only [factor, SamplerExecution.factor, dite_eq_right h]
    exact SamplerFinCells.cast_value _ _
      (SamplerExecution.map (SamplerExecution.prime (by omega) n) (factorPrimeEquiv (by omega)))
      (primeFactor_value (ell := ell) (by omega) n) s

theorem factor_cells (n ell : ℕ) (s : (factorCoupling n ell).Seed) :
    (factor n ell s).2 ≤ 3*n^3+88 := by
  by_cases h : ell < 4
  · simp only [factor, dite_eq_left h]
    apply SamplerFinCells.cast_cells
    intro t
    dsimp only
    omega
  · simp only [factor, dite_eq_right h]
    exact SamplerFinCells.cast_cells _ _ _ (primeFactor_cells (ell := ell) (by omega) n) s

def pairFactors (n a b : ℕ)
    (s : ((factorCoupling n a).prod (factorCoupling n b)).Seed) :=
  SamplerProductCells.run (factor n a) (factor n b) (3*n^3+88) s

theorem pairFactors_value (n a b : ℕ)
    (s : ((factorCoupling n a).prod (factorCoupling n b)).Seed) :
    (pairFactors n a b s).1 =
      (SamplerExecution.prod (SamplerExecution.factor n a) (SamplerExecution.factor n b)).run s :=
  SamplerProductCells.value _ _ _ _ _ (factor_value n a) (factor_value n b) s

theorem pairFactors_cells (n a b : ℕ)
    (s : ((factorCoupling n a).prod (factorCoupling n b)).Seed) :
    (pairFactors n a b s).2 ≤ 6*n^3+192 := by
  have hp := SamplerProductCells.cells (factor n a) (factor n b)
    (3*n^3+88) (3*n^3+88) (factor_cells n a) (factor_cells n b) s
  dsimp only [pairFactors]
  omega

def triple (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    SamplerExecution.Trace ↥(tripleRange a b c) × ℕ :=
  let r := SamplerProductCells.run (pairFactors n a b) (factor n c) (3*n^3+88) s
  (⟨r.1.value.map (tripleFactorEquiv a b c), r.1.reads, r.1.tests⟩, r.2+8)

theorem triple_value (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    (triple n a b c s).1 = (SamplerExecution.triplePrime n a b c).run s := by
  have hv := SamplerProductCells.value (pairFactors n a b) (factor n c) (3*n^3+88)
    (SamplerExecution.prod (SamplerExecution.factor n a) (SamplerExecution.factor n b))
    (SamplerExecution.factor n c) (pairFactors_value n a b) (factor_value n c) s
  simp only [triple, SamplerExecution.triplePrime, SamplerExecution.map, hv]

theorem triple_cells (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    (triple n a b c s).2 ≤ 9*n^3+304 := by
  have hp := SamplerProductCells.cells (pairFactors n a b) (factor n c)
    (6*n^3+192) (3*n^3+88) (pairFactors_cells n a b) (factor_cells n c) s
  change _+8 ≤ _
  omega

def nested (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    (Option (Vector ℕ 3) × ℕ) × ℕ :=
  let r := triple n a b c s
  ((r.1.value.map (fun p => ScalarSamplerArrays.factors p.val), r.1.reads+r.1.tests+7), r.2+16)

theorem nested_value (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    (nested n a b c s).1 = ScalarSamplerArrays.nested n a b c s := by
  simp only [nested, triple_value, ScalarSamplerArrays.nested]

theorem nested_cells (n a b c : ℕ) (s : (triplePrimeCoupling n a b c).Seed) :
    (nested n a b c s).2 ≤ 9*n^3+320 := by
  have hp := triple_cells n a b c s
  change _+16 ≤ _
  omega

def extra {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) (s : (primeCoupling hell n).Seed) :
    (Option ℕ × ℕ) × ℕ :=
  let r := SamplerVectorCells.primeSeed hell n s
  ((r.1.value.map Subtype.val, r.1.reads+r.1.tests+1), r.2+16)

theorem extra_value {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) (s : (primeCoupling hell n).Seed) :
    (extra hell n s).1 = ScalarSamplerArrays.extra hell n s := by
  simp only [extra, SamplerVectorCells.primeSeed_value, ScalarSamplerArrays.extra]

theorem extra_cells {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ) (s : (primeCoupling hell n).Seed) :
    (extra hell n s).2 ≤ 3*n^3+96 := by
  have h := SamplerVectorCells.primeSeed_cells hell n s
  change _+16 ≤ _
  omega

def residueTail (n pL pR : ℕ) [NeZero pL] [NeZero pR]
    (s : ((finCoupling n pL).prod (finCoupling n pR)).Seed) :=
  SamplerProductCells.run (SamplerFinCells.run n pL) (SamplerFinCells.run n pR) (3*n^3+80) s

theorem residueTail_value (n pL pR : ℕ) [NeZero pL] [NeZero pR]
    (s : ((finCoupling n pL).prod (finCoupling n pR)).Seed) :
    (residueTail n pL pR s).1 =
      (SamplerExecution.prod (SamplerExecution.fin n pL) (SamplerExecution.fin n pR)).run s :=
  SamplerProductCells.value _ _ _ _ _ (SamplerFinCells.run_value n pL)
    (SamplerFinCells.run_value n pR) s

theorem residueTail_cells (n pL pR : ℕ) [NeZero pL] [NeZero pR]
    (s : ((finCoupling n pL).prod (finCoupling n pR)).Seed) :
    (residueTail n pL pR s).2 ≤ 6*n^3+176 := by
  have h := SamplerProductCells.cells (SamplerFinCells.run n pL) (SamplerFinCells.run n pR)
    (3*n^3+80) (3*n^3+80) (SamplerFinCells.run_cells n pL) (SamplerFinCells.run_cells n pR) s
  dsimp only [residueTail]
  omega

def residues (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR]
    (s : (ScalarSamplerArrays.residueCoupling n p0 pL pR).Seed) :
    (Option (Vector ℕ 3) × ℕ) × ℕ :=
  let r := SamplerProductCells.run (SamplerFinCells.run n p0) (residueTail n pL pR)
    (6*n^3+176) s
  ((r.1.value.map ScalarSamplerArrays.residueValues, r.1.reads+r.1.tests+7), r.2+16)

theorem residues_value (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR]
    (s : (ScalarSamplerArrays.residueCoupling n p0 pL pR).Seed) :
    (residues n p0 pL pR s).1 = ScalarSamplerArrays.residues n p0 pL pR s := by
  have h := SamplerProductCells.value (SamplerFinCells.run n p0) (residueTail n pL pR)
    (6*n^3+176) (SamplerExecution.fin n p0)
    (SamplerExecution.prod (SamplerExecution.fin n pL) (SamplerExecution.fin n pR))
    (SamplerFinCells.run_value n p0) (residueTail_value n pL pR) s
  simp only [residues, h, ScalarSamplerArrays.residues, ScalarSamplerArrays.residueExecution]

theorem residues_cells (n p0 pL pR : ℕ) [NeZero p0] [NeZero pL] [NeZero pR]
    (s : (ScalarSamplerArrays.residueCoupling n p0 pL pR).Seed) :
    (residues n p0 pL pR s).2 ≤ 9*n^3+288 := by
  have h := SamplerProductCells.cells (SamplerFinCells.run n p0) (residueTail n pL pR)
    (3*n^3+80) (6*n^3+176) (SamplerFinCells.run_cells n p0) (residueTail_cells n pL pR) s
  change _+16 ≤ _
  omega

end LowSpaceSubsetSum.ScalarSamplerCells

end

end OAI
