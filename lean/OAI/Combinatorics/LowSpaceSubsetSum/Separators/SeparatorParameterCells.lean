import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorParameterExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ComputedFuelCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MixerParameterCells

namespace OAI

/-! # Live scalar storage while preparing a separating family

The power and logarithm loops use scalar accumulators. The five binomial
computations use the actual multiplicative loop, retaining four denominator
states and the numerator. Input scalars and all four returned counts fit
inside a constant number of cells.
-/

namespace LowSpaceSubsetSum.SeparatorParameterCells

open scoped BigOperators

def powerLoop : ℕ → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | 0, value, work => ((value,work+1),16)
  | fuel+1, value, work => powerLoop fuel (value*3) (work+3)

theorem powerLoop_value (fuel value work : ℕ) :
    (powerLoop fuel value work).1 = SeparatorParameterExecution.powerLoop fuel value work := by
  induction fuel generalizing value work with
  | zero => rfl
  | succ fuel ih => exact ih _ _

theorem powerLoop_cells (fuel value work : ℕ) : (powerLoop fuel value work).2 ≤ 16 := by
  induction fuel generalizing value work with
  | zero => exact le_rfl
  | succ fuel ih => exact ih _ _

def logBits (m : ℕ) : (ℕ × ℕ) × ℕ :=
  let power := powerLoop m 1 0
  let bits := MixerParameterCells.logLoop (2*m) power.1.1 0 0 0
  ((bits.1.1,power.1.2+bits.1.2+2),power.2+bits.2+16)

theorem logBits_value (m : ℕ) : (logBits m).1 = SeparatorParameterExecution.logBits m := by
  simp only [logBits,powerLoop_value,MixerParameterCells.logLoop_value,
    SeparatorParameterExecution.logBits,MeasuredLog2.run]

theorem logBits_cells (m : ℕ) : (logBits m).2 ≤ 48 := by
  have hp := powerLoop_cells m 1 0
  have hb := MixerParameterCells.logLoop_cells (2*m) (powerLoop m 1 0).1.1 0 0 0
  simp only [Nat.zero_max] at hb
  change _+_+16 ≤ _
  omega

def sample (g k : ℕ) : (ℕ × ℕ) × ℕ :=
  let bits := logBits (4*g)
  (((8*g*g-bits.1.1*(g-k))/(16*g),bits.1.2+12),bits.2+16)

theorem sample_value (g k : ℕ) : (sample g k).1 = SeparatorParameterExecution.sample g k := by
  simp only [sample,logBits_value,SeparatorParameterExecution.sample]

theorem sample_cells (g k : ℕ) : (sample g k).2 ≤ 64 := by
  have h := logBits_cells (4*g)
  change _+16 ≤ _
  omega

def families (g k e : ℕ) : (Vector ℕ 4 × ℕ) × ℕ :=
  let numerator := ComputedFuelCells.choose g e
  let denominators := Vector.ofFn (fun i : Fin 4 =>
    ComputedFuelCells.choose (g/2) (e-balancedBlockCounts 4 k i))
  ((Vector.ofFn (fun i : Fin 4 =>
      (10*numerator.1.value) ⌈/⌉ denominators[i.val].1.value),
    8*numerator.1.steps+(∑ i : Fin 4,8*denominators[i.val].1.steps+6)+10),
    numerator.2+(∑ i : Fin 4,denominators[i.val].2)+80)

theorem families_value (g k e : ℕ) :
    (families g k e).1 = SeparatorParameterExecution.families g k e := by
  simp only [families,SeparatorParameterExecution.families,Vector.getElem_ofFn,
    ComputedFuelCells.choose_value]

theorem families_cells (g k e : ℕ) : (families g k e).2 ≤ 160 := by
  have hn := ComputedFuelCells.choose_cells g e
  have hd := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    ComputedFuelCells.choose_cells (g/2) (e-balancedBlockCounts 4 k i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hd
  change _+(∑ i : Fin 4,
    (ComputedFuelCells.choose (g/2) (e-balancedBlockCounts 4 k i)).2)+80 ≤ _
  omega

def run (g k : ℕ) : (SeparatorParameterExecution.Data × ℕ) × ℕ :=
  let e := sample g k
  let counts := families g k e.1.1
  ((⟨e.1.1,counts.1.1⟩,e.1.2+counts.1.2+1),e.2+counts.2+16)

theorem run_value (g k : ℕ) : (run g k).1 = SeparatorParameterExecution.run g k := by
  simp only [run,sample_value,families_value,SeparatorParameterExecution.run]

theorem run_work (g k : ℕ) : (run g k).1.2 ≤ 60*g+51 := by
  rw [run_value]
  exact SeparatorParameterExecution.work g k

theorem run_cells (g k : ℕ) : (run g k).2 ≤ 240 := by
  have he := sample_cells g k
  have hc := families_cells g k (sample g k).1.1
  change _+_+16 ≤ _
  omega

end LowSpaceSubsetSum.SeparatorParameterCells

end OAI
