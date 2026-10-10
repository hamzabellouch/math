import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedFamilyExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorParameterCells

namespace OAI

/-! # Executing the integer separator parameters before family generation -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

abbrev SeparatorPrepared (g k : ℕ) :=
  {d : SeparatorParameterExecution.Data // d = (SeparatorParameterExecution.run g k).1}

def separatorCompute (g k : ℕ) : (SeparatorPrepared g k × ℕ) × ℕ :=
  let r := SeparatorParameterCells.run g k
  ((⟨r.1.1,congrArg Prod.fst (SeparatorParameterCells.run_value g k)⟩,r.1.2+2),r.2+16)

def familiesFromSeparatorData (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2*g ≤ 3*k) (w n : ℕ) (hw : Nat.clog 2 g ≤ w)
    (d : SeparatorPrepared g k) :
    Execution (WordSeedRealization.families
      (SeparatorParameters.rounded g k hg heven hk hklo) w n hw) :=
  familiesUsing (SeparatorParameters.rounded g k hg heven hk hklo)
    (fun _ => d.val.size) (fun i => d.val.counts[i.val])
    (fun i => by rw [d.property]; exact SeparatorParameterExecution.rounded_size g k hg heven hk hklo i)
    (fun i => by rw [d.property]; exact SeparatorParameterExecution.rounded_counts g k hg heven hk hklo i)
    w n hw

def familiesPrepared (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2*g ≤ 3*k) (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    Execution (WordSeedRealization.families
      (SeparatorParameters.rounded g k hg heven hk hklo) w n hw) :=
  prepareThen (fun _ => separatorCompute g k)
    (familiesFromSeparatorData g k hg heven hk hklo w n hw)

theorem separatorCompute_work (g k : ℕ) :
    (separatorCompute g k).1.2 ≤ 60*g+53 := by
  have h := SeparatorParameterExecution.work g k
  rw [←SeparatorParameterCells.run_value] at h
  change (SeparatorParameterCells.run g k).1.2+2 ≤ _
  omega

theorem separatorCompute_cells (g k : ℕ) :
    (separatorCompute g k).2 ≤ 256 := by
  have h := SeparatorParameterCells.run_cells g k
  change (SeparatorParameterCells.run g k).2+16 ≤ _
  omega

theorem familiesPrepared_bounded (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2*g ≤ 3*k) (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    (familiesPrepared g k hg heven hk hklo w n hw).Bounded
      (60*g+55+100*(11*2^g+1)*(maskBudget n g+100))
      (264+100*(11*2^g+1)*(maskBudget n g+100))
      (264+100*(11*2^g+1)*(maskBudget n g+100)) := by
  have h := prepareThen_bounded (fun _ => separatorCompute g k)
    (familiesFromSeparatorData g k hg heven hk hklo w n hw)
    (60*g+53) 256 _ _ _ (separatorCompute_work g k) (separatorCompute_cells g k)
    (fun d => by
      apply familiesUsing_bounded)
  exact bounded_mono _ h (by omega) (by omega) (by omega)

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
