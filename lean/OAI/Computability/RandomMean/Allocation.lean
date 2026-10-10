import OAI.Computability.RandomMean.Loop

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Counter
noncomputable def fixedPower : ℕ → Code Count Count
  | 0 => const [()]
  | k+1 => (Code.id ⋏ₚ fixedPower k) ≫ₚ mul
@[simp] theorem fixedPower_length (k : ℕ) (c : Count) : (fixedPower k c).length=c.length^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [fixedPower,ih,pow_succ,Nat.mul_comm]
end Counter
namespace RootCode
open InputCode

noncomputable def g : Code Parsed Count := width ≫ₚ NaturalLog.length ≫ₚ Counter.inc ≫ₚ Counter.inc
noncomputable def argument : Code Parsed Count := (const (List.replicate (2^17) ()) ⋏ₚ g) ≫ₚ Counter.mul
noncomputable def exponent : Code Parsed Count := argument ≫ₚ Counter.word ≫ₚ NaturalLog.ceil
noncomputable def cap : Code Parsed Count := (argument ⋏ₚ argument) ≫ₚ Counter.add
noncomputable def samples : Code Parsed Count := (exponent ⋏ₚ cap) ≫ₚ Counter.power
noncomputable def trialBase : Code Parsed Count := (samples ⋏ₚ (n ≫ₚ Counter.inc)) ≫ₚ Counter.mul ≫ₚ Counter.fixedPower 6
noncomputable def trials : Code Parsed Count := (trialBase ⋏ₚ trialBase) ≫ₚ Counter.add ≫ₚ Counter.inc
noncomputable def basic : Code Parsed Count := (n ⋏ₚ ((const (List.replicate 128 ()) ⋏ₚ samples) ≫ₚ Counter.mul)) ≫ₚ Counter.mul
noncomputable def env : Code Parsed RawControl.Env := rows ⋏ₚ exponent ⋏ₚ samples ⋏ₚ trials ⋏ₚ basic

theorem g_length (G : Game) : (g (game G)).length=globalG (topWidth G).toNat+1 := by
  change (NaturalLog.length (width (game G))).length+1+1=_
  rw [NaturalLog.length_exact _ (by rw [width_val]; exact (topWidth_positive G).le),width_val]
  unfold globalG
  omega
 theorem argument_length (G : Game) : (argument (game G)).length=2^17*(globalG (topWidth G).toNat+1) := by
  simp only [argument,comp_eval,pair_eval,const_eval,Counter.mul_length,List.length_replicate,g_length]
 theorem exponent_length (G : Game) : (exponent (game G)).length=sampleExponent (topWidth G).toNat := by
  change (NaturalLog.ceil (Counter.word (argument (game G)))).length=_
  rw [NaturalLog.ceil_exact _ (by rw [Counter.word_val]; exact_mod_cast (show 0<(argument (game G)).length by rw [argument_length]; positivity)),Counter.word_val,Int.toNat_natCast,argument_length]
  rfl
 theorem samples_length (G : Game) : (samples (game G)).length=globalS (topWidth G).toNat := by
  change (Counter.power (exponent (game G),cap (game G))).length=_
  rw [Counter.power_exact]
  · rw [List.length_replicate,exponent_length]
    rfl
  · change 2^(exponent (game G)).length ≤ (Counter.add (argument (game G),argument (game G))).length
    rw [Counter.add_length,exponent_length,argument_length]
    have h := Counter.pow_clog_le (2^17*(globalG (topWidth G).toNat+1)) (by positivity)
    change 2^Nat.clog 2 (2^17*(globalG (topWidth G).toNat+1)) ≤ _
    simpa only [two_mul] using h
 theorem trials_length (G : Game) : (trials (game G)).length=globalJ G.n (topWidth G).toNat := by
  simp only [trials,trialBase,comp_eval,pair_eval,Counter.inc_length,Counter.add_length,Counter.fixedPower_length,Counter.mul_length,n_game,List.length_replicate,samples_length]
  unfold globalJ
  omega
 theorem basic_length (G : Game) : (basic (game G)).length=G.n*(128*globalS (topWidth G).toNat) := by
  simp only [basic,comp_eval,pair_eval,Counter.mul_length,const_eval,List.length_replicate,n_game,samples_length]
 theorem env_rep (G : Game) : RawControl.EnvRep G (topWidth G).toNat (env (game G)) := by
  refine ⟨⟨Normalize.word G,rows_game G,Normalize.word_val G⟩,exponent_length G,samples_length G,trials_length G,?_⟩
  exact (basic_length G).ge
end RootCode
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace RootCode
open InputCode
noncomputable def ones : Code Parsed (List W) := n ≫ₚ map (Word.constant 1)
noncomputable def budgets : Code Parsed RawBudget.Data :=
  ((n ≫ₚ Counter.word) ⋏ₚ Word.constant 1) ⋏ₚ
  ((n ≫ₚ Counter.word) ⋏ₚ Word.constant 1) ⋏ₚ ones ⋏ₚ ones
noncomputable def box : Code Parsed RawBox.Data :=
  width ⋏ₚ (n ≫ₚ map (Word.constant 0)) ⋏ₚ ((width ⋏ₚ n) ≫ₚ envMap (fst : Code (W×Unit) W))
noncomputable def state : Code Parsed RawControl.State :=
  RawControl.call 0 (RawControl.pack budgets box) (const [])
noncomputable def start : Code Digits (W×RawControl.Acc) :=
  parse ≫ₚ (width ⋏ₚ (env ⋏ₚ state))

 theorem budgets_rep (G : Game) : RawBudget.Rep (rootBudgets G) (budgets (game G)) := by
  have hn : (Counter.word (n (game G))).val=G.n := by simp
  have hx : ones (game G)=List.ofFn (fun _ : Fin G.n => EdgeRead.encodedWord 1) := by
    change (List.replicate G.n ()).map (fun _ => EdgeRead.encodedWord 1)=_
    simp [List.ofFn_const]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change 0<(Counter.word (n (game G))).val
    rw [hn]; exact_mod_cast G.positive
  · change 0<(Word.constant 1 (game G)).val
    simp
  · change 0<(Counter.word (n (game G))).val
    rw [hn]; exact_mod_cast G.positive
  · change 0<(Word.constant 1 (game G)).val
    simp
  · change (G.n : ℚ)=(Counter.word (n (game G))).val/(Word.constant 1 (game G)).val
    simp
  · change (G.n : ℚ)=(Counter.word (n (game G))).val/(Word.constant 1 (game G)).val
    simp
  · refine ⟨fun _ => EdgeRead.encodedWord 1,fun _ => EdgeRead.encodedWord 1,hx,hx,?_,?_,?_,?_⟩ <;>
      intro i <;> simp [EdgeRead.encodedWord_val,rootBudgets]
 theorem box_rep (G : Game) : RawBox.Rep (rootBox G) (box (game G)) := by
  refine ⟨?_,?_,?_⟩
  · change (width (game G)).val=((topWidth G).toNat : ℤ)
    rw [width_val,Int.toNat_of_nonneg (topWidth_positive G).le]
  · refine ⟨fun _ => EdgeRead.encodedWord 0,?_,?_⟩
    · change (List.replicate G.n ()).map (fun _ => EdgeRead.encodedWord 0)=_
      simp [List.ofFn_const]
    · intro i; exact EdgeRead.encodedWord_val 0
  · refine ⟨fun _ => width (game G),?_,?_⟩
    · change (List.replicate G.n ()).map (fun _ => width (game G))=_
      simp [List.ofFn_const]
    · intro i; exact width_val G
 theorem state_rep (G : Game) : RawControl.StateRep
    (SourceControl.State.call (SourceControl.Job.solve (rootBudgets G) (rootBox G)) .done) (state (game G)) := by
  exact .call rfl ⟨budgets_rep G,box_rep G⟩ .done
end RootCode
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Allocation
end Allocation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff

namespace PolyBound
variable {ι : Type} {r f g : ι→ℕ}
end PolyBound
namespace TreeDevice
open BinaryData
end TreeDevice
end MeanPayoff

end

end OAI
