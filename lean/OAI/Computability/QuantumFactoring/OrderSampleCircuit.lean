import Mathlib
import OAI.Computability.QuantumFactoring.ModularPower
import OAI.Computability.QuantumFactoring.HornerEncoding
import OAI.Computability.QuantumFactoring.CoherentSampling
import OAI.Computability.QuantumFactoring.AppendRegister
import OAI.Computability.QuantumFactoring.TriangularPreparation

namespace OAI

section
open scoped BigOperators


/-! Actual modular-power/triangular-transform order sampler. All arithmetic
inputs are read-only wires; the modular output remains coherent. -/
namespace ExactQuantumFactoring.OrderSample
open scoped BigOperators
open BooleanNetwork Triangular

abbrev inputWidth (w b : ℕ) := (w+w)+Triangular.width b

noncomputable def inputWord {w b : ℕ} (a m : Basis w) (x : Basis b) :
    Basis (inputWidth w b) := Fin.append (Fin.append a m) (Triangular.encode b (x,0))

def powerInputs (w b : ℕ) : BooleanNetwork (inputWidth w b) ((w+w)+b) :=
  select (Fin.addCases (Fin.castAdd (Triangular.width b))
    (fun i => Fin.natAdd (w+w) (Triangular.dataWire i)))

lemma powerInputs_eval {w b : ℕ} (a m : Basis w) (x : Basis b) :
    (powerInputs w b).eval (inputWord a m x) = Fin.append (Fin.append a m) x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [powerInputs,eval_select,Function.comp_apply,Fin.addCases_left,inputWord,
      Fin.append_left]
  · simp only [powerInputs,eval_select,Function.comp_apply,Fin.addCases_right,inputWord,
      Fin.append_right,Triangular.encode_bit]

def powerNetwork (w b : ℕ) : BooleanNetwork (inputWidth w b) w :=
  (powerInputs w b).comp (BitArithmetic.modularPower w b)

lemma powerNetwork_count (w b : ℕ) : (powerNetwork w b).net.count ≤
    w+b*(3672*w*w+436*w+36) := by
  simpa only [powerNetwork,count_comp,powerInputs,count_select,zero_add] using
    BitArithmetic.modularPower_count w b

lemma powerNetwork_value {w b : ℕ} (a m : Basis w) (x : Basis b)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (bitsValue ((powerNetwork w b).eval (inputWord a m x))).toNat =
      (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat := by
  rw [powerNetwork,eval_comp,powerInputs_eval,BitArithmetic.modularPower_value _ _ _ hm,
    BitArithmetic.horner_full]

lemma powerNetwork_eq {w b : ℕ} (a m : Basis w) (x : Basis b) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (powerNetwork w b).eval (inputWord a m x)=u ↔
      (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat=(bitsValue u).toNat := by
  rw [← powerNetwork_value a m x hm]
  constructor
  · intro h; rw [h]
  · intro h
    exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)

abbrev scratch (w b : ℕ) := w+b*(3672*w*w+436*w+36)
abbrev width (w b : ℕ) := inputWidth w b+w+scratch w b

def program (w s : ℕ) : List (Instruction (width w (s+2))) :=
  sampleProgram (powerNetwork w (s+2)) (powerNetwork_count w (s+2))
    (rightProgram (w+w) (Triangular.transform s))

lemma program_length (w s : ℕ) : (program w s).length ≤
    4*scratch w (s+2)+2*w+(s+2)*(998*(s+2)+49)+2*(s+5) := by
  have hh := sampleProgram_length (powerNetwork w (s+2)) (powerNetwork_count w (s+2))
    (rightProgram (w+w) (Triangular.transform s))
  have ht := Triangular.transform_length s
  have hp := powerNetwork_count w (s+2)
  simp only [rightProgram,List.length_map] at hh
  change (program w s).length ≤ _ at hh
  dsimp [scratch] at ⊢
  omega

noncomputable def word {w b : ℕ} (a m : Basis w) (x : Basis b) (u : Basis w) :
    Basis (width w b) := packed (scratch w b) (inputWord a m x) u

noncomputable def uniformInput (w b : ℕ) (a m : Basis w) : State (width w b) :=
  encodeState (fun x : Basis b => word a m x (fun _ => false))
    (fun _ => (Real.sqrt ((2:ℝ)^b):ℂ)⁻¹)

lemma transform_entry {w s : ℕ} (a m : Basis w) (x y : Basis (s+2)) :
    programMatrix (rightProgram (w+w) (Triangular.transform s))
      (inputWord a m y) (inputWord a m x) =
    (Real.sqrt ((2:ℝ)^(s+2)):ℂ)⁻¹ *
      OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(s+2)) := by
  rw [inputWord,inputWord,rightProgram_entry]
  have hh := Triangular.transform_selected s x y
  simpa only [matrix_basisVector] using hh

/-- The physically produced selected amplitude, expressed as a finite word sum. -/
lemma program_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (program w s)).mulVec (uniformInput w (s+2) a m) (word a m y u) =
      ((2:ℂ)^(s+2))⁻¹ * ∑ x : Basis (s+2),
        if (bitsValue a).toNat^inputNumber x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(s+2)) else 0 := by
  classical
  rw [program,uniformInput]
  change (programMatrix (sampleProgram _ _ _)).mulVec
    (encodeState (fun x : Basis (s+2) => packed _ (inputWord a m x) (fun _ => false)) _)
    (packed _ (inputWord a m y) u) = _
  rw [sampleProgram_encoded_amplitude]
  simp_rw [powerNetwork_eq a m _ u hm,transform_entry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · have hh : (Real.sqrt ((2:ℝ)^(s+2)):ℂ)^2 = (2:ℂ)^(s+2) := by
      rw [← Complex.ofReal_pow,Real.sq_sqrt (by positivity),Complex.ofReal_pow]
      rfl
    rw [← hh]
    ring
  · simp

lemma inputNumber_sum (b : ℕ) (f : ℕ → ℂ) :
    (∑ x : Basis b, f (inputNumber x)) = ∑ x ∈ Finset.range (2^b), f x := by
  let e : Basis b ≃ Fin (2^b) := Equiv.ofBijective _ (Triangular.inputNumber_bijective b)
  rw [← Fin.sum_univ_eq_sum_range]
  exact e.sum_comp (fun x => f x.val)

/-- Exactly 1/Q times the coherent modular-power residue sum of Section3. -/
theorem program_amplitude_range {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (program w s)).mulVec (uniformInput w (s+2) a m) (word a m y u) =
      ((2^(s+2):ℕ):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^(s+2)),
        if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((outputNumber y:ℝ)*x/(2^(s+2):ℕ)) else 0 := by
  rw [program_amplitude a m y u hm]
  push_cast
  simp_rw [mul_comm (inputNumber _ : ℝ) (outputNumber y : ℝ)]
  congr 1
  exact inputNumber_sum (s+2) (fun x =>
    if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
    then OrderTrial.phase ((outputNumber y:ℝ)*x/(2:ℝ)^(s+2)) else 0)

end ExactQuantumFactoring.OrderSample


end

end OAI
