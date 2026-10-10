import OAI.MathematicalPhysics.RapidForcing.VelocitySyntax
import OAI.MathematicalPhysics.RapidForcing.RecursiveComputable
import OAI.MathematicalPhysics.RapidForcing.RatOperations

namespace OAI

open Encodable
open scoped BigOperators
namespace RapidForcing
open EffectiveArithmetic
@[fun_prop] lemma computable_fin_val {n : ℕ} : Computable (fun i : Fin n => i.val) := Primrec.fin_val.to_comp
@[fun_prop] lemma compPred_nat_lt : CompPred (fun p : ℕ × ℕ => p.1 < p.2) := Primrec.nat_lt.decide.to_comp
@[fun_prop] lemma compPred_nat_le : CompPred (fun p : ℕ × ℕ => p.1 ≤ p.2) := Primrec.nat_le.decide.to_comp

namespace ScaleData
private def dataEquiv : ScaleData ≃ ℕ × ℕ × ℕ :=
  ⟨fun d => (d.rA, d.rQ, d.B), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩
instance : Primcodable ScaleData := Primcodable.ofEquiv (ℕ × ℕ × ℕ) dataEquiv
@[fun_prop] lemma primrec_rA : Primrec ScaleData.rA := Primrec.fst.comp (Primrec.of_equiv (e := dataEquiv))
@[fun_prop] lemma primrec_rQ : Primrec ScaleData.rQ := (Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := dataEquiv))
@[fun_prop] lemma primrec_B : Primrec ScaleData.B := (Primrec.snd.comp Primrec.snd).comp (Primrec.of_equiv (e := dataEquiv))
@[fun_prop] lemma primrec_mk : Primrec (fun p : ℕ × ℕ × ℕ => ScaleData.mk p.1 p.2.1 p.2.2) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec (@encode (ℕ × ℕ × ℕ) _))
@[fun_prop] lemma computable_A : Computable ScaleData.A := by unfold A; fun_prop
@[fun_prop] lemma computable_S : Computable ScaleData.S := by unfold S; fun_prop
@[fun_prop] lemma computable_P : Computable (fun p : ScaleData × ℕ => p.1.P p.2) := by unfold P; fun_prop
@[fun_prop] lemma computable_L : Computable (fun p : ScaleData × ℕ => p.1.L p.2) := by unfold L; fun_prop
@[fun_prop] lemma computable_capacity : Computable (fun p : ScaleData × ℕ => p.1.capacity p.2) := by unfold capacity; fun_prop
@[fun_prop] lemma computable_C : Computable ScaleData.C := by unfold C; fun_prop
@[fun_prop] lemma computable_s : Computable (fun p : ScaleData × ℕ => p.1.s p.2) := by unfold s; fun_prop
@[fun_prop] lemma computable_D : Computable (fun p : ScaleData × ℕ => p.1.D p.2) := by unfold D; fun_prop
@[fun_prop] lemma computable_deltaQ : Computable (fun p : ScaleData × ℕ => p.1.δQ p.2) := by unfold δQ; fun_prop
@[fun_prop] lemma computable_bQ : Computable (fun p : ScaleData × ℕ => p.1.bQ p.2) := by unfold bQ; fun_prop
end ScaleData

abbrev RawMachine := ℕ × ℕ × ℕ × List (Option (ℕ × ℕ × Move))
abbrev RawInput := RawMachine × List ℕ
namespace RawMachine

def instruction (M : RawMachine) (q z : ℕ) : ℕ × ℕ × Move :=
  if q < M.1 ∧ z < M.2.1 then
    (M.2.2.2[q * M.2.1 + z]?.getD none).getD (M.1, z, 1)
  else (M.1, z, 1)

def scaleData (M : RawMachine) (w : List ℕ) : ScaleData := ⟨M.2.1 + 1, M.1 + 1, w.length⟩
def terminalDigit (M : RawMachine) (d : ScaleData) (k : ℕ) : ℕ :=
  if k % d.S = M.1 then 1 else 0

def nextDigit (M : RawMachine) (d : ScaleData) (n k : ℕ) : ℕ :=
  let q := k % d.S
  let j := (k / d.S) % d.P n
  let T := k / (d.S * d.P n)
  let z := (T / d.A ^ j) % d.A
  if q < M.1 ∧ j ≤ 2 * n ∧ z < M.2.1 then
    let inst := M.instruction q z
    inst.1 + d.S * (j + inst.2.2.val +
      d.P (n + 1) * d.A * (T - z * d.A ^ j + inst.2.1 * d.A ^ j))
  else 0

def initialDigit (M : RawMachine) (w : List ℕ) : ℕ :=
  let d := M.scaleData w
  M.2.2.1 + d.S * (d.P 0 * ((w.zipIdx.map fun a => a.1 * d.A ^ a.2).sum))

@[fun_prop] lemma computable_scaleData : Computable (fun p : RawInput => scaleData p.1 p.2) := by
  unfold scaleData; fun_prop
@[fun_prop] lemma computable_instruction : Computable (fun p : RawMachine × ℕ × ℕ => instruction p.1 p.2.1 p.2.2) := by
  have hg : Computable (fun p : RawMachine × ℕ × ℕ => p.1.2.2.2[p.2.1 * p.1.2.1 + p.2.2]?) :=
    Primrec.list_getElem?.to_comp.comp (by fun_prop) (by fun_prop)
  unfold instruction
  fun_prop (disch := assumption)
@[fun_prop] lemma computable_terminalDigit : Computable (fun p : RawMachine × ScaleData × ℕ => terminalDigit p.1 p.2.1 p.2.2) := by
  unfold terminalDigit; fun_prop

private def digitParts (p : ScaleData × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let q := p.2.2 % p.1.S
  let j := (p.2.2 / p.1.S) % p.1.P p.2.1
  let T := p.2.2 / (p.1.S * p.1.P p.2.1)
  (q, j, T, (T / p.1.A ^ j) % p.1.A)
private lemma computable_digitParts : Computable digitParts := by
  have hq : Computable (fun p : ScaleData × ℕ × ℕ => p.2.2 % p.1.S) := by fun_prop
  have hj : Computable (fun p : ScaleData × ℕ × ℕ => (p.2.2 / p.1.S) % p.1.P p.2.1) := by fun_prop
  have hT : Computable (fun p : ScaleData × ℕ × ℕ => p.2.2 / (p.1.S * p.1.P p.2.1)) := by fun_prop
  have hf : Computable (fun p : ScaleData × (ℕ × ℕ × ℕ) =>
      (p.2.1, p.2.2.1, p.2.2.2, (p.2.2.2 / p.1.A ^ p.2.2.1) % p.1.A)) := by fun_prop
  exact (hf.comp (Computable.fst.pair (hq.pair (hj.pair hT)))).of_eq (fun _ => rfl)
private def digitFinish (p : (RawMachine × ScaleData × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × Move)) : ℕ :=
  if p.2.1.1 < p.1.1.1 ∧ p.2.1.2.1 ≤ 2 * p.1.2.2 ∧ p.2.1.2.2.2 < p.1.1.2.1 then
    p.2.2.1 + p.1.2.1.S * (p.2.1.2.1 + p.2.2.2.2.val +
      p.1.2.1.P (p.1.2.2 + 1) * p.1.2.1.A * (p.2.1.2.2.1 - p.2.1.2.2.2 * p.1.2.1.A ^ p.2.1.2.1 + p.2.2.2.1 * p.1.2.1.A ^ p.2.1.2.1))
  else 0
private lemma computable_digitFinish : Computable digitFinish := by
  unfold digitFinish
  fun_prop
@[fun_prop] lemma computable_nextDigit : Computable (fun p : RawMachine × ScaleData × ℕ × ℕ => nextDigit p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hp := computable_digitParts.comp (show Computable (fun p : RawMachine × ScaleData × ℕ × ℕ => p.2) by fun_prop)
  let assemble (p : (RawMachine × ScaleData × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) :=
    ((p.1.1, p.1.2.1, p.1.2.2.1), p.2, instruction p.1.1 p.2.1 p.2.2.2.2)
  have ha : Computable assemble := by unfold assemble; fun_prop
  exact (computable_digitFinish.comp (ha.comp (Computable.id.pair hp))).of_eq (fun _ => rfl)

private def tapeDigits (A : ℕ) (w : List ℕ) : ℕ := (w.zipIdx.map fun a => a.1 * A ^ a.2).sum
private lemma tapeDigits_cons (A z : ℕ) (w : List ℕ) : tapeDigits A (z :: w) = z + A * tapeDigits A w := by
  simp only [tapeDigits, List.zipIdx_cons', List.map_cons, List.sum_cons, pow_zero,
    mul_one, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  dsimp
  rw [pow_succ]
  ring
@[fun_prop] lemma computable_initialDigit : Computable (fun p : RawInput => initialDigit p.1 p.2) := by
  have hpow : Computable (fun p : ℕ × List ℕ => tapeDigits p.1 p.2) := by
    have h := computable_list_foldr (f := fun p : ℕ × List ℕ => p.2) (g := fun _ => (0 : ℕ))
      (h := fun p a => a.1 + p.1 * a.2) (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)
    apply h.of_eq
    intro p
    induction p.2 with
    | nil => rfl
    | cons z w ih => simp only [List.foldr_cons, tapeDigits_cons, ih]
  have ht := hpow.comp (show Computable (fun p : RawInput => ((scaleData p.1 p.2).A, p.2)) by fun_prop)
  unfold initialDigit
  change Computable (fun p : RawInput => p.1.2.2.1 + (scaleData p.1 p.2).S *
    ((scaleData p.1 p.2).P 0 * tapeDigits (scaleData p.1 p.2).A p.2))
  fun_prop (disch := assumption)

end RawMachine
end RapidForcing

end OAI
