import OAI.Computability.RandomMean.Traces

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.Chunks
open BinaryData
open BinaryStack.Addition (value)
open SignedBits (value_bound)
def decode (e : ℕ) : ℕ→List Bool→List Count
  | 0,_ => []
  | n+1,bs => List.replicate (value (bs.take e).reverse) () :: decode e n (bs.drop e)
 theorem sample_exact (s : State) (hc : 2 ^ (s.1.1.length) ≤ s.1.2.length) (hl : s.1.1.length ≤ s.2.2.bits.length) :
    sample s=List.replicate (value (s.2.2.bits.take s.1.1.length).reverse) () := by
  change Counter.bounded (IntegerRead.positive (Split.split (s.2.2.bits,s.1.1)).1.reverse,s.1.2)=_
  rw [Split.exact _ _ hl]
  apply Counter.bounded_exact
  · simp only [IntegerRead.positive,SignedBits.Word.val,Bool.false_eq_true,↓reduceIte,sub_zero]
  · have h := value_bound (s.2.2.bits.take s.1.1.length).reverse
    rw [List.length_reverse,List.length_take,min_eq_left hl] at h
    omega
 theorem fold_decode (s : State) (cs : Count) (hc : 2 ^ (s.1.1.length) ≤ s.1.2.length)
    (hl : s.1.1.length*cs.length ≤ s.2.2.bits.length) :
    (Fold.fold step.eval s cs).2.1.reverse=s.2.1.reverse++decode s.1.1.length cs.length s.2.2.bits := by
  induction cs generalizing s with
  | nil => simp [Fold.fold,decode]
  | cons u us ih =>
    have he : s.1.1.length ≤ s.2.2.bits.length := by simp only [List.length_cons] at hl; nlinarith
    have hd : (next s).1.1.length*us.length ≤ (next s).2.2.bits.length := by
      rw [next_params,next_bits,List.length_drop]
      simp only [List.length_cons] at hl
      have hh : s.1.1.length*us.length+s.1.1.length ≤ s.2.2.bits.length := by nlinarith
      omega
    change (Fold.fold step.eval (next s) us).2.1.reverse=_
    rw [ih (next s) (by rw [next_params]; exact hc) hd,next_params,next_acc,next_bits,List.reverse_cons,List.append_assoc]
    simp only [List.length_cons,decode,List.singleton_append,sample_exact s hc he]
 theorem run_exact (p : Count×Count) (bs : Digits) (cs : Count)
    (hc : 2 ^ (p.1.length) ≤ p.2.length) (hl : p.1.length*cs.length ≤ bs.bits.length) :
    run (p,bs,cs)=decode p.1.length cs.length bs.bits := by
  change (Fold.fold step.eval (p,[],bs) cs).2.1.reverse=_
  rw [fold_decode (p,[],bs) cs hc hl]
  rfl
 theorem decode_append (e n : ℕ) (xs ys : List Bool) (hx : xs.length=e) :
    decode e (n+1) (xs++ys)=List.replicate (value xs.reverse) ()::decode e n ys := by
  subst e
  simp only [decode,List.take_left,List.drop_left]
end MeanPayoff.TreeDevice.Certified.Chunks

end

section
namespace MeanPayoff.RandomTree
 theorem bind_congr_all {α β : Type} (t : RandomTree α) (f g : α→RandomTree β)
    (h : t.All (fun a => f a=g a)) : t.bind f=t.bind g := by
  induction t with
  | leaf a => exact h
  | coin l r il ir => exact congrArg₂ coin (il h.1) (ir h.2)
end MeanPayoff.RandomTree
namespace MeanPayoff.TreeDevice.Certified.Chunks
open RandomTree BinaryStack.Addition
 theorem decode_law (e n : ℕ) :
    (FairBits.draw (e*n)).map (decode e n)=RawControl.drawSamples e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show e*(n+1)=e+e*n by ring, FairBits.append]
    simp only [RandomTree.map_bind,RandomTree.map_map,RawControl.drawSamples]
    rw [←FairBits.number e,RandomTree.bind_map]
    apply bind_congr_all
    apply all_mono _ (FairBits.length e)
    intro xs hx
    simp_rw [decode_append e n xs _ hx]
    rw [←RandomTree.map_map,ih]
end MeanPayoff.TreeDevice.Certified.Chunks

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace PostCode
abbrev Input := Digits×Preparation.Aux
noncomputable def samples : Code Input (List Count) :=
  ((snd ≫ₚ fst) ⋏ₚ (fst ≫ₚ Chunks.reverseDigits) ⋏ₚ (snd ≫ₚ snd ≫ₚ fst)) ≫ₚ Chunks.run
noncomputable def start : Code Input (W×RawControl.Acc) := snd ≫ₚ snd ≫ₚ snd
noncomputable def execute : Code Input (W×RawControl.Acc) :=
  (start ≫ₚ fst) ⋏ₚ (((start ≫ₚ snd) ⋏ₚ samples) ≫ₚ RawControl.loop)
noncomputable def returned : Code (W×RawControl.Acc) (W×List W) :=
  fst ⋏ₚ (snd ≫ₚ snd ≫ₚ fst ≫ₚ snd ≫ₚ RawControl.q)
noncomputable def classify : Code (W×List W) (List Bool) :=
  ((fst ≫ₚ Word.half) ⋏ₚ snd) ≫ₚ envMap Word.lt
noncomputable def boolean : Device Compare.bitTree boolData (fun b : Bool => b) :=
  (TreeDevice.branch (TreeDevice.identity Compare.bitTree)
    (TreeDevice.constant Compare.bitTree boolData true)
    (TreeDevice.constant Compare.bitTree boolData false)).extFun (by intro b; cases b <;> rfl)
 theorem boolean_poly : PolynomialCost boolean :=
  PolynomialCost.branch (LinearCost.identity _).polynomial (LinearCost.constant _ _ _).polynomial
    (LinearCost.constant _ _ _).polynomial
noncomputable def digits : Code (List Bool) Digits := by
  let D := Map.device boolean
  refine ⟨Digits.mk,D.recode encode encode _root_.id Digits.mk (fun _ => rfl) (fun _ => ?_),?_⟩
  · simp [encode]
  · obtain ⟨K,d,h⟩ := PolynomialCost.map boolean_poly
    exact ⟨K,d,fun z => h z⟩
noncomputable def run : Code Input Digits := execute ≫ₚ returned ≫ₚ classify ≫ₚ digits
 theorem classify_eval (w : W) (xs : List W) :
    classify (w,xs)=xs.map (fun x => decide (w.val/2<x.val)) := by
  simp only [classify,comp_eval,pair_eval,fst_eval,snd_eval,envMap_eval]
  apply List.map_congr_left
  intro x hx
  change Compare.testPair (Halve.halve w,x)=_
  rw [Compare.testPair_eq,Halve.halve_val]
 theorem returned_eval (w : W) (a : RawControl.Acc) : returned (w,a)=(w,a.2.1.2.q) := rfl
 theorem digits_eval (bs : List Bool) : digits bs=⟨bs⟩ := rfl
 theorem samples_eval (z : Input) : samples z=Chunks.run (z.2.1,⟨z.1.bits.reverse⟩,z.2.2.1) := rfl
 theorem execute_eval (z : Input) : execute z=(z.2.2.2.1,RawControl.loop (z.2.2.2.2,samples z)) := rfl
end PostCode
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.Box5
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (config_ext)
end MeanPayoff.Box5

end

section
namespace MeanPayoff.Emit
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
end MeanPayoff.Emit

end

end OAI
