import OAI.MathematicalPhysics.RapidForcing.Model

namespace OAI

section
open Encodable Nat.Partrec
namespace RapidForcing.EffectiveArithmetic

variable {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]

def runTyped (c : Code) (a : A) : Part B :=
  (c.eval (encode a)).bind (fun n => Part.ofOption (decode n))

lemma partrec_runTyped : Partrec (fun p : Code × A => (runTyped p.1 p.2 : Part B)) :=
  (Code.eval_part.comp Computable.fst (Computable.encode.comp Computable.snd)).bind
    ((Computable.ofOption Computable.decode).comp Computable.snd).to₂

lemma exists_typedCode {f : A → Part B} (hf : Partrec f) :
    ∃ c : Code, ∀ a, c.eval (encode a) = (f a).map encode := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  exact ⟨c, fun a => by simpa using congrFun hc (encode a)⟩

noncomputable def typedCode (f : A → Part B) (hf : Partrec f) : Code :=
  Classical.choose (exists_typedCode hf)

lemma typedCode_eval (f : A → Part B) (hf : Partrec f) (a : A) :
    (typedCode f hf).eval (encode a) = (f a).map encode :=
  Classical.choose_spec (exists_typedCode hf) a

lemma runTyped_typedCode (f : A → Part B) (hf : Partrec f) (a : A) :
    runTyped (typedCode f hf) a = f a := by
  unfold runTyped
  rw [typedCode_eval]
  simp

lemma runTyped_curry (c : Code) (a : A) (b : B) :
    (runTyped (c.curry (encode a)) b : Part C) = runTyped c (a, b) := by
  simp [runTyped, Code.eval_curry, encode_prod_val]

lemma computable_specialize : Computable (fun p : Code × A => p.1.curry (encode p.2)) :=
  Code.primrec₂_curry.to_comp.comp Computable.fst (Computable.encode.comp Computable.snd)

end RapidForcing.EffectiveArithmetic

end

end OAI
