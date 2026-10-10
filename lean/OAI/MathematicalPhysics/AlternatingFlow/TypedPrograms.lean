import OAI.MathematicalPhysics.AlternatingFlow.RecursiveBounds

namespace OAI

section TypedProgramsDevelopment

namespace AlternatingNS.Effective

open Encodable

def execute {A B : Type*} [Encodable A] [Encodable B] (c : Program) (a : A) : Part B :=
  (c.eval (encode a)).bind (fun n => Part.ofOption (decode n))

lemma execute_partrec {A B : Type*} [Primcodable A] [Primcodable B] :
    Partrec₂ (@execute A B _ _) := by
  exact (Nat.Partrec.Code.eval_part.comp Computable.fst
    (Computable.encode.comp Computable.snd)).bind
    (Computable.ofOption (Computable.decode.comp Computable.snd))

lemma typed_fixedpoint {A B : Type*} [Primcodable A] [Primcodable B]
    (F : Program → A → Part B) (hF : Partrec₂ F) :
    ∃ c : Program, ∀ a, execute c a = F c a := by
  let G (c : Program) (n : ℕ) : Part ℕ :=
    (Part.ofOption (decode n)).bind (fun a : A => (F c a).map encode)
  have hG : Partrec₂ G := (Computable.ofOption (Computable.decode.comp Computable.snd)).bind
    ((hF.comp (Computable.fst.comp Computable.fst) Computable.snd).map
      (Computable.encode.comp Computable.snd))
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hG
  refine ⟨c, fun a => ?_⟩
  simp [execute, hc, G, Part.bind_map]

lemma computable_of_execute {A B : Type*} [Primcodable A] [Primcodable B]
    (c : Program) (f : A → B) (h : ∀ a, f a ∈ execute c a) : Computable f :=
  (execute_partrec.comp (Computable.const c) Computable.id).of_eq_tot h

lemma partrec_ite {A B : Type*} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : Computable (fun a => decide (p a)))
    (f g : A → Part B) (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun a => if p a then f a else g a) := by
  
  obtain ⟨cf,hcf⟩ := Nat.Partrec.Code.exists_code.mp hf
  obtain ⟨cg,hcg⟩ := Nat.Partrec.Code.exists_code.mp hg
  have hr : Partrec (fun a => execute (B := B) (if p a then cf else cg) a) :=
    execute_partrec.comp ((Computable.cond hp (Computable.const cf) (Computable.const cg)).of_eq
      (by simp)) Computable.id
  apply hr.of_eq
  intro a
  split_ifs <;> simp [execute, hcf, hcg, encodek, Part.bind_map]

lemma binary_recursive_program {A B : Type*} [Primcodable A] [Primcodable B]
    (p : A → Prop) [DecidablePred p] (hp : Computable (fun a => decide (p a)))
    (base : A → B) (hb : Computable base) (left right : A → A)
    (hl : Computable left) (hr : Computable right)
    (op : A × B × B → B) (ho : Computable op) :
    ∃ c : Program, ∀ a, execute c a =
      if p a then Part.some (base a) else
        (execute c (left a)).bind (fun u => (execute c (right a)).map (fun v => op (a,u,v))) := by
  let F (c : Program) (a : A) : Part B := if p a then Part.some (base a) else
    (execute c (left a)).bind (fun u => (execute c (right a)).map (fun v => op (a,u,v)))
  apply typed_fixedpoint F
  apply partrec_ite (p := fun z : Program × A => p z.2) (hp.comp Computable.snd)
  · exact hb.comp Computable.snd
  · have hrec₁ : Partrec (fun z : Program × A => execute (B := B) z.1 (left z.2)) :=
      execute_partrec.comp Computable.fst (hl.comp Computable.snd)
    have hrec₂ : Partrec (fun z : (Program × A) × B => execute (B := B) z.1.1 (right z.1.2)) :=
      execute_partrec.comp (Computable.fst.comp Computable.fst) (hr.comp (Computable.snd.comp Computable.fst))
    exact hrec₁.bind (hrec₂.map (ho.comp
      ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))))

end AlternatingNS.Effective

end TypedProgramsDevelopment

end OAI
