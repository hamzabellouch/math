import Mathlib

namespace OAI

namespace SimpleFInftyOvergroups.EffectiveNames.Finite
variable {A B P : Type*} {n : ℕ}

def traverse (f : A → Part B) (x : Fin n → A) : Part (Fin n → B) :=
  (List.Vector.mOfFn (fun i => f (x i))).map List.Vector.get

theorem vector_full (f : Fin n → Part B) (g : Fin n → B) (h : ∀ i, g i ∈ f i) :
    List.Vector.ofFn g ∈ List.Vector.mOfFn f := by
  induction n with
  | zero => exact Part.mem_some _
  | succ n ih =>
    simp only [List.Vector.mOfFn]
    refine Part.mem_bind_iff.mpr ⟨g 0, h 0, ?_⟩
    exact Part.mem_bind_iff.mpr ⟨_,ih (fun i => f i.succ) (fun i => g i.succ)
      (fun i => h i.succ), Part.mem_some _⟩

theorem traverse_full (f : A → Part B) (g : A → B) (x : Fin n → A)
    (h : ∀ i, g (x i) ∈ f (x i)) : (fun i => g (x i)) ∈ traverse f x := by
  change _ ∈ (List.Vector.mOfFn (fun i => f (x i))).map List.Vector.get
  convert Part.mem_map List.Vector.get (vector_full (fun i => f (x i)) (fun i => g (x i)) h) using 1
  funext i
  exact (List.Vector.get_ofFn (fun i => g (x i)) i).symm

variable [Primcodable A] [Primcodable B] [Primcodable P]

 theorem partrec_traverse {f : P → A → Part B} (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => traverse (n:=n) (f p)) := by
  have hh : ∀ i : Fin n, Partrec (fun p : P × (Fin n → A) => f p.1 (p.2 i)) :=
    fun i => hf.comp Computable.fst (Primrec.fin_app.to_comp.comp Computable.snd (Computable.const i))
  exact (Partrec.vector_mOfFn hh).map (Primrec.vector_get'.to_comp.comp Computable.snd).to₂

 theorem computable_function {f : P → Fin n → B} (hf : ∀ i, Computable (fun p => f p i)) :
    Computable f := by
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hf)).of_eq
    (fun p => by funext i; simp)

 theorem primrec_function {f : P → Fin n → B} (hf : ∀ i, Primrec (fun p => f p i)) :
    Primrec f := by
  exact (Primrec.vector_get'.comp (Primrec.vector_ofFn hf)).of_eq
    (fun p => by funext i; simp)
end SimpleFInftyOvergroups.EffectiveNames.Finite

end OAI
