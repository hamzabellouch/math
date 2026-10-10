import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringAddresses
import OAI.Computability.VertexCover.Machines.Walk

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine

namespace FixedSearch

def run {α ι β : Type} (p : α → ι → Bool) (f : α → ι → β) (z : β) : List ι → α → β
  | [], _ => z
  | i::xs, a => if p a i then f a i else run p f z xs a

noncomputable def poly {α ι β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (p : α → ι → Bool) (f : α → ι → β) (z : β)
    (cp : ∀ i, Poly ea boolBits (fun a => p a i))
    (cf : ∀ i, Poly ea eb (fun a => f a i)) :
    (xs : List ι) → Poly ea eb (run p f z xs)
  | [] => Poly.const ea eb z
  | i::xs => (cp i).ite (cf i) (poly ea eb p f z cp cf xs)

 theorem eq_scan {ι β : Type} (p : ι → Prop) [DecidablePred p] (f : ι → β) (z : β) :
    ∀ (xs : List ι) (h : ∃ i ∈ xs, p i),
      run (fun (_ : Unit) i => decide (p i)) (fun _ i => f i) z xs () =
        f (UniqueGames.Foundations.PCP.PoweringLabels.scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons i xs ih =>
    intro h
    by_cases hp : p i
    · simp [run,UniqueGames.Foundations.PCP.PoweringLabels.scanWitness,hp]
    · simp only [run,decide_eq_true_eq,hp,↓reduceIte,
        UniqueGames.Foundations.PCP.PoweringLabels.scanWitness,↓reduceDIte]
      exact ih _

end FixedSearch

namespace AddressMachine
open UniqueGames.Foundations.PCP
open PoweringLabels PoweringAddresses WalkMachine

def search {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label)
    (x : State d × ℕ) : GraphTables.Label :=
  FixedSearch.run (fun x w => decide ((word w.1.val w.2 x.1).2.val=x.2))
    (fun _ w => a w) 0 (allAddresses d t) x

noncomputable def searchPoly {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label) :
    Poly (prodBits (code (d := d)) natBits) finCode (search t a) := by
  exact FixedSearch.poly (prodBits code natBits) finCode _ _ 0
    (fun w => ((((Poly.fst code natBits).comp (wordPoly w.1.val w.2)).comp vertexPoly).pair
      (Poly.snd code natBits)).comp Poly.natEq)
    (fun w => Poly.const _ finCode (a w)) (allAddresses d t)

 theorem search_decode {d : ℕ} (T : PortTables.Input d) (t : ℕ) (v : Fin T.1)
    (u : Ball (PortTables.portGraph T.2) t v) (a : PaddedLabel (Fin d) t GraphTables.Label) :
    search t a ((⟨T,v⟩ : State d),u.val.val) =
      decode (finitePortSelector (PortTables.portGraph T.2) t v) a u := by
  let p := fun w : PortWords (Fin d) t =>
    (wordToBall (PortTables.portGraph T.2) t v w).val = u.val
  have h : ∃ w ∈ allAddresses d t, p w := by
    obtain ⟨w,hw⟩ := wordToBall_surjective (PortTables.portGraph T.2) t v u
    exact ⟨w,mem_allAddresses d t w,congrArg Subtype.val hw⟩
  have hs := FixedSearch.eq_scan p a 0 (allAddresses d t) h
  change _ = a (scanWitness p (allAddresses d t) h).val
  rw [← hs]
  unfold search
  generalize allAddresses d t = xs
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    dsimp only [FixedSearch.run]
    have hp : decide ((word w.1.val w.2 (⟨T,v⟩ : State d)).2.val = u.val.val) = decide (p w) := by
      simp only [p,word,wordToBall,Fin.val_inj]
      rfl
    exact if_congr (Iff.of_eq (congrArg (fun c : Bool => c=true) hp))
      rfl ih

end AddressMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
