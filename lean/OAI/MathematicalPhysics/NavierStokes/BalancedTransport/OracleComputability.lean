import Mathlib

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Encodable
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
variable {O : Set (ℕ →. ℕ)}

lemma computableIn_of_eq {f g : α → β} (hf : ComputableIn O f)
    (h : ∀ a, f a = g a) : ComputableIn O g := (funext h) ▸ hf

lemma computableIn_pair {f : α → β} {g : α → γ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O (fun a => (f a, g a)) := by
  apply Nat.RecursiveIn.of_eq (Nat.RecursiveIn.pair hf hg)
  intro n
  cases decode (α := α) n <;> simp [Seq.seq]

lemma computableIn_comp {f : β → γ} {g : α → β} (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O (fun a => f (g a)) := by
  apply Nat.RecursiveIn.of_eq (Nat.RecursiveIn.comp hf hg)
  intro n
  cases decode (α := α) n <;> simp

lemma computableIn_comp₂ {δ : Type*} [Primcodable δ] {f : β → γ → δ}
    {g : α → β} {h : α → γ} (hf : ComputableIn₂ O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O (fun a => f (g a) (h a)) :=
  computableIn_comp hf (computableIn_pair hg hh)

lemma computableIn_fin_triple (f g h : α → β) (hf : ComputableIn O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O (fun a => ![f a, g a, h a]) := by
  have hv : Primrec₂ (fun i : Fin 3 => fun p : β × β × β => (![p.1, p.2.1, p.2.2] : Fin 3 → β) i) := by
    apply Primrec.fin_curry₁.mpr
    intro i
    fin_cases i
    · exact Primrec.fst
    · exact Primrec.fst.comp Primrec.snd
    · exact Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : β × β × β => ![p.1, p.2.1, p.2.2]) :=
    Primrec.fin_curry.mpr (hv.comp Primrec.snd Primrec.fst)
  exact computableIn_comp hc.computableIn (computableIn_pair hf (computableIn_pair hg hh))

lemma computableIn_fin_eval {n : ℕ} {f : α → (Fin n → β)} (hf : ComputableIn O f)
    (i : Fin n) : ComputableIn O (fun a => f a i) :=
  computableIn_comp (Primrec.fin_app.comp Primrec.id (Primrec.const i)).computableIn hf

end BalancedTransport.Effectivity
end

end OAI
