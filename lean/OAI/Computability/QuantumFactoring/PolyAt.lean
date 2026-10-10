import Mathlib
import OAI.Computability.QuantumFactoring.PolyBounds

namespace OAI



section

namespace ExactQuantumFactoring
/-- Uniform polynomial bounds over arbitrary auxiliary parameters. Only the
chosen length is charged, so this also records worst-case bounds over all
finite loop indices and all networks satisfying a supplied count invariant. -/
def PolyAt {α : Sort*} (length : α→ℕ) (f : α→ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ a,f a≤p.eval (length a)
namespace PolyAt
variable {α : Sort*} {len f g : α→ℕ}
lemma const (len : α→ℕ) (c : ℕ) : PolyAt len (fun _=>c) :=
  ⟨Polynomial.C c,fun _=>by simp⟩
lemma self (len : α→ℕ) : PolyAt len len := ⟨Polynomial.X,fun _=>by simp⟩
lemma add (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a+g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p+q,fun a=>by simpa using Nat.add_le_add (hp a) (hq a)⟩
lemma mul (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>f a*g a) := by
  obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg
  exact ⟨p*q,fun a=>by simpa using Nat.mul_le_mul (hp a) (hq a)⟩
lemma pow (hf : PolyAt len f) (k : ℕ) : PolyAt len (fun a=>f a^k) := by
  obtain ⟨p,hp⟩:=hf
  exact ⟨p^k,fun a=>by simpa using Nat.pow_le_pow_left (hp a) k⟩
lemma of_le (hg : PolyAt len g) (h : ∀a,f a≤g a) : PolyAt len f := by
  obtain ⟨p,hp⟩:=hg
  exact ⟨p,fun a=>(h a).trans (hp a)⟩
lemma sub (hf : PolyAt len f) : PolyAt len (fun a=>f a-g a) := hf.of_le fun _=>Nat.sub_le _ _
lemma div (hf : PolyAt len f) : PolyAt len (fun a=>f a/g a) := hf.of_le fun _=>Nat.div_le_self _ _
lemma mod (hf : PolyAt len f) : PolyAt len (fun a=>f a%g a) := hf.of_le fun _=>Nat.mod_le _ _
lemma max (hf : PolyAt len f) (hg : PolyAt len g) : PolyAt len (fun a=>max (f a) (g a)) :=
  (hf.add hg).of_le fun _=>Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩
lemma ite (p : α→Prop) [∀a,Decidable (p a)] (hf : PolyAt len f) (hg : PolyAt len g) :
    PolyAt len (fun a=>if p a then f a else g a) :=
  (hf.max hg).of_le fun a=>by split_ifs <;> omega
lemma pull {β : Sort*} (hf : PolyAt len f) (g : β→α) :
    PolyAt (fun b=>len (g b)) (fun b=>f (g b)) := by
  obtain ⟨p,hp⟩:=hf; exact ⟨p,fun b=>hp (g b)⟩
lemma ofPoly {f : ℕ→ℕ} (hf : PolyBound f) (len : α→ℕ) :
    PolyAt len (fun a=>f (len a)) := PolyAt.pull hf len
lemma comp {h : ℕ→ℕ} (hh : PolyBound h) (hf : PolyAt len f) :
    PolyAt len (fun a=>h (f a)) := by
  obtain ⟨p,hp⟩:=hh; obtain ⟨q,hq⟩:=hf
  refine ⟨p.comp q,fun a=>?_⟩
  simpa only [Polynomial.eval_comp] using
    (hp (f a)).trans (PolyBound.eval_mono p (hq a))
lemma natSize (hf : PolyAt len f) : PolyAt len (fun a=>(f a).size) :=
  hf.of_le fun _=>Nat.size_le.mpr Nat.lt_two_pow_self
end PolyAt

syntax "poly_at" : tactic
macro_rules
  | `(tactic| poly_at) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact PolyAt.self _
    | exact PolyAt.const _ _
    | (apply PolyAt.add <;> poly_at)
    | (apply PolyAt.mul <;> poly_at)
    | (apply PolyAt.pow <;> poly_at)
    | (apply PolyAt.max <;> poly_at)
    | (apply PolyAt.sub <;> poly_at)
    | (apply PolyAt.div <;> poly_at)
    | (apply PolyAt.mod <;> poly_at)
    | (apply PolyAt.natSize <;> poly_at))
end ExactQuantumFactoring

end



end OAI
