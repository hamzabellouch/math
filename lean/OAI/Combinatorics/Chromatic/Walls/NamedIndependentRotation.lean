import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IndependentRotationComparison
import OAI.Combinatorics.Chromatic.QuantumTorus.IndependentElementReindex

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
open Classical
noncomputable section
variable {K M V : Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (ell : M →+ ℤ) (p : M) (hp : ell p=1)

include hΩ in
lemma independentElement_named_rotation (w : V → M) (a b c : V)
    (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    (hwb : w b=w a+p) (hpa : Ω p (w a)=1) (hpc : Ω p (w c)= -1)
    (hac0 : Ω (w a) (w c)=0) (hw : ∀x,x≠a → x≠b → x≠c → Ω p (w x)=0) (k : ℕ) :
    pureAction v (complementOmega ell Ω) (complementAlpha ell p Ω)
      (embed v Ω hΩ ell p hp (independentElement v Ω (Function.update w b (w c+p)) k)) =
      embed v Ω hΩ ell p hp (independentElement v Ω w k) := by
  let e : Fin 3 ↪ V := ⟨![a,b,c],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let W := {x : V // x∉Set.range e}
  let eqv := embeddingSumCompl e
  let outside : W → M := fun x=>w x.val
  have ho : ∀x:W, x.val≠a ∧ x.val≠b ∧ x.val≠c := by
    intro x
    refine ⟨?_,?_,?_⟩
    · intro h; exact x.property ⟨0,h.symm⟩
    · intro h; exact x.property ⟨1,h.symm⟩
    · intro h; exact x.property ⟨2,h.symm⟩
  have hold : w ∘ eqv=Sum.elim ![w a,w a+p,w c] outside := by
    funext x
    cases x with
    | inl i =>
      change w (![a,b,c] i)=![w a,w a+p,w c] i
      fin_cases i <;> simp [hwb]
    | inr x => rfl
  have hnew : (Function.update w b (w c+p)) ∘ eqv=
      Sum.elim ![w a,w c+p,w c] outside := by
    funext x
    cases x with
    | inl i =>
      change Function.update w b (w c+p) (![a,b,c] i)=![w a,w c+p,w c] i
      fin_cases i <;> simp [hab,Ne.symm hbc]
    | inr x =>
      change Function.update w b (w c+p) x.val=w x.val
      exact Function.update_of_ne (ho x).2.1 _ _
  rw [independentElement_reindex v Ω (Function.update w b (w c+p)) eqv k,
    independentElement_reindex v Ω w eqv k,hnew,hold]
  exact independentElement_rotation v Ω hΩ ell p hp (w a) (w c) hpa hpc hac0 outside
    (fun x=>hw x.val (ho x).1 (ho x).2.1 (ho x).2.2) k
end
end ElementaryPositivity.RationalFiber

end

end OAI
