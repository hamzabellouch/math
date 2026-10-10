import OAI.Computability.DegreeRigidity.Syntax.BoundedCertificate
import OAI.Computability.DegreeRigidity.SetModels.InternalNameValidity
import OAI.Computability.DegreeRigidity.Syntax.SigmaSyntax
import OAI.Computability.DegreeRigidity.CohenForcing.SigmaForcing

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u

namespace SigmaCode

def forcing : SigmaFormula → ℕ → ℕ → ℕ → (ℕ → ℕ) → SigmaFormula
  | .bounded φ, ci,oi,pi,v => CertificateCode.certificate φ ci oi pi v
  | .existsSet φ, ci,oi,pi,v => .existsSet
      (SigmaFormula.conj (NameValidity.Code.valid (ci+1) 0)
        (forcing φ (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1))))
end SigmaCode

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem realize_sigmaForcing (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {o : ZFSet.{u}}
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (henv : ∀ i, env i ∈ M)
    (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (SigmaCode.forcing φ ci oi pi v).Realize M env ↔ SigmaForces M e φ p := by
  induction φ generalizing e env ci oi pi v with
  | bounded φ =>
    exact realize_boundedCertificate M hM hP hU hPow hS hR hI ho φ e p env henv ci oi pi v hc ho' hp hv
  | existsSet φ ih =>
    have henv' (x : ZFSet.{u}) (hx : x ∈ M) : ∀ i, cons x env i ∈ M := by
      intro i; cases i <;> simp only [cons_zero,cons_succ]; exact hx; exact henv _
    have valid (x : ZFSet.{u}) (hx : x ∈ M) :
        (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
          ∃ a : Name (Conditions c), a.encode (label c) = x := by
      have h := NameValidity.realize_valid M hM hP hU hPow hS hR hI
        (cons x env) (henv' x hx) (ci+1) 0
      change (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
        (∃ a : Name (Conditions (env ci)), a.encode (label (env ci)) = x) at h
      rw [hc] at h
      exact h
    have sub (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :=
      ih (push a e) (cons (a.encode (label c)) env) (henv' _ ha)
        (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1)) hc ho' hp
        (by intro i; cases i <;> simp only [push_zero,push_succ,cons_zero,cons_succ,hv])
    simp only [SigmaCode.forcing,SigmaFormula.Realize,SigmaFormula.realize_conj]
    constructor
    · rintro ⟨x,hx,hvalid,hforce⟩
      obtain ⟨a,rfl⟩ := (valid x hx).mp hvalid
      exact ⟨a,hx,(sub a hx).mp hforce⟩
    · rintro ⟨a,ha,hforce⟩
      exact ⟨_,ha,(valid _ ha).mpr ⟨a,rfl⟩,(sub a ha).mpr hforce⟩

end TuringRigidity.BoundedForcing

end OAI
