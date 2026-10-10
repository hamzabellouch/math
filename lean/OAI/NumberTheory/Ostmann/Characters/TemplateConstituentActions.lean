import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalUnitRoot

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def constituentAssignment {Q : ℕ} (T : Layout) (width : Role → ℕ)
    (e : Equiv.Perm (T.Constituent width)) :
    (T.Constituent width → PrimeUpTo Q) ≃ (T.Constituent width → PrimeUpTo Q) where
  toFun x i := x (e.symm i)
  invFun x i := x (e i)
  left_inv x := by funext i; exact congrArg x (e.symm_apply_apply i)
  right_inv x := by funext i; exact congrArg x (e.apply_symm_apply i)

theorem constituentPrimePrior_mass_assignment {Q : ℕ} (T : Layout) (width : Role → ℕ)
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (e : Equiv.Perm (T.Constituent width)) (he : ∀i,E (e i)=E i)
    (x : T.Constituent width → PrimeUpTo Q) :
    (constituentPrimePrior T width E hE).mass (constituentAssignment T width e x)=
      (constituentPrimePrior T width E hE).mass x := by
  have he' (i : T.Constituent width) : E (e.symm i)=E i := by
    simpa only [e.apply_symm_apply] using (he (e.symm i)).symm
  change (∏i,(primeShellPrior (E i) (hE i)).mass (x (e.symm i)))=
    ∏i,(primeShellPrior (E i) (hE i)).mass (x i)
  have hp := e.symm.prod_comp (fun i => (primeShellPrior (E i) (hE i)).mass (x i))
  simpa only [primeShellPrior_mass,he'] using hp

theorem constituentPrimePrior_mean_assignment {Q : ℕ} (T : Layout) (width : Role → ℕ)
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (e : Equiv.Perm (T.Constituent width)) (he : ∀i,E (e i)=E i)
    (f : (T.Constituent width → PrimeUpTo Q) → ℝ) :
    (constituentPrimePrior T width E hE).mean (fun x => f (constituentAssignment T width e x))=
      (constituentPrimePrior T width E hE).mean f := by
  have hh := (constituentAssignment (Q:=Q) T width e).sum_comp
    (fun x => (constituentPrimePrior T width E hE).mass x*f x)
  simpa only [FinitePrior.mean,FinitePrior.cmean,constituentPrimePrior_mass_assignment T width E hE e he] using hh

theorem constituentPrimePrior_cmean_assignment {Q : ℕ} (T : Layout) (width : Role → ℕ)
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (e : Equiv.Perm (T.Constituent width)) (he : ∀i,E (e i)=E i)
    (f : (T.Constituent width → PrimeUpTo Q) → ℂ) :
    (constituentPrimePrior T width E hE).cmean (fun x => f (constituentAssignment T width e x))=
      (constituentPrimePrior T width E hE).cmean f := by
  have hh := (constituentAssignment (Q:=Q) T width e).sum_comp
    (fun x => ((constituentPrimePrior T width E hE).mass x:ℂ)*f x)
  simpa only [FinitePrior.mean,FinitePrior.cmean,constituentPrimePrior_mass_assignment T width E hE e he] using hh

end Ostmann.Characters.Template

end

end OAI
