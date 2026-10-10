import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePrefix
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTransportActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTransportPrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTransport
open SymbolicHistory TemplateSupportRemoval TemplateOneSidedSupportTelescoping
open TemplateOneSidedRelabel Template Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open OneSidedPhase ParityActions
attribute [local instance] Classical.propDecidable

theorem fullProductMean_hybrid_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (π : ι ≃ κ)
    (S : κ→Finset ℤ) (μ : κ→ℤ→ℝ) (D : ι→Finset (Expr ι))
    (removed : Finset ι) (core : (ι→ℤ)→Prop) (f : (ι→ℤ)→ℂ) :
    fullProductMean S μ (hybridValue (removed.map π.toEmbedding)
      (fun a=>core (fun i=>a (π i))) (familyCoprime (relabelFamilies π D))
      (familyPolynomial (relabelFamilies π D)) (fun a=>f (fun i=>a (π i)))) =
    fullProductMean (fun i=>S (π i)) (fun i=>μ (π i))
      (hybridValue removed core (familyCoprime D) (familyPolynomial D) f) := by
  have hh := congrArg (fullProductMean S μ)
    (funext (hybridValue_relabel π D removed core f))
  exact hh.trans (fullProductMean_reindex π S μ _).symm

theorem fullProductMean_hybrid_relabel_error {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (π : ι ≃ κ)
    (S : κ→Finset ℤ) (μ : κ→ℤ→ℝ) (D : ι→Finset (Expr ι))
    (r₁ r₂ : Finset ι) (core : (ι→ℤ)→Prop) (f : (ι→ℤ)→ℂ) :
    ‖fullProductMean S μ (hybridValue (r₁.map π.toEmbedding)
        (fun a=>core (fun i=>a (π i))) (familyCoprime (relabelFamilies π D))
        (familyPolynomial (relabelFamilies π D)) (fun a=>f (fun i=>a (π i))))-
      fullProductMean S μ (hybridValue (r₂.map π.toEmbedding)
        (fun a=>core (fun i=>a (π i))) (familyCoprime (relabelFamilies π D))
        (familyPolynomial (relabelFamilies π D)) (fun a=>f (fun i=>a (π i))))‖ =
    ‖fullProductMean (fun i=>S (π i)) (fun i=>μ (π i))
        (hybridValue r₁ core (familyCoprime D) (familyPolynomial D) f)-
      fullProductMean (fun i=>S (π i)) (fun i=>μ (π i))
        (hybridValue r₂ core (familyCoprime D) (familyPolynomial D) f)‖ := by
  rw [fullProductMean_hybrid_relabel,fullProductMean_hybrid_relabel]

theorem source_prefix_cmean_error {k Q : ℕ} (cfg : SourceConfiguration k) (m n : ℕ)
    (hm : m ≤ sourceWidth cfg m .word) (bulk top E : Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) (n+1) i))
    (σ : Reassignments k n m)
    (f g : ((schedule k (n+1)).Constituent (sourceWidth cfg m)→PrimeUpTo Q)→ℂ) :
    ‖(constituentPrimePrior (schedule k (n+1)) (sourceWidth cfg m)
        (scheduledPrimeShells k (sourceWidth cfg m)
          (configurationPrimeShells cfg m bulk top E) (n+1)) hE).cmean
        (fun x=>f (constituentAssignment (schedule k (n+1)) (sourceWidth cfg m)
          (prefixConstituentPermutation k n (sourceWidth cfg m) m hm σ) x))-
      (constituentPrimePrior (schedule k (n+1)) (sourceWidth cfg m)
        (scheduledPrimeShells k (sourceWidth cfg m)
          (configurationPrimeShells cfg m bulk top E) (n+1)) hE).cmean
        (fun x=>g (constituentAssignment (schedule k (n+1)) (sourceWidth cfg m)
          (prefixConstituentPermutation k n (sourceWidth cfg m) m hm σ) x))‖ =
    ‖(constituentPrimePrior (schedule k (n+1)) (sourceWidth cfg m)
        (scheduledPrimeShells k (sourceWidth cfg m)
          (configurationPrimeShells cfg m bulk top E) (n+1)) hE).cmean f-
      (constituentPrimePrior (schedule k (n+1)) (sourceWidth cfg m)
        (scheduledPrimeShells k (sourceWidth cfg m)
          (configurationPrimeShells cfg m bulk top E) (n+1)) hE).cmean g‖ := by
  exact constituentPrimePrior_assignment_error _ _ _ hE _
    (source_prefix_shells cfg m n hm bulk top E σ) f g

end Ostmann.Characters.TemplateOneSidedSupportTransport

end

end OAI
