import OAI.NumberTheory.Ostmann.Characters.TemplateInitialUnary
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseReindex

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

theorem initialPhase_reindex {ι κ:Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e:κ≃ι)
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (a:∀i,ZMod (p i)) (s:ℤ) :
    initialPhase (fun i => p (e i)) (fun i => χ (e i)) (fun i => a (e i)) s =
      initialPhase p χ a s := by
  have hh := completePrimePhase_reindex e p χ a
    (fun i => initialKappa (χ i)*(χ i (s:ZMod (p i)))^(-1:ℤ))
    (fun i h => if i=h then 0 else 1) s
  rw [initialPhase_separate,initialPhase_separate]
  simpa only [completePrimePhase,EmbeddingLike.apply_eq_iff_eq] using hh

end Ostmann.Characters.Template

end

end OAI
