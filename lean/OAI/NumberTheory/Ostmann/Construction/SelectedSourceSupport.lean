import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

lemma initialSourceValue_rel_nonbulk {α β : Type*} (b k : ℕ) (a : α) (a' : β)
    (top : Fin 3 → α) (top' : Fin 3 → β) (comp : Fin k → Fin 2 → α)
    (comp' : Fin k → Fin 2 → β) (R : α → β → Prop)
    (htop : ∀i,R (top i) (top' i)) (hcomp : ∀j i,R (comp j i) (comp' j i))
    (origin : ℕ) (hlo : 2*b≤origin) (hhi : origin<2*b+6+4*k) :
    R (initialSourceValue b k a top comp origin) (initialSourceValue b k a' top' comp' origin) := by
  unfold initialSourceValue
  split_ifs with hb ht hj
  · omega
  · exact htop _
  · exact hcomp _ _
  · omega

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem source_log_support (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ℕ) (hlo : 2*(Conclusion.bulkSize k L/2)≤origin)
    (hhi : origin<2*(Conclusion.bulkSize k L/2)+6+4*k)
    (p : (C.sources origin).Sample) (hp : (C.sources origin).law.mass p≠0) :
    |Real.log (p:ℕ)-C.cells.center (Conclusion.bulkSize k L/2) origin|<1 := by
  have h := initialSourceValue_rel_nonbulk (Conclusion.bulkSize k L/2) k C.bulk (0:ℝ)
    (C.cells.topSource E C.deleted_card) (fun i => (C.cells.top i:ℝ))
    (C.cells.compSource E C.deleted_card) (fun j i => (C.cells.comp j i:ℝ))
    (fun (S : PrimeSource) c => ∀p:S.Sample,S.law.mass p≠0 → |Real.log (p:ℕ)-c|<1)
    (fun i p hp => logCellPrimeSource_log_support _ E
      (C.cells.top_balanced i E C.deleted_card).choose p hp)
    (fun j i p hp => logCellPrimeSource_log_support _ E
      (C.cells.comp_balanced j i E C.deleted_card).choose p hp)
    origin hlo hhi
  exact h p hp

theorem giant_log_support (C : InitialSourceChoice d Bs BD Bz k L E)
    (p : C.giant.Sample) (hp : C.giant.law.mass p≠0) :
    |Real.log (p:ℕ)-(C.giantCenter:ℝ)|<1 :=
  logCellPrimeSource_log_support _ ∅ C.giantPositive p hp

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
