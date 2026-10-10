import OAI.Combinatorics.ContingencyTables.Machines.FiniteEncodedHistory

namespace OAI

/-! # Adaptive histories observed through a projection -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS
open scoped Classical
noncomputable section

/-- Intermediate representations may vary as long as their projected next-step
law agrees and the representation invariant is preserved. -/
theorem projected_foldl_sameLaw {C Z U V : Type*} [Fintype U] [Fintype V]
    (F : C→U→C) (G : Z→V→Z) (e : C→Z) (Valid : C→Prop)
    (hvalid : ∀ c,Valid c→∀ u,Valid (F c u))
    (hstep : ∀ c,Valid c→SameLaw (fun u => e (F c u)) (G (e c)))
    (c : C) (hc : Valid c) (N : ℕ) :
    SameLaw (fun us : Fin N→U => e ((List.ofFn us).foldl F c))
      (fun vs : Fin N→V => (List.ofFn vs).foldl G (e c)) := by
  intro phi
  induction N generalizing c phi with
  | zero => simp only [List.ofFn_zero,List.foldl_nil,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp only [List.ofFn_cons,List.foldl_cons]
    have h := hstep c hc (fun z => uniformAverage (fun vs : Fin N→V =>
      phi ((List.ofFn vs).foldl G z)))
    have hl : uniformAverage (fun u : U => uniformAverage (fun us : Fin N→U =>
        phi (e ((List.ofFn us).foldl F (F c u)))))=
        uniformAverage (fun u : U => uniformAverage (fun vs : Fin N→V =>
          phi ((List.ofFn vs).foldl G (e (F c u))))) := by
      apply congrArg uniformAverage
      funext u
      exact ih (F c u) (hvalid c hc u) phi
    exact hl.trans h

end
end ContingencyTables.FiniteObservableTransport

end OAI
