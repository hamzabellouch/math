import OAI.Combinatorics.ContingencyTables.Transport.FiniteProjectedHistory

namespace OAI

/-! # Projected adaptive laws up to the prescribed number of phases -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS
open scoped Classical
noncomputable section

theorem bounded_projected_foldl_sameLaw {C Z U V : Type*} [Fintype U] [Fintype V]
    (F : C→U→C) (G : Z→V→Z) (e : C→Z) (Valid : C→Prop)
    (size : C→ℕ) (H : ℕ)
    (hsize : ∀ c u,size (F c u)=size c+1)
    (hvalid : ∀ c,Valid c→size c<H→∀ u,Valid (F c u))
    (hstep : ∀ c,Valid c→size c<H→SameLaw (fun u => e (F c u)) (G (e c)))
    (c : C) (hc : Valid c) (N : ℕ) (hN : size c+N≤H) :
    SameLaw (fun us : Fin N→U => e ((List.ofFn us).foldl F c))
      (fun vs : Fin N→V => (List.ofFn vs).foldl G (e c)) := by
  intro phi
  induction N generalizing c phi with
  | zero => simp only [List.ofFn_zero,List.foldl_nil,uniformAverage_const]
  | succ N ih =>
    have hlt : size c<H := by omega
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp only [List.ofFn_cons,List.foldl_cons]
    have h := hstep c hc hlt (fun z => uniformAverage (fun vs : Fin N→V =>
      phi ((List.ofFn vs).foldl G z)))
    have hl : uniformAverage (fun u : U => uniformAverage (fun us : Fin N→U =>
        phi (e ((List.ofFn us).foldl F (F c u)))))=
        uniformAverage (fun u : U => uniformAverage (fun vs : Fin N→V =>
          phi ((List.ofFn vs).foldl G (e (F c u))))) := by
      apply congrArg uniformAverage
      funext u
      apply ih (F c u) (hvalid c hc hlt u)
      rw [hsize]
      omega
    exact hl.trans h

end
end ContingencyTables.FiniteObservableTransport

end OAI
