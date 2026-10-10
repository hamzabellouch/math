import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport

namespace OAI

/-! # Observable laws under adaptive finite-word calls

The stored state may include rational estimates and is not assumed
finite. Each fresh word is finite; equality of every conditional call
therefore suffices for equality of the entire executed history.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section

variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

theorem SameLaw.bind {f : X → Z} {g : Y → Z} (hfg : SameLaw f g)
    (F : Z → U → W) (G : Z → V → W) (h : ∀ z,SameLaw (F z) (G z)) :
    SameLaw (fun xu : X × U => F (f xu.1) xu.2)
      (fun yv : Y × V => G (g yv.1) yv.2) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hi (x : X) := h (f x) phi
  simp_rw [hi]
  exact hfg (fun z => uniformAverage (fun v : V => phi (G z v)))

def adaptiveRun (step : Z → X → Z) (z : Z) : (N : ℕ) → (Fin N → X) → Z
  | 0,_ => z
  | N+1,xs => adaptiveRun step (step z (xs 0)) N (Fin.tail xs)

theorem adaptiveRun_sameLaw (F : Z → X → Z) (G : Z → Y → Z)
    (h : ∀ z,SameLaw (F z) (G z)) (z : Z) (N : ℕ) :
    SameLaw (adaptiveRun F z N) (adaptiveRun G z N) := by
  intro phi
  induction N generalizing z with
  | zero => simp only [adaptiveRun,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp only [adaptiveRun,Fin.cons_zero,Fin.tail_cons]
    have hi (x : X) := ih (F z x)
    simp_rw [hi]
    exact h z (fun next => uniformAverage (fun ys : Fin N → Y =>
      phi (adaptiveRun G next N ys)))

def appendStep (step : List Z → X → Z) (history : List Z) (x : X) : List Z :=
  history++[step history x]

theorem appendStep_sameLaw (F : List Z → X → Z) (G : List Z → Y → Z)
    (h : ∀ history,SameLaw (F history) (G history)) (history : List Z) :
    SameLaw (appendStep F history) (appendStep G history) :=
  (h history).map (fun z => history++[z])

/-- This transports complete stored histories, hence also every final
estimate and every abort event obtained from that history. -/
theorem adaptiveHistory_sameLaw (F : List Z → X → Z) (G : List Z → Y → Z)
    (h : ∀ history,SameLaw (F history) (G history)) (history : List Z) (N : ℕ) :
    SameLaw (adaptiveRun (appendStep F) history N)
      (adaptiveRun (appendStep G) history N) :=
  adaptiveRun_sameLaw _ _ (appendStep_sameLaw F G h) history N

end
end ContingencyTables.FiniteObservableTransport

end OAI
