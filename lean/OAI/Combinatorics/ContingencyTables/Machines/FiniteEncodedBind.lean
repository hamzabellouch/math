import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent

namespace OAI

/-! # Composing exact laws through a noninjective state encoding -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped Classical
noncomputable section

theorem encoded_bind {A B U V C Z W : Type*}
    [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    (f : A → C) (g : B → Z) (e : Z → C) (F : C → U → W) (G : Z → V → W)
    (hinit : SameLaw f (fun b => e (g b))) (hstep : ∀ z,SameLaw (F (e z)) (G z)) :
    SameLaw (fun p : A×U => F (f p.1) p.2) (fun p : B×V => G (g p.1) p.2) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hi := hinit (fun c => uniformAverage (fun u : U => phi (F c u)))
  refine hi.trans ?_
  apply congrArg uniformAverage
  funext b
  exact hstep (g b) phi

theorem flat_encoded_bind {C Z W : Type*} (a b c d : ℕ)
    (f : (Fin a → Bool) → C) (g : (Fin c → Bool) → Z) (e : Z → C)
    (F : C → (Fin b → Bool) → W) (G : Z → (Fin d → Bool) → W)
    (hinit : SameLaw f (fun bits => e (g bits))) (hstep : ∀ z,SameLaw (F (e z)) (G z)) :
    SameLaw (fun bits : Fin (a+b) → Bool =>
      F (f (splitWordEquiv a b bits).1) (splitWordEquiv a b bits).2)
      (fun bits : Fin (c+d) → Bool =>
        G (g (splitWordEquiv c d bits).1) (splitWordEquiv c d bits).2) := by
  have h := encoded_bind f g e F G hinit hstep
  intro phi
  have hl := uniformAverage_equiv (splitWordEquiv a b)
    (fun p : (Fin a → Bool)×(Fin b → Bool) => phi (F (f p.1) p.2))
  have hr := uniformAverage_equiv (splitWordEquiv c d)
    (fun p : (Fin c → Bool)×(Fin d → Bool) => phi (G (g p.1) p.2))
  exact hl.trans ((h phi).trans hr.symm)

end
end ContingencyTables.FiniteObservableTransport

end OAI
