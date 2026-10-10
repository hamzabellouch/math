import OAI.Combinatorics.ParityLifts.RaceBounds

namespace OAI

namespace ParityWL.Complexity

def ParamPolyProgram.post {ρ α β γ : Type} [TreeCodec ρ] [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : ρ → α → β} {g : β → γ} (P : ParamPolyProgram ρ α β f) (Q : PolyProgram β γ g) :
    ParamPolyProgram ρ α γ (fun r x => g (f r x)) :=
  P.comp (ParamPolyProgram.ofPoly (f := fun (_ : ρ) b => g b) ((PolyProgram.snd ρ β).comp Q))

def ParamPolyProgram.lift {ρ α β : Type} [TreeCodec ρ] [TreeCodec α] [TreeCodec β]
    {f : α → β} (P : PolyProgram α β f) : ParamPolyProgram ρ α β (fun _ x => f x) :=
  ParamPolyProgram.ofPoly (f := fun (_ : ρ) x => f x) ((PolyProgram.snd ρ α).comp P)

def ParamPolyProgram.parameter (ρ α : Type) [TreeCodec ρ] [TreeCodec α] :
    ParamPolyProgram ρ α ρ (fun r _ => r) :=
  .ofPoly (f := fun r (_ : α) => r) (PolyProgram.fst ρ α)

end ParityWL.Complexity

end OAI
