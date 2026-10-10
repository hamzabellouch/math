import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical Matrix
variable {R : Type} [CommRing R] {k : Kind} {d e : LocalRanks k}
def columnCongr (h : d=e) (p : k.table.Port) : d.Columns p ≃ e.Columns p :=
  Equiv.sigmaCongr (Equiv.refl _) (fun c => finCongr (congrArg (fun z : LocalRanks k => z.rank p (some c)) h))
def parentCongr (h : d=e) (p : k.table.Port) : d.Parent p ≃ e.Parent p :=
  finCongr (congrArg (fun z : LocalRanks k => z.rank p none) h)
lemma transportFrames_reindex (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p)) (p : k.table.Port) :
    (transportFrames h f p).reindex (columnCongr h p) (parentCongr h p)=f p := by
  subst e
  have hc : columnCongr (d:=d) rfl p=Equiv.refl _ := Equiv.ext (fun _ => rfl)
  have hp : parentCongr (d:=d) rfl p=Equiv.refl _ := by ext i; rfl
  rw [hc,hp]
  exact MatrixIso.reindex_refl_eq _
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
end

end OAI
