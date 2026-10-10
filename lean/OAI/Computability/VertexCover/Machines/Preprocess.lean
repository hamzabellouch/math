import Mathlib
import OAI.Computability.VertexCover.Machines.Regular
import OAI.Computability.VertexCover.Machines.Padding
import OAI.Computability.VertexCover.Machines.Lazy

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                      
section

namespace VertexCover.Machine.PreprocessMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingTables

def overlayInput (H : BaseTable) (T : GraphTables.Table) :
    OverlayMachine.Input (PreprocessingRegularTables.internalDegree+1) PreprocessingRegularTables.internalDegree :=
  ⟨vertices T,padded H T,overlayFamily H T⟩

noncomputable def paddedPoly (H : BaseTable) : Poly tableCode PortMachine.code
    (fun T => (⟨vertices T,padded H T⟩ : PortTables.Input (PreprocessingRegularTables.internalDegree+1))) :=
  (RegularMachine.regularPoly H).comp PaddingMachine.poly

 theorem familyRows (H : BaseTable) (T : GraphTables.Table) :
    (overlayFamily H T).rows.toList.map Fin.val =
      (ExpandMachine.erase (ExpandMachine.paddedFamily H (regularVertices T))).2 := by
  exact congrArg Prod.snd (CloudMachine.erase_resize
    (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices T))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices T))))

noncomputable def familyRowsPoly (H : BaseTable) : Poly tableCode (listBits natBits)
    (fun T => (overlayFamily H T).rows.toList.map Fin.val) := by
  let r : Poly (ExpandMachine.code (q := PreprocessingRegularTables.internalDegree)) (listBits natBits)
      (fun T => (ExpandMachine.erase T).2) :=
    (Poly.snd natBits (listBits natBits)).encodeCongr ExpandMachine.erase (fun _ => rfl) (fun _ => rfl)
  let c := (CloudMachine.regularVerticesPoly.comp (ExpandMachine.paddedFamilyPoly H)).comp r
  exact c.congr (fun T => (familyRows H T).symm)

noncomputable def overlayInputPoly (H : BaseTable) : Poly tableCode OverlayMachine.code (overlayInput H) :=
  ((paddedPoly H).pair (familyRowsPoly H)).encodeCongr id (fun _ => rfl) (fun _ => rfl)

noncomputable def poly (H : BaseTable) : Poly tableCode PortMachine.code (output H) :=
  ((overlayInputPoly H).comp OverlayMachine.poly).comp LazyMachine.poly

end VertexCover.Machine.PreprocessMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
