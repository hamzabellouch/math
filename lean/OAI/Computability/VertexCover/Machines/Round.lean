import Mathlib
import OAI.Computability.VertexCover.Machines.Preprocess
import OAI.Computability.VertexCover.Machines.Power
import OAI.Computability.VertexCover.Machines.Alphabet

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

namespace VertexCover.Machine.RoundMachine
open UniqueGames.Foundations.PCP
open TableMachine
noncomputable def poweredPoly (H : RoundTables.BaseTable) : Poly tableCode GenericMachine.code (RoundTables.powered H) :=
  (PreprocessMachine.poly H).comp (PowerMachine.poly RoundTables.degree_positive RoundTables.walkParameter)
noncomputable def poly (H : RoundTables.BaseTable) : Poly tableCode tableCode (RoundTables.build H) :=
  (poweredPoly H).comp AlphabetMachine.poly
end VertexCover.Machine.RoundMachine
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
