import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by720_721 : By passesAt 720 721 := by
  apply byRun passesAt 720 1 721
  · rfl
  decide +kernel
end GeneralMahler.SCal.Grid.Nodes

end OAI
