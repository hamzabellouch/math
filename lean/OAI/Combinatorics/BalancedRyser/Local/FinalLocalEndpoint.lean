import OAI.Combinatorics.BalancedRyser.Local.LocalEndpointCompletion
import OAI.Combinatorics.BalancedRyser.Local.LocalTwoReuseEndpoint

namespace OAI

namespace Balanced.Local

universe u

theorem pencilLocal_proof : PencilLocalResult.{u} :=
  pencilLocal_of_two_reuses pencilTwoReuses_proof

end Balanced.Local

end OAI
