import OAI.Combinatorics.BalancedRyser.Local.LocalEndpointReduction
import OAI.Combinatorics.BalancedRyser.Local.LocalSmallReuseAssembly

namespace OAI

namespace Balanced.Local

universe u

theorem pencilLocal_of_two_reuses
    (hTwo : PencilTwoReusesResult.{u}) : PencilLocalResult.{u} :=
  pencilLocal_of_small_and_two_reuse pencilSmallReuse_proof hTwo

end Balanced.Local

end OAI
