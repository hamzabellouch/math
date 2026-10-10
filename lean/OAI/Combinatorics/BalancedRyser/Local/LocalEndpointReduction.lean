import OAI.Combinatorics.BalancedRyser.Incidence.PencilReuseEndpoint
import OAI.Combinatorics.BalancedRyser.Local.LocalEndpointAssembly

namespace OAI

namespace Balanced.Local

universe u

theorem pencilLocal_of_small_and_two_reuse
    (hSmall : PencilSmallReuseResult.{u})
    (hTwo : PencilTwoReusesResult.{u}) : PencilLocalResult.{u} :=
  pencilLocal_of_three_reuse_estimates pencilReuse_proof hSmall hTwo

end Balanced.Local

end OAI
