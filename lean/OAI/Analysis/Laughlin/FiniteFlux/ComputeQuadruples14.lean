import OAI.Analysis.Laughlin.FourBody.GramCompute

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_14 : GramCompute.quadruples 14 = [(0,1,2,12), (0,1,3,11), (0,1,4,10), (0,1,5,9), (0,1,6,8), (0,2,3,10), (0,2,4,9), (0,2,5,8), (0,2,6,7), (0,3,4,8), (0,3,5,7), (0,4,5,6), (1,2,3,9), (1,2,4,8), (1,2,5,7), (1,3,4,7), (1,3,5,6), (2,3,4,6)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
