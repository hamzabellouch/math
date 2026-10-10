import OAI.Analysis.Laughlin.FourBody.GramCompute

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_13 : GramCompute.quadruples 13 = [(0,1,2,11), (0,1,3,10), (0,1,4,9), (0,1,5,8), (0,1,6,7), (0,2,3,9), (0,2,4,8), (0,2,5,7), (0,3,4,7), (0,3,5,6), (1,2,3,8), (1,2,4,7), (1,2,5,6), (1,3,4,6), (2,3,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
