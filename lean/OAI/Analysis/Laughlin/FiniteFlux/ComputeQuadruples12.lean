import OAI.Analysis.Laughlin.FourBody.GramCompute

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_12 : GramCompute.quadruples 12 = [(0,1,2,10), (0,1,3,9), (0,1,4,8), (0,1,5,7), (0,2,3,8), (0,2,4,7), (0,2,5,6), (0,3,4,6), (1,2,3,7), (1,2,4,6), (1,3,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
