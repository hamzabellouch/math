import OAI.Analysis.Laughlin.FourBody.GramCompute

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_16 : GramCompute.quadruples 16 = [(0,1,2,14), (0,1,3,13), (0,1,4,12), (0,1,5,11), (0,1,6,10), (0,1,7,9), (0,2,3,12), (0,2,4,11), (0,2,5,10), (0,2,6,9), (0,2,7,8), (0,3,4,10), (0,3,5,9), (0,3,6,8), (0,4,5,8), (0,4,6,7), (1,2,3,11), (1,2,4,10), (1,2,5,9), (1,2,6,8), (1,3,4,9), (1,3,5,8), (1,3,6,7), (1,4,5,7), (2,3,4,8), (2,3,5,7), (2,4,5,6)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
