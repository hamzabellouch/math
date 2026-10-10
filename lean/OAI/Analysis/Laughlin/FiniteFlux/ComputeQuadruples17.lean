import OAI.Analysis.Laughlin.FourBody.GramCompute

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_17 : GramCompute.quadruples 17 = [(0,1,2,15), (0,1,3,14), (0,1,4,13), (0,1,5,12), (0,1,6,11), (0,1,7,10), (0,1,8,9), (0,2,3,13), (0,2,4,12), (0,2,5,11), (0,2,6,10), (0,2,7,9), (0,3,4,11), (0,3,5,10), (0,3,6,9), (0,3,7,8), (0,4,5,9), (0,4,6,8), (0,5,6,7), (1,2,3,12), (1,2,4,11), (1,2,5,10), (1,2,6,9), (1,2,7,8), (1,3,4,10), (1,3,5,9), (1,3,6,8), (1,4,5,8), (1,4,6,7), (2,3,4,9), (2,3,5,8), (2,3,6,7), (2,4,5,7), (3,4,5,6)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
