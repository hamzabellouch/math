import OAI.Analysis.Laughlin.FourBody.GramCompute
import OAI.Analysis.Laughlin.FourBody.Matrix
import OAI.Analysis.Laughlin.FourBody.MatrixCompute
import OAI.Analysis.Laughlin.FourBody.RowBridge

namespace OAI

namespace Laughlin.Certificate

theorem Z_eq_gramCompute (D r s : ℕ) : Z D r s = GramCompute.ZFast D r s := by
  exact Z_eq_fast D r s

theorem compressedRational_eq_compute (D : ℕ) :
    compressedRational D = MatrixCompute.compressed D (errorRational D) (gramRational D) := by
  rfl

end Laughlin.Certificate

end OAI
