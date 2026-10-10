import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.ScalarTower
import OAI.Analysis.Kaplansky.Regular.HilbertTensorModel
import OAI.Analysis.Kaplansky.Ultrapower.Polar
import OAI.Analysis.Kaplansky.Ultrapower.Maximal
import OAI.Analysis.Kaplansky.Ultrapower.PartialCorners
import OAI.Analysis.Kaplansky.Ultrapower.Wandering
import OAI.Analysis.Kaplansky.Ultrapower.MatrixDenseUnits
import OAI.Analysis.Kaplansky.StableFiniteness.SimpleTensor
import OAI.Analysis.Kaplansky.StableFiniteness.QuasitraceLoss

namespace OAI

section
noncomputable section
namespace KaplanskyConsequences

theorem stable_finiteness_bundle : StableFinitenessBundle :=
  ⟨simple_stable_tensor_counterexample_exists,reduced_quasitrace_loss_exists,
    trace_free_stably_finite_exists⟩

end KaplanskyConsequences
end
end

end OAI
