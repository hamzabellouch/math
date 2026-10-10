import OAI.Analysis.IrrationalRotation.Rotation.RotationFiniteReturnTowers
import OAI.Analysis.IrrationalRotation.Rotation.RotationRecursiveTowerAssembly

namespace OAI

noncomputable section

namespace Invariant233.Rotation

theorem isHyperfinite_algebra {θ : ℝ} (hθ : Irrational θ) :
    IsHyperfinite (algebra θ) := by
  obtain ⟨raw, hnest, hheight, hmesh⟩ := exists_raw_finiteReturnTowers hθ
  exact isHyperfinite_of_raw_return_towers θ raw
    (fun n => hnest (Nat.le_succ n)) hheight hmesh

end Invariant233.Rotation

end

end OAI
