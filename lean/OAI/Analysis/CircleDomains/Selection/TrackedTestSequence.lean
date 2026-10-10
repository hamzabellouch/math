import OAI.Analysis.CircleDomains.Selection.RecursiveTestConstruction

namespace OAI

/-! Follow each old scalar through every actual appending stage. The
coordinate indices shift by two, and both errors retain the chosen budget. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)

local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 def index (i : Fin T.count) : (n : ℕ) → Fin (states n).family.count
  | 0 => i
  | n+1 => (index i n).succ.succ

local notation "idx" => index hsupply hsard hsch hG hinf hTD ha hBa hε T

 def scalar (i : Fin T.count) (n : ℕ) : EuclideanPlane → ℝ :=
  (states n).family.test (idx i n)

 def witness (i : Fin T.count) (n : ℕ) :
    DeGiorgi.MemW1pWitness 2 (scalar hsupply hsard hsch hG hinf hTD ha hBa hε T i n)
      (physicalPlaneDomain G) := (states n).family.witness (idx i n)

local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem step_uniform (i : Fin T.count) (n : ℕ) (x : EuclideanPlane) :
    |f i (n+1) x-f i n x| < recursiveTestBudget ε n (states n).tolerances := by
  exact ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).data.old_close (idx i n) x

 theorem step_gradient (i : Fin T.count) (n : ℕ) :
    (eLpNorm (fun x => (W i (n+1)).weakGrad x-(W i n).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal < recursiveTestBudget ε n (states n).tolerances := by
  exact ((states n).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n).data.old_error (idx i n)

 theorem scalar_continuous (i : Fin T.count) (n : ℕ) : Continuous (f i n) :=
  (states n).family.continuous _

 theorem scalar_compact (i : Fin T.count) (n : ℕ) : HasCompactSupport (f i n) :=
  (states n).family.compact _

end AppendingSequence
end CircleDomainRigidity

end

end OAI
