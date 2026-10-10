import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestPointTail

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore SharpLogRamsey.PointScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem projective_point_tail
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (R : ℕ) (b : ℝ) (p : ℕ) (hp : Even p) (t M : ℝ) (ht : 0<t) (hM : 0≤M)
    (hm : ∀ bits : A → Fin R → Bool,
      (∫ ω,(∑ H : A,scoreTerm (lines x H) b (bits H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R × RadialLine x => L*radialWeight (S\(O∪{x})) x c i.2))≤M) :
    (batchMeasure (fun _ : Fin R × S => L*c)).real
      {ω | (∀ r (y : S),y.1=x → ω (r,y)=0) ∧
        t ≤ |pointScore (fun y : S => y.1∈O)
          (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep) b ω|}
      ≤ M/t^p := by
  apply point_score_tail (fun _ : Fin R × S => L*c)
    (fun y : S => y.1∈O) (fun y : S => y.1=x)
    (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep)
    (outsideDirection S O x) (fun H : A => lines x H)
    (fun H y => outsideDirection_incidence S O x H (hA H H.2) y) b
    (fun k => L*radialWeight (S\(O∪{x})) x c k.2) _ p hp t M ht hM hm
  intro k
  exact actual_radial_rate S O x L c k

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
