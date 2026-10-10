import Mathlib
import OAI.Analysis.Conductivity.Geometry.ControlledCorrectionBoxes
import OAI.Analysis.Conductivity.Sobolev.WallParticularFamily

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
lemma wall_particular_family_finishes
    {χ : Box3 → ℝ} {v : P×Box3 → ℝ} {r : Fin 2 → P×Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    (q : P) {U : Set Coord3} (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    (hrs : ∀ j,HasCompactSupport (fun y => r j (q,y)))
    (hne : ∀ z∈tsupport χ,wallQuotient (wallDerivative (fun y => v (q,y))) z≠0)
    (hm : physicalSourceMoment (wallCoordinatePair (fun y => v (q,y))) (wallInputPair r q)=0)
    {ε : ℝ} (small : ∀ x,‖wallParticularFamily χ v r (q,x)‖≤ε/2)
    (solve : physicalSourceMoment (wallCoordinatePair (fun y => v (q,y)))
        (fun j x => wallResidualFamily χ v r j (q,x))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U
        (fun j x => wallResidualFamily χ v r j (q,x)) (ε/2)) :
    BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U (wallInputPair r q) ε := by
  have hvq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) := hv.comp (contDiff_const.prodMk contDiff_id)
  have hrq (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => r j (q,y)) := (hr j).comp (contDiff_const.prodMk contDiff_id)
  have hRm := (wallResidualFamily_moment hχ hχc hv hr hrs hne).trans hm
  let H : Coord3 → Mat3 := fun x => wallParticularFamily χ v r (q,x)
  have hHs : ContDiff ℝ (↑(⊤:ℕ∞)) H := by
    change ContDiff ℝ (↑(⊤:ℕ∞)) (wallParticularTensor χ (fun y => v (q,y))
      (fun y => r 0 (q,y)) (fun y => r 1 (q,y)))
    exact wallParticularTensor_smooth hχ hvq (hrq 0) (hrq 1) hne
  have hc := wallParticularTensor_compact (χ:=χ) (v:=fun y => v (q,y))
    (r₁:=fun y => r 0 (q,y)) (r₂:=fun y => r 1 (q,y)) hχc
  have hHsolve : BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U
      (symmetricSource H (wallCoordinatePair (fun y => v (q,y)))) (ε/2) :=
    ⟨H,hHs,hc.1,hc.2.trans hχU,by
      unfold H wallParticularFamily wallParticularTensor
      intro x
      exact wallMatrix_symmetric _ _ x,fun _ => rfl,small⟩
  have hh := hHsolve.add (wallCoordinatePair_smooth hvq) (solve hRm)
  rw [wallResidualFamily_eq,add_sub_cancel] at hh
  convert hh using 1; ring

end ScalarConductivity

end
end

end OAI
