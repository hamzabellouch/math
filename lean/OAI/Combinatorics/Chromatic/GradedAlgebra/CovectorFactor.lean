import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PowerSeriesThreeFactors
import OAI.Combinatorics.Chromatic.GradedAlgebra.QuantumTorusSignFactors

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
variable {R : Type*} [Ring R]
lemma rightFactor_zero (F : PowerSeries R) (hF : constantCoeff F=1) :
    rightFactor 0 F=F := by
  have H:=uniqueness (0 : R→+R) F 1 F (by simp) hF (by simp)
    (fun n=>by simp) (fun n=>rfl)
  exact H.2.symm
lemma leftFactor_id (F : PowerSeries R) (hF : constantCoeff F=1) :
    leftFactor (AddMonoidHom.id R) F=F := by
  have H:=uniqueness (AddMonoidHom.id R) F F 1 hF (by simp) (by simp)
    (fun n=>rfl) (fun n=>by simp)
  exact H.1.symm
end ElementaryPositivity.PowerSeriesSplit
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)
lemma positiveProject_zero : positiveProject v Ω (0 : M→+ℝ)=0 := by
  classical
  apply AddMonoidHom.ext
  intro f
  apply Finsupp.ext
  intro m
  change (Finsupp.filter (fun a : M=>0<(0 : ℝ)) f) m=0
  simp
lemma zeroProject_zero : zeroProject v Ω (0 : M→+ℝ)=AddMonoidHom.id _ := by
  classical
  apply AddMonoidHom.ext
  intro f
  apply Finsupp.ext
  intro m
  change (Finsupp.filter (fun a : M=>(0 : ℝ)=0) f) m=f m
  simp
lemma zeroFactor_zero (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1) :
    zeroFactor (positiveProject v Ω (0 : M→+ℝ)) (zeroProject v Ω (0 : M→+ℝ)) F=F := by
  rw [positiveProject_zero,zeroProject_zero,zeroFactor,rightFactor_zero _ hF,leftFactor_id _ hF]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
