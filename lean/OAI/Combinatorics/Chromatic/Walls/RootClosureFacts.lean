import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.SeriesApproximation
import OAI.Combinatorics.Chromatic.Walls.RootProducts

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
open WallUnits
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M)
variable {A : Set (PowerSeries (Torus LaurentRay.vUnit Ω))}
variable {F : PowerSeries (Torus LaurentRay.vUnit Ω)}

lemma InPrecisionClosure.graded
    (hF : InPrecisionClosure LaurentRay.vUnit Ω A F)
    (hA : ∀G∈A,SeriesGraded LaurentRay.vUnit Ω C G) :
    SeriesGraded LaurentRay.vUnit Ω C F := by
  classical
  intro n m hm
  ext j
  obtain ⟨G,hG,H⟩:=hF {(n,m,j+1)}
  have HH:=H (n,m,j+1) (by simp) j (by dsimp; omega)
  dsimp only at HH
  rw [hA G hG n m hm] at HH
  exact HH.symm

lemma InPrecisionClosure.constant
    (hF : InPrecisionClosure LaurentRay.vUnit Ω A F)
    (hA : ∀G∈A,constantCoeff G=1) : constantCoeff F=1 := by
  classical
  apply Finsupp.ext
  intro m
  ext j
  obtain ⟨G,hG,H⟩:=hF {(0,m,j+1)}
  have HH:=H (0,m,j+1) (by simp) j (by dsimp; omega)
  dsimp only at HH
  rw [coeff_zero_eq_constantCoeff] at HH
  rw [hA G hG] at HH
  exact HH.symm

variable (V : M→Prop)
def rootClosureCompleted (hF : InPrecisionClosure LaurentRay.vUnit Ω
    (literalRootProducts Ω C V) F) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨F,hF.constant Ω (fun _ h=>literalRootProducts_constant Ω C V h),
    hF.graded Ω C (fun _ h=>literalRootProducts_graded Ω C V h)⟩

lemma InPrecisionClosure.zeroFactor
    (hF : InPrecisionClosure LaurentRay.vUnit Ω A F)
    (hA : ∀G∈A,SeriesGraded LaurentRay.vUnit Ω C G)
    (h : M→+ℝ) (B : Set (PowerSeries (Torus LaurentRay.vUnit Ω)))
    (hB : ∀G∈A,InPrecisionClosure LaurentRay.vUnit Ω B
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) G)) :
    InPrecisionClosure LaurentRay.vUnit Ω B
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) F) := by
  let g:=precisionApprox LaurentRay.vUnit Ω hF
  have hg:=precisionApprox_converges LaurentRay.vUnit Ω hF
  have hgg : ∀T,SeriesGraded LaurentRay.vUnit Ω C (g T) :=
    fun T=>hA _ (precisionApprox_mem LaurentRay.vUnit Ω hF T)
  have hFG:=hF.graded Ω C hA
  have H:=filter_factors_converge LaurentRay.vUnit Ω C Filter.atTop (fun m=>0<h m) hg hgg hFG
  have HH:=filter_factors_converge LaurentRay.vUnit Ω C Filter.atTop (fun m=>h m=0) H.2
    (fun T n=>by
      simpa only [PowerSeriesSplit.rightFactor,coeff_mk] using
        (filter_pair_graded LaurentRay.vUnit Ω C (fun m=>0<h m) (g T) (hgg T) n).2)
    (fun n=>by
      simpa only [PowerSeriesSplit.rightFactor,coeff_mk] using
        (filter_pair_graded LaurentRay.vUnit Ω C (fun m=>0<h m) F hFG n).2)
  apply InPrecisionClosure.of_converges LaurentRay.vUnit Ω Filter.atTop HH.1
  exact Eventually.of_forall (fun T=>hB _ (precisionApprox_mem LaurentRay.vUnit Ω hF T))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
