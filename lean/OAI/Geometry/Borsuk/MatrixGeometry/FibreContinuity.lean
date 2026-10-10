import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.FibreHomotopy

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreContinuity
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.negativeCoordinates_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : ContinuousOn (negativeCoordinates f I) {Q : M | 0 ≤ Q} := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_apply i.val).comp_continuousOn hf.positiveExtension_continuousOn

omit [Nonempty ν] in
lemma centeredFibre_continuousOn (c : E) :
    ContinuousOn (fun p : E × M => centeredFibre c p.1 p.2) {p | c+p.1 ≠ 0} :=
  householder_matrix_joint_continuousOn c

omit [Nonempty ν] in
lemma fibreTransport_continuousOn_comp {X : Type*} [TopologicalSpace X]
    {S : Set X} (c : E) {u v : X → E} {Q : X → M}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (hQ : ContinuousOn Q S)
    (hc : ∀ x ∈ S, c+u x ≠ 0 ∧ c+v x ≠ 0) :
    ContinuousOn (fun x => fibreTransport c (u x) (v x) (Q x)) S := by
  exact ContinuousOn.comp' (g := fun p : E × E × M => fibreTransport c p.1 p.2.1 p.2.2)
    (f := fun x : X => (u x,v x,Q x)) (s := S)
    (fibreTransport_continuousOn c) (hu.prodMk (hv.prodMk hQ)) hc

omit [DecidableEq ν] [Nonempty ν] in
lemma chamberPath_matrix_continuousOn {Z : Set E} {c : E} (hcz : c ∈ Z)
    (hcs : c ∈ safeNormals Z) :
    ContinuousOn (fun p : ℝ × E × M => chamberPath c p.2.1 p.1)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber Z c} := by
  have hp : Continuous (fun p : ℝ × E × M => (p.1,p.2.1)) :=
    continuous_fst.prodMk continuous_snd.fst
  exact ContinuousOn.comp' (g := fun p : ℝ × E => chamberPath c p.2 p.1)
    (f := fun p : ℝ × E × M => (p.1,p.2.1))
    (chamberPath_continuousOn hcz hcs) hp.continuousOn (fun _ h => h)

omit [DecidableEq ι] in
omit [Nonempty ν] in
lemma transportedFibre_continuousOn {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : E} (hc : c ∈ commonPositiveCone f I) :
    ContinuousOn (fun p : ℝ × E × M => transportedFibre c p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber (activeVectors f I) c} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  apply fibreTransport_continuousOn_comp c continuous_snd.fst.continuousOn
    (chamberPath_matrix_continuousOn hcz hcs) continuous_snd.snd.continuousOn
  intro p hp
  exact ⟨chamber_add_ne_zero hcz hcs hp.2,
    chamber_add_ne_zero hcz hcs (chamberPath_mem hcz hcs hp.2 hp.1)⟩

lemma Admissible.fibreHomotopy_continuousOn {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × E × M => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  let S : Set (ℝ × E × M) := {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1}
  have hT : ContinuousOn (fun p : ℝ × E × M => transportedFibre c p.1 p.2.1 p.2.2) S :=
    (transportedFibre_continuousOn hf hI hc).mono (fun _ hp => ⟨hp.1,hp.2.2.1⟩)
  have hC : ContinuousOn (fun p : ℝ × E × M => centeredFibre c p.2.1 p.2.2) S :=
    (centeredFibre_continuousOn c).comp continuous_snd.continuousOn
      (fun _ hp => chamber_add_ne_zero hcz hcs hp.2.2.1)
  have hET := (hf.negativeCoordinates_continuousOn I).comp hT
    (fun _ hp => (transportedFibre_mem hf hI hc hcn hp.2.1 hp.2.2.1 hp.1 hp.2.2.2).1)
  have hEC := (hf.negativeCoordinates_continuousOn I).comp hC
    (fun _ hp => (centeredFibre_mem hcn hp.2.1 hp.2.2.2).1)
  exact hET.add (continuous_fst.continuousOn.smul ((hg.comp_continuousOn hC).sub hEC))

end FibreContinuity
end BorsukNine

end OAI
