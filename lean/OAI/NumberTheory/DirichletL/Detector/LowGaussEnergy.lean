import OAI.NumberTheory.DirichletL.Detector.LowRayAmplitude
import OAI.NumberTheory.DirichletL.Moments.ReflectedChild

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumn (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then
    (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)
  else 0

lemma lowGaussColumn_row (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) (m : O) :
    (if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0)=
      lowGaussColumn C W1 Y σ v s*
        gaussRow (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) (-m) := by
  have he := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
  unfold lowGaussColumn gaussRow
  rw [congrArg Ideal.absNorm he]
  split_ifs
  · rw [lowAdditiveCoefficient_eq]
    simp only [div_eq_mul_inv]
    ring
  · simp

theorem lowRayAmplitude_gaussPolynomial (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀v : ℝ,∀m : O,
      lowRayAmplitude C W1 Y σ m v=
        gaussPolynomial F (fun s=>primaryGenerator s.val)
          (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) (-m) := by
  obtain ⟨F,hF⟩ := lowRayAmplitude_eq_finite C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ v m
  rw [hF σ m v]
  unfold gaussPolynomial
  apply Finset.sum_congr rfl
  intro s hs
  exact lowGaussColumn_row C W1 Y σ v s m

theorem lowRayAmplitude_energy (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀v : ℝ,
      ∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0<Q→∀rows : Finset O,
      (∀z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/Q)).re)→
      (∀z∈rows,1≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/Q)).re)→
      (∑z∈rows,‖lowRayAmplitude C W1 Y σ z v‖^2)≤
        (gaussEnergy F (fun s=>primaryGenerator s.val)
          (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) U Q).re := by
  obtain ⟨F,hF⟩ := lowRayAmplitude_gaussPolynomial C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ v U Q hQ rows hU hmajor
  simp_rw [hF σ v]
  exact CenteredMomentReflectedChild.finite_reflected_energy_le_gaussEnergy F
    (fun s=>primaryGenerator s.val) (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
    (lowGaussColumn C W1 Y σ v) U Q hQ rows hU hmajor

end SevenEighths.ProbePhysical
end

end OAI
