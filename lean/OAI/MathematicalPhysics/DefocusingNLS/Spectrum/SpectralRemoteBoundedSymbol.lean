import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFrameSymbol

namespace OAI

/-! Uniform symbols for the physical bounded part and the transformed remainder. -/

open Set Filter Topology
namespace DefocusingNLS
namespace HasUniformLogJetBound

theorem prodMk {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {L : ℕ → ℝ} {sigma : ℝ}
    {f : ℕ → ℝ → A} {g : ℕ → ℝ → B}
    (hf : HasUniformLogJetBound L sigma f) (hg : HasUniformLogJetBound L sigma g) :
    HasUniformLogJetBound L sigma (fun n t => (f n t,g n t)) := by
  have hh := (hf.map (ContinuousLinearMap.inl ℝ A B)).add
    (hg.map (ContinuousLinearMap.inr ℝ A B))
  simpa only [ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,
    add_zero,zero_add] using hh

theorem smul_const {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A]
    {L : ℕ → ℝ} {sigma : ℝ} {f : ℕ → ℝ → ℂ}
    (hf : HasUniformLogJetBound L sigma f) (v : A) :
    HasUniformLogJetBound L sigma (fun n t => f n t • v) :=
  hf.map (((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ)

end HasUniformLogJetBound

theorem spectralRemote_bounded_operator_symbol
    {L : ℕ → ℝ} {dp dm cp cm : ℕ → ℝ → ℂ}
    (hdp : HasUniformLogJetBound L 0 dp) (hdm : HasUniformLogJetBound L 0 dm)
    (hcp : HasUniformLogJetBound L 0 cp) (hcm : HasUniformLogJetBound L 0 cm) :
    HasUniformLogJetBound L 0 (fun n t => spectralRemoteBoundedOperator
      (dp n t) (dm n t) (cp n t) (cm n t)) := by
  let A := SpectralRemoteSpace →L[ℂ] ℂ
  let V := SpectralRemoteSpace →L[ℂ] (ℂ × ℂ)
  have hplus := ((HasUniformLogJetBound.const (L := L)
    ((-12 : ℂ) • spectralRemoteVelocityPlus)).add
      (hdp.smul_const spectralRemotePositionPlus)).add (hcp.smul_const spectralRemotePositionMinus)
  have hminus := ((HasUniformLogJetBound.const (L := L)
    ((-12 : ℂ) • spectralRemoteVelocityMinus)).add
      (hdm.smul_const spectralRemotePositionMinus)).add (hcm.smul_const spectralRemotePositionPlus)
  have hp := ((HasUniformLogJetBound.const (L := L) (0 : A)).prodMk hplus).map
    (ContinuousLinearMap.prodₗᵢ ℝ : A × A ≃ₗᵢ[ℝ] V).toContinuousLinearMap
  have hm := ((HasUniformLogJetBound.const (L := L) (0 : A)).prodMk hminus).map
    (ContinuousLinearMap.prodₗᵢ ℝ : A × A ≃ₗᵢ[ℝ] V).toContinuousLinearMap
  exact (hp.prodMk hm).map
    (ContinuousLinearMap.prodₗᵢ ℝ : V × V ≃ₗᵢ[ℝ] SpectralRemoteOperator).toContinuousLinearMap

noncomputable def spectralRemoteInitialRemainder
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator)
    (n : ℕ) (t : ℝ) : SpectralRemoteOperator :=
  Ring.inverse (spectralRemoteInitialFrame (c n t)) *
    (B n t*spectralRemoteInitialFrame (c n t) -
      deriv (fun s => spectralRemoteInitialFrame (c n s)) t)

theorem spectralRemote_initial_remainder_symbol
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ} {B : ℕ → ℝ → SpectralRemoteOperator}
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32)
    (hB : HasUniformLogJetBound L 0 B) :
    HasUniformLogJetBound L 0 (spectralRemoteInitialRemainder c B) := by
  obtain ⟨hP,hI⟩ := spectralRemote_initial_frame_symbols hc hsmall
  have hBP : HasUniformLogJetBound L 0
      (fun n t => B n t*spectralRemoteInitialFrame (c n t)) := by
    simpa only [add_zero] using hB.mul hP
  have hh := hI.mul (hBP.sub hP.deriv)
  convert hh using 1
  · simp only [add_zero]
  · rfl

end DefocusingNLS

end OAI
