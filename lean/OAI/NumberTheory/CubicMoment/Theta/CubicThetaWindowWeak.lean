import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothGlobalWeak

namespace OAI

/-! The exact compact-window weak equation connects the low forcing
with the high cusp observation of every actual spectral residue. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaWindowForcingSection (s : ℂ) : CubicThetaSection :=
  cubicThetaHighWindowSection s-cubicThetaForcingSection s

lemma cubicThetaWindowForcingSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaWindowForcingSection s)) :=
  cubicThetaCompactSection_sub _ _ (cubicThetaHighWindowSection_compact s)
    (cubicThetaForcingSection_compact s)

lemma cubicThetaWindowForcingL2 (s : ℂ) :
    (cubicThetaCompactSection_memLp (cubicThetaWindowForcingSection s)
      (cubicThetaWindowForcingSection_compact s)).toLp _=
      cubicThetaHighWindowL2 s-cubicThetaForcingL2 s := by
  exact MemLp.toLp_sub (cubicThetaCompactSection_memLp (cubicThetaHighWindowSection s)
    (cubicThetaHighWindowSection_compact s))
    (cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s))

lemma cubicThetaWindow_coordinate_equation (s : ℂ) (p : ℂ × ℝ) (hp : 0<p.2) :
    cubicThetaCoordinateLaplacian (cubicThetaSectionFunction (cubicThetaIncomingWindowTest s)) p=
      s*(s-2)*cubicThetaSectionFunction (cubicThetaIncomingWindowTest s) p-
        cubicThetaSectionFunction (cubicThetaWindowForcingSection s) p := by
  have he : ∀ x y v, 0<v →
      cubicThetaSectionFunction (cubicThetaIncomingWindowTest s) (cubicThetaCartesianPoint x y v)=
        cubicThetaIncomingWindow (cubicThetaCartesianPoint x y v) s := by
    intro x y v hv
    rw [cubicThetaSectionFunction_apply _ hv]
    rfl
  rw [cubicThetaCoordinateLaplacian_hyperbolic,
    cubicThetaHyperbolicOperator_congr he p.1.re p.1.im hp,
    cubicThetaIncomingWindow_equation s p.1.re p.1.im hp,cubicThetaCartesianPoint_self,
    cubicThetaSectionFunction_apply _ hp,cubicThetaSectionFunction_apply _ hp]
  change s*(s-2)*cubicThetaIncomingWindow p s+cubicThetaForcingSeries p s-
    cubicThetaHighWindowSeries p s=
    s*(s-2)*cubicThetaIncomingWindow p s-
      (cubicThetaHighWindowSeries p s-cubicThetaForcingSeries p s)
  ring

theorem cubicThetaWindow_global_weak (s : ℂ) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalGradient (cubicThetaIncomingWindowTest s))+
    s*(s-2)*inner ℂ (cubicThetaGlobalInclusion v)
      (cubicThetaGlobalMass (cubicThetaIncomingWindowTest s))=
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaHighWindowL2 s-cubicThetaForcingL2 s) := by
  have h := cubicThetaSmooth_global_weak (cubicThetaIncomingWindowTest s)
    (cubicThetaWindowForcingSection s) (cubicThetaWindowForcingSection_compact s)
    (s*(s-2)) (cubicThetaWindow_coordinate_equation s) v
  rwa [cubicThetaWindowForcingL2] at h

lemma cubicThetaWindow_forcing_balance (σ : ℝ) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaForcingL2 σ)=
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaHighWindowL2 σ) := by
  have hR := cubicThetaArithmeticResidueEnergy_weak σ
    (cubicThetaGlobalEnergyTest (cubicThetaIncomingWindowTest σ))
  rw [cubicThetaGlobalInclusion_test,cubicThetaGlobalEnergyGradient_test] at hR
  have hR' := congrArg (starRingEnd ℂ) hR
  simp only [map_add,map_mul,map_sub,map_zero,map_ofNat,inner_conj_symm,
    Complex.conj_ofReal] at hR'
  have hW := cubicThetaWindow_global_weak σ (cubicThetaArithmeticResidueEnergy σ)
  have hz : inner ℂ (cubicThetaGlobalEnergyGradient (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaGlobalGradient (cubicThetaIncomingWindowTest σ))+
      (σ:ℂ)*((σ:ℂ)-2)*inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
        (cubicThetaGlobalMass (cubicThetaIncomingWindowTest σ))=0 := by
    linear_combination hR'
  rw [hz,inner_sub_right] at hW
  exact (sub_eq_zero.mp hW.symm).symm

lemma cubicThetaResidue_forcing_orthogonal_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaForcingL2 σ)=0 := by
  rw [cubicThetaWindow_forcing_balance]
  have h := cubicThetaHighWindowPairing_residue_zero_closed hσ hσ2 hne
  rw [← inner_conj_symm, h, map_zero]

lemma cubicThetaResidue_forcing_orthogonal {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaForcingL2 σ)=0 :=
  cubicThetaResidue_forcing_orthogonal_closed hσ hσ2.le hne

end CubicFirstMoment

end

end OAI
