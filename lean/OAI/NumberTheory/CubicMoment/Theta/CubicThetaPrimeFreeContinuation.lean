import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeSquareRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDeterminant

namespace OAI

/-! Holomorphic continuation of the pole-cleared square-class twist,
constructed from the actual arithmetic Fourier family. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaRegularizedFrequency_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedFrequency h s=(s-4/3)*cubicThetaFrequencyDirichlet h s := by
  have hs1 : 1<s.re := by linarith
  have hleft := (cubicThetaRegularizedFrequency_analytic hh s hs1).continuousAt
  have hright : ContinuousAt (fun z : ℂ => (z-4/3)*cubicThetaFrequencyDirichlet h z) s :=
    (continuousAt_id.sub continuousAt_const).mul
      (cubicThetaFrequencyDirichlet_differentiableAt h (by linarith)).continuousAt
  have hn : ∀ᶠ z : ℂ in 𝓝 s, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have he : cubicThetaRegularizedFrequency h=ᶠ[𝓝[≠] s]
      (fun z => (z-4/3)*cubicThetaFrequencyDirichlet h z) := by
    filter_upwards [cubicThetaRegularizedFrequency_germ hh hs1,nhdsWithin_le_nhds hn]
      with z hz hz3
    rw [hz,cubicThetaFrequencyContinuation_right _ hz3]
  exact tendsto_nhds_unique ((hleft.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (hright.tendsto.mono_left nhdsWithin_le_nhds)

def cubicThetaRegularizedPrimeFreeOne (p h : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaRegularizedFrequency (p^2*h) s/cubicThetaPrimeDeterminant p s

theorem cubicThetaRegularizedPrimeFreeOne_analytic {p : Eisenstein}
    (hp : primaryPrime p) {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedPrimeFreeOne p h) {s : ℂ | 1<s.re} := by
  intro s hs
  exact (cubicThetaRegularizedFrequency_analytic
    (mul_ne_zero (pow_ne_zero 2 hp.2.ne_zero) hh) s hs).div
      (cubicThetaPrimeDeterminant_analytic hp s) (cubicThetaPrimeDeterminant_ne_zero hp hs)

theorem cubicThetaRegularizedPrimeFreeOne_right {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedPrimeFreeOne p h s=(s-4/3)*cubicThetaPrimeFreeDirichlet p s h 1 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  unfold cubicThetaRegularizedPrimeFreeOne
  rw [cubicThetaRegularizedFrequency_right (mul_ne_zero (pow_ne_zero 2 hp.2.ne_zero) hh0) hs,
    cubicThetaFrequencyDirichlet_primeSquare hp (by linarith) h hh]
  have hd := cubicThetaPrimeDeterminant_ne_zero hp (s:=s) (by linarith)
  change ((s-4/3)*(cubicThetaPrimeDeterminant p s*cubicThetaPrimeFreeDirichlet p s h 1))/
    cubicThetaPrimeDeterminant p s=_
  field_simp

theorem cubicThetaRegularizedPrimeFreeOne_pole {p : Eisenstein}
    (hp : primaryPrime p) {h : Eisenstein} (hh : h≠0) :
    cubicThetaRegularizedPrimeFreeOne p h (4/3)=
      cubicThetaArithmeticFourierResidue (p^2*h) (4/3)/(1-((norm p:ℂ)⁻¹)^2) := by
  rw [cubicThetaRegularizedPrimeFreeOne,cubicThetaRegularizedFrequency_residue
    (mul_ne_zero (pow_ne_zero 2 hp.2.ne_zero) hh),cubicThetaPrimeDeterminant_pole hp]

end CubicFirstMoment

end

end OAI
