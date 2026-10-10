import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationAnnulusTail
import OAI.Analysis.CoulombRadii.RandomFields.CoreGap

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem physical_observed_inner_deficit_tail {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : Fin J) {r a T p₀ : ℝ}
    (hr : 0<r) (hp₀ : 0<p₀) (hre : r+Real.sqrt 3*ℓ h≤a)
    (hth : 2*Coulomb.atomicInnerFieldConstant*Coulomb.screenMass
      (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r<T) :
    (observationLaw J (rawLaw ψ)).real
      (observationCoordinateData ℓ ⁻¹'
        {y | T<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)})≤p₀ := by
  rw [physical_arrayEvent_probability hd.2.2.1 hn ℓ (fun h => (hℓ h).ne')
    (observed_deficit_event_measurable h Z a T)]
  exact atomic_observed_inner_deficit_tail Z hZ hd hn hmin hE hbase hD ℓ hℓ h hr hp₀ hre hth

lemma deficit_screening_exponential_cutoff {B K D r k : ℝ}
    (hB : 0≤B) (hK : 0≤K) (hD : 0≤D) (hr : 0≤r) (hk : 0≤k) :
    B*Coulomb.screenMass (D+K*(1-Real.log (Real.exp (-k)))^5) r <
      (B*(Coulomb.screenBaseMass r+Real.sqrt ((D+K)*r))+1)*(1+k)^3 := by
  rw [Real.log_exp]
  have hv : 1≤1+k := by linarith
  have h6 : 1≤(1+k)^6 := one_le_pow₀ hv
  have h56 : (1+k)^5≤(1+k)^6 := by
    calc
      _ ≤ (1+k)^5*(1+k) := le_mul_of_one_le_right (by positivity) hv
      _ = _ := by ring
  have hδ : (D+K*(1- -k)^5)*r≤((D+K)*r)*((1+k)^3)^2 := by
    have hD' := mul_le_mul_of_nonneg_left h6 hD
    have hK' := mul_le_mul_of_nonneg_left h56 hK
    have H : D+K*(1- -k)^5≤(D+K)*(1+k)^6 := by nlinarith
    have H' := mul_le_mul_of_nonneg_right H hr
    nlinarith
  have hs : Real.sqrt ((D+K*(1- -k)^5)*r)≤Real.sqrt ((D+K)*r)*(1+k)^3 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (add_nonneg hD hK) hr)]
    exact hδ
  have hbase : Coulomb.screenBaseMass r≤Coulomb.screenBaseMass r*(1+k)^3 :=
    le_mul_of_one_le_right (Coulomb.screenBaseMass_nonneg r) (one_le_pow₀ hv)
  unfold Coulomb.screenMass
  have H := mul_le_mul_of_nonneg_left (add_le_add hbase hs) hB
  have hp : 0<(1+k)^3 := by positivity
  nlinarith

def observedDeficitCoefficient {J : ℕ} (ℓ : Fin J → ℝ) (D r : ℝ) : ℝ :=
  2*Coulomb.atomicInnerFieldConstant*(Coulomb.screenBaseMass r+
    Real.sqrt ((D+observationEventEnergyConstant*observationWidthSquareSum ℓ)*r))+1

lemma observedDeficitCoefficient_pos {J : ℕ} (ℓ : Fin J → ℝ) (D r : ℝ) :
    0<observedDeficitCoefficient ℓ D r := by
  unfold observedDeficitCoefficient
  have := Coulomb.atomicInnerFieldConstant_nonneg
  have := Coulomb.screenBaseMass_nonneg r
  positivity

theorem physical_observed_deficit_exponential_tail {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : Fin J) {r a k : ℝ}
    (hr : 0<r) (hk : 0≤k) (hre : r+Real.sqrt 3*ℓ h≤a) :
    (observationLaw J (rawLaw ψ)).real
      (observationCoordinateData ℓ ⁻¹'
        {y | observedDeficitCoefficient ℓ D₀ r*(1+k)^3<
          (Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)})≤Real.exp (-k) := by
  exact physical_observed_inner_deficit_tail Z hZ hd hn hmin hE hbase hD ℓ hℓ h hr
    (Real.exp_pos _) hre (deficit_screening_exponential_cutoff
      (mul_nonneg (by norm_num) Coulomb.atomicInnerFieldConstant_nonneg)
      (mul_nonneg observationEventEnergyConstant_pos.le (observationWidthSquareSum_nonneg ℓ)) hD hr.le hk)
end NeutralAtom

end

end
end

end OAI
