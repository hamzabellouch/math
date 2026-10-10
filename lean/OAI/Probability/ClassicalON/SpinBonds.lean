import OAI.Probability.ClassicalON.RawBond

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_eq (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1)=
      amplitudeBondParam left right b r := by
  funext e
  unfold amplitudeBondParam amplitudeCoupling
  congr 2
  ring

theorem integral_spinBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η ∂freeSpinReference 3)=
      ∫ r,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*
      spinBondWeight left right b s η) :=
    (continuous_freeSpinEnergy 3 left right b).rexp.mul (continuous_spinBondWeight left right b η)
  rw [integral_freeSpinReference_cylinder _ hc]
  apply integral_congr_ae
  filter_upwards with r
  simp_rw [cylindrical_spin_bond_weight,integral_const_mul]
  change (∫ τ,Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
    bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1) η τ*
    planarAmplitudePartition left right b r ∂isingReference)=_
  rw [integral_mul_const,integral_const_mul,integral_isingReference]
  simp_rw [bondSignProduct_eq,← Finset.mul_sum,compatibleSigns_sum]
  rw [amplitudeBondParam_eq]
  unfold amplitudeBondWeight amplitudeBondPrefactor bondWeight
  ring

theorem integral_freeSpinWeight (left right : E → V) (b : E → ℝ) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂freeSpinReference 3)=
      ∫ r,amplitudeDensity left right b r ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  have he (s : V → Spin 3) : Real.exp (freeSpinEnergy 3 left right b s)=
      ∑ η,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η := by
    rw [← Finset.mul_sum,spinBondWeight_sum,mul_one]
  rw [show (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s))=
    (fun s => ∑ η,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η) from funext he]
  rw [integral_finsetSum]
  · simp_rw [integral_spinBondWeight]
    rw [← integral_finsetSum]
    · simp_rw [amplitudeBondWeight_sum]
    · intro η _
      exact compact_integrable (continuous_amplitudeBondWeight _ _ _ _)
  · intro η _
    exact compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul (continuous_spinBondWeight _ _ _ _))

def freeBondMean (left right : E → V) (b : E → ℝ) (f : (E → Bool) → ℝ) : ℝ :=
  freeSpinMean 3 left right b (fun s => ∑ η,spinBondWeight left right b s η*f η)

theorem freeBondMean_eq_jointBondMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (f : (E → Bool) → ℝ) :
    freeBondMean left right b f=jointBondMean sphericalAmplitudeLaw left right b (fun _ η => f η) := by
  rw [jointBondMean_raw _ _ _ _ hb]
  unfold freeBondMean freeSpinMean weightedMean
  rw [integral_freeSpinWeight]
  simp_rw [amplitudeBondWeight_sum]
  congr 1
  simp_rw [Finset.mul_sum,← mul_assoc]
  rw [integral_finsetSum,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro η _
    rw [integral_mul_const,integral_mul_const,integral_spinBondWeight]
  · intro η _
    exact (compact_integrable (continuous_amplitudeBondWeight _ _ _ _)).mul_const _
  · intro η _
    exact (compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul
      (continuous_spinBondWeight _ _ _ _))).mul_const _

end ClassicalON

end

end OAI
