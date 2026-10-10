import OAI.Analysis.LipschitzHilbert.Estimates.SmoothedCommutatorDecomposition

namespace OAI

/-! The assembled finite commutator bound has one constant, independent
of the coefficient smoothing and the number of input frequency bands. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def lineLowHighEnergyConstant : ℝ :=
  36*((∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*
    localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9))^2

def lineHighLowEnergyConstant : ℝ :=
  576*((∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*(26*Real.pi/3))^2

def lineCommutatorEnergyConstant : ℝ :=
  3*(lineLowHighEnergyConstant+lineHighLowEnergyConstant+49152*comparableCommutatorConstant)

theorem comparableCommutatorConstant_nonneg : 0≤comparableCommutatorConstant := by
  unfold comparableCommutatorConstant
  have h := smoothCarlesonDualConstant_nonneg
  positivity

theorem lineCommutatorEnergyConstant_nonneg : 0≤lineCommutatorEnergyConstant := by
  unfold lineCommutatorEnergyConstant lineLowHighEnergyConstant lineHighLowEnergyConstant
  have h := comparableCommutatorConstant_nonneg
  positivity

theorem lineSchwartz_three_add_energy (f g h : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(f+g+h) x‖^2)≤3*((∫ x, ‖f x‖^2)+(∫ x, ‖g x‖^2)+(∫ x, ‖h x‖^2)) := by
  simpa only [sub_neg_eq_add,neg_apply,norm_neg] using lineSchwartz_three_energy f (-g) h

theorem smoothedCommutator_energy (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (l v : ℤ) (hl : ∀ j∈J, l≤j+4) (hv : ∀ j∈J, j+4≤v) :
    (∫ x, ‖lineSchwartzCommutator m (lineLowpass b l)
      (schwartzDerivative 1 (∑ j∈J, lineDyadic h j)) x‖^2)≤
        lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
  let I := Finset.Icc (l+1) v
  let F := ∑ j∈J, lowHighPiece m b h j
  let G := ∑ i∈I, highLowRow J m b h i
  let H := ∑ i∈I, lineSchwartzCommutator m (lineDyadic b i)
    (schwartzDerivative 1 (nearbyInput J h i))
  have hm0 (eta : ℝ) : ‖m eta‖≤A := by
    simpa only [pow_zero,one_mul,iteratedDeriv_zero] using hm 0 (by norm_num) eta
  have hF : (∫ x, ‖F x‖^2)≤lineLowHighEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
    apply (lowHighSum_energy J m b h A L hA hm hLip).trans_eq
    unfold lineLowHighEnergyConstant
    ring
  have hG : (∫ x, ‖G x‖^2)≤lineHighLowEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
    apply (highLowSum_energy I J m b h A L hm0 hLip).trans_eq
    unfold lineHighLowEnergyConstant
    ring
  have hH : (∫ x, ‖H x‖^2)≤(49152*comparableCommutatorConstant)*A^2*L^2*(∫ x, ‖h x‖^2) := by
    have hc := comparableCommutatorSum_energy I m b (nearbyInput J h) A L hm0 hLip
      (fun i _ eta heta => nearbyInput_frequency J h i eta heta)
    have hnear := nearbyInput_energy I J h
    calc
      _ ≤ comparableCommutatorConstant*A^2*L^2*(∑ i∈I, ∫ x, ‖nearbyInput J h i x‖^2) := hc
      _ ≤ comparableCommutatorConstant*A^2*L^2*(49152*(∫ x, ‖h x‖^2)) :=
        mul_le_mul_of_nonneg_left hnear (by have := comparableCommutatorConstant_nonneg; positivity)
      _ = _ := by ring
  rw [smoothedCommutator_decomposition J m b h l v hl hv]
  calc
    _ ≤ 3*((∫ x, ‖F x‖^2)+(∫ x, ‖G x‖^2)+(∫ x, ‖H x‖^2)) := lineSchwartz_three_add_energy F G H
    _ ≤ 3*(lineLowHighEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2)+
        lineHighLowEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2)+
        (49152*comparableCommutatorConstant)*A^2*L^2*(∫ x, ‖h x‖^2)) := by gcongr
    _ = _ := by unfold lineCommutatorEnergyConstant; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
