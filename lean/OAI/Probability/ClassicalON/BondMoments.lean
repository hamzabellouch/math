import OAI.Probability.ClassicalON.JointBond

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem ising_numerator_bond_sum (left right : E → V) (K : E → ℝ) (x y : V) :
    (∫ s,Real.exp (edgeHamiltonian (isingEnergy left right) K s)*(signValue (s x)*signValue (s y)) ∂isingReference)=
      (2:ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,K e)*
        ∑ η,bondWeight left right (fun e => Real.exp (2*K e)-1) η*
          (if bondConnected left right η x y then 1 else 0) := by
  have hs (η : E → Bool) :
      (∑ s : V → Bool,Real.exp (-∑ e,K e)*(bondProduct (fun e => Real.exp (2*K e)-1) η*
        (if s∈compatibleSigns left right η then 1 else 0))*(signValue (s x)*signValue (s y)))=
        Real.exp (-∑ e,K e)*bondWeight left right (fun e => Real.exp (2*K e)-1) η*
          (if bondConnected left right η x y then 1 else 0) := by
    calc
      _ = (Real.exp (-∑ e,K e)*bondProduct (fun e => Real.exp (2*K e)-1) η)*
          ∑ s : V → Bool,(if s∈compatibleSigns left right η then 1 else 0)*(signValue (s x)*signValue (s y)) := by
        rw [Finset.mul_sum]; congr 1; ext s; ring
      _ = _ := by
        rw [compatible_sign_correlation_sum]
        split_ifs <;> simp [bondWeight]
        ring
  have hall : (∑ s : V → Bool,Real.exp (edgeHamiltonian (isingEnergy left right) K s)*
      (signValue (s x)*signValue (s y)))=
      Real.exp (-∑ e,K e)*∑ η,bondWeight left right (fun e => Real.exp (2*K e)-1) η*
        (if bondConnected left right η x y then 1 else 0) := by
    simp_rw [ising_expansion,bondSignProduct_eq,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [hs]
    simp_rw [mul_assoc]
  rw [integral_isingReference,hall]
  ring

theorem isingAmplitudePartition_bond_sum (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    isingAmplitudePartition left right b r=
      (2:ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
        ∑ η,bondWeight left right (amplitudeBondParam left right b r) η := by
  have hp : (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1)=
      amplitudeBondParam left right b r := by
    funext e
    unfold amplitudeBondParam amplitudeCoupling
    congr 2
    ring
  rw [isingAmplitudePartition,amplitudePartition,ising_partition_bond_sum,hp]

end ClassicalON

end

end OAI
