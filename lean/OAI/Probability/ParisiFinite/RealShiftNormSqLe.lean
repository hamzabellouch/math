import Mathlib
import OAI.Probability.ParisiFinite.ScalarPhase
import OAI.Probability.ParisiFinite.SumLeCode

namespace OAI

/-! Real Shift Norm Sq Le. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter

namespace GaussianCoherent
variable {κ : Type*} [Fintype κ]

theorem realShift_norm_sq_le (v : Mode κ) :
    ‖WithLp.toLp 2 (realShift v)‖^2≤4*‖v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  change ‖-2*(v k).im‖^2≤4*‖v k‖^2
  simp only [Real.norm_eq_abs,sq_abs]
  have h := Complex.sq_norm_sub_sq_im (v k)
  nlinarith [sq_nonneg (v k).re]

namespace Quadratic
variable {ι : Type*}

def packetConstant (R : ℝ) : ℝ := 8+32*R^2+64*R^4

theorem packetConstant_nonneg (R : ℝ) : 0≤packetConstant R := by
  unfold packetConstant
  positivity

 

theorem coherent_error_sq_le_uniform (s : Finset ι) (d e : ι → RealMode κ)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0)
    (he : ∀i∈s,∀j∈s,i≠j → ⟪e i,e j⟫=0) (t R : ℝ) (hR : 0≤R)
    (v : Mode κ) (hv : ‖v‖≤R) :
    ‖unitary s d e t (CoherentFock.coherent v)-CoherentFock.coherent v‖^2≤
      t^2*ClassicalGaussian.Shifted.kernelSq (RealMode κ) s d e*packetConstant R := by
  have hv2 := (sq_le_sq₀ (norm_nonneg v) hR).mpr hv
  have hs := realShift_norm_sq_le v
  have hs2 : ‖WithLp.toLp 2 (realShift v)‖^2≤4*R^2 := by nlinarith
  have hs4 := pow_le_pow_left₀ (sq_nonneg ‖WithLp.toLp 2 (realShift v)‖) hs2 2
  have hp : 8+8*‖WithLp.toLp 2 (realShift v)‖^2+
      4*‖WithLp.toLp 2 (realShift v)‖^4≤packetConstant R := by
    unfold packetConstant
    nlinarith
  exact (coherent_error_sq_le s d e ho he t v).trans
    (mul_le_mul_of_nonneg_left hp
      (mul_nonneg (sq_nonneg t) (ClassicalGaussian.Shifted.kernelSq_nonneg _ s d e)))

 

theorem packet_error_le {ρ : Type*} (s : Finset ι) (d e : ι → RealMode κ)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0)
    (he : ∀i∈s,∀j∈s,i≠j → ⟪e i,e j⟫=0) (t R : ℝ) (hR : 0≤R)
    (u : Finset ρ) (c : ρ → ℂ) (v : ρ → Mode κ) (hv : ∀j∈u,‖v j‖≤R) :
    ‖unitary s d e t (∑j∈u,c j • CoherentFock.coherent (v j))-
      ∑j∈u,c j • CoherentFock.coherent (v j)‖≤
      (∑j∈u,‖c j‖)*Real.sqrt
        (t^2*ClassicalGaussian.Shifted.kernelSq (RealMode κ) s d e*packetConstant R) := by
  calc
    _=‖∑j∈u,c j • (unitary s d e t (CoherentFock.coherent (v j))-
          CoherentFock.coherent (v j))‖ := by
      simp only [map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]
    _≤∑j∈u,‖c j‖*‖unitary s d e t (CoherentFock.coherent (v j))-
          CoherentFock.coherent (v j)‖ := by
      simpa only [norm_smul] using norm_sum_le u
        (fun j=>c j • (unitary s d e t (CoherentFock.coherent (v j))-CoherentFock.coherent (v j)))
    _≤∑j∈u,‖c j‖*Real.sqrt
        (t^2*ClassicalGaussian.Shifted.kernelSq (RealMode κ) s d e*packetConstant R) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (Real.le_sqrt_of_sq_le (coherent_error_sq_le_uniform s d e ho he t R hR (v j) (hv j hj)))
        (norm_nonneg _)
    _=_ := by rw [Finset.sum_mul]

end Quadratic
end GaussianCoherent

 

open scoped BigOperators Topology RealInnerProductSpace
open Filter

namespace GaussianCoherent.Quadratic

 

theorem varying_dimension_packet_limit
    (κ ι ρ : ℕ → Type*) [∀n,Fintype (κ n)]
    (s : ∀n,Finset (ι n)) (d e : ∀n,ι n → RealMode (κ n))
    (ho : ∀n,∀i∈s n,∀j∈s n,i≠j → ⟪d n i,d n j⟫=0 ∧ ⟪d n i,e n j⟫=0)
    (he : ∀n,∀i∈s n,∀j∈s n,i≠j → ⟪e n i,e n j⟫=0)
    (t R M : ℝ) (hR : 0≤R)
    (u : ∀n,Finset (ρ n)) (c : ∀n,ρ n → ℂ) (v : ∀n,ρ n → Mode (κ n))
    (hv : ∀n,∀j∈u n,‖v n j‖≤R) (hc : ∀n,(∑j∈u n,‖c n j‖)≤M)
    (hk : Tendsto (fun n=>ClassicalGaussian.Shifted.kernelSq (RealMode (κ n)) (s n) (d n) (e n))
      atTop (𝓝 0)) :
    Tendsto (fun n=>‖unitary (s n) (d n) (e n) t
        (∑j∈u n,c n j • CoherentFock.coherent (v n j))-
        ∑j∈u n,c n j • CoherentFock.coherent (v n j)‖) atTop (𝓝 0) := by
  have ht : Tendsto (fun n=>M*Real.sqrt
      (t^2*ClassicalGaussian.Shifted.kernelSq (RealMode (κ n)) (s n) (d n) (e n)*packetConstant R))
      atTop (𝓝 0) := by
    have h := ((hk.const_mul (t^2)).mul_const (packetConstant R)).sqrt.const_mul M
    simpa only [mul_zero,zero_mul,Real.sqrt_zero] using h
  apply squeeze_zero (fun n=>norm_nonneg _) _ ht
  intro n
  exact (packet_error_le (s n) (d n) (e n) (ho n) (he n) t R hR (u n) (c n) (v n) (hv n)).trans
    (mul_le_mul_of_nonneg_right (hc n) (Real.sqrt_nonneg _))

 

theorem error_le_packet_error {κ ι : Type*} [Fintype κ]
    (s : Finset ι) (d e : ι → RealMode κ) (t : ℝ)
    (ψ φ : CoherentFock.Space (Mode κ)) :
    ‖unitary s d e t ψ-ψ‖≤2*‖ψ-φ‖+‖unitary s d e t φ-φ‖ := by
  calc
    _=‖(unitary s d e t ψ-unitary s d e t φ)+(unitary s d e t φ-φ)+(φ-ψ)‖ := by
      congr 1
      abel
    _≤‖unitary s d e t ψ-unitary s d e t φ‖+‖unitary s d e t φ-φ‖+‖φ-ψ‖ :=
      (norm_add_le ((unitary s d e t ψ-unitary s d e t φ)+(unitary s d e t φ-φ)) (φ-ψ)).trans
        (_root_.add_le_add (norm_add_le (unitary s d e t ψ-unitary s d e t φ)
          (unitary s d e t φ-φ)) (le_refl ‖φ-ψ‖))
    _=2*‖ψ-φ‖+‖unitary s d e t φ-φ‖ := by
      rw [←map_sub,(unitary s d e t).norm_map,norm_sub_rev φ ψ]
      ring

end GaussianCoherent.Quadratic

 

open scoped BigOperators Topology RealInnerProductSpace
open Filter

namespace ClassicalGaussian.Shifted
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}

 

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kernelSq_le_mass_square (s : Finset ι) (d e : ι → E) (p : ι → ℝ) (C : ℝ)
    (hd : ∀i∈s,‖d i‖^2≤C*p i) (he : ∀i∈s,‖e i‖^2≤C*p i) :
    kernelSq E s d e≤C^2*∑i∈s,p i^2 := by
  unfold kernelSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul (hd i hi) (he i hi) (sq_nonneg ‖e i‖)
    ((sq_nonneg ‖d i‖).trans (hd i hi))
  nlinarith

theorem mass_square_le_max (s : Finset ι) (p : ι → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hp : ∀i∈s,0≤p i) (hs : (∑i∈s,p i)≤1) (hm : ∀i∈s,p i≤δ) :
    (∑i∈s,p i^2)≤δ := by
  calc
    _≤∑i∈s,δ*p i := Finset.sum_le_sum fun i hi=>by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hm i hi) (hp i hi)
    _=δ*∑i∈s,p i := (Finset.mul_sum ..).symm
    _≤δ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hδ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kernelSq_le_max_mass (s : Finset ι) (d e : ι → E) (p : ι → ℝ) (C δ : ℝ)
    (hδ : 0≤δ) (hp : ∀i∈s,0≤p i) (hs : (∑i∈s,p i)≤1) (hm : ∀i∈s,p i≤δ)
    (hd : ∀i∈s,‖d i‖^2≤C*p i) (he : ∀i∈s,‖e i‖^2≤C*p i) :
    kernelSq E s d e≤C^2*δ :=
  (kernelSq_le_mass_square E s d e p C hd he).trans
    (mul_le_mul_of_nonneg_left (mass_square_le_max s p δ hδ hp hs hm) (sq_nonneg C))

end ClassicalGaussian.Shifted

namespace GaussianCoherent.Quadratic

 

theorem sender_dilution_limit
    (κ ι ρ : ℕ → Type*) [∀n,Fintype (κ n)]
    (s : ∀n,Finset (ι n)) (d e : ∀n,ι n → RealMode (κ n))
    (p : ∀n,ι n → ℝ) (C : ℝ) (δ : ℕ → ℝ)
    (hδ : ∀n,0≤δ n) (hp : ∀n,∀i∈s n,0≤p n i)
    (hs : ∀n,(∑i∈s n,p n i)≤1) (hm : ∀n,∀i∈s n,p n i≤δ n)
    (hd : ∀n,∀i∈s n,‖d n i‖^2≤C*p n i) (hde : ∀n,∀i∈s n,‖e n i‖^2≤C*p n i)
    (ho : ∀n,∀i∈s n,∀j∈s n,i≠j → ⟪d n i,d n j⟫=0 ∧ ⟪d n i,e n j⟫=0)
    (he : ∀n,∀i∈s n,∀j∈s n,i≠j → ⟪e n i,e n j⟫=0)
    (t R M : ℝ) (hR : 0≤R)
    (u : ∀n,Finset (ρ n)) (c : ∀n,ρ n → ℂ) (v : ∀n,ρ n → Mode (κ n))
    (hv : ∀n,∀j∈u n,‖v n j‖≤R) (hc : ∀n,(∑j∈u n,‖c n j‖)≤M)
    (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n=>‖unitary (s n) (d n) (e n) t
        (∑j∈u n,c n j • CoherentFock.coherent (v n j))-
        ∑j∈u n,c n j • CoherentFock.coherent (v n j)‖) atTop (𝓝 0) := by
  apply varying_dimension_packet_limit κ ι ρ s d e ho he t R M hR u c v hv hc
  apply squeeze_zero (fun n=>ClassicalGaussian.Shifted.kernelSq_nonneg _ _ _ _)
    (fun n=>ClassicalGaussian.Shifted.kernelSq_le_max_mass _ (s n) (d n) (e n) (p n) C (δ n)
      (hδ n) (hp n) (hs n) (hm n) (hd n) (hde n))
  simpa only [mul_zero] using hlim.const_mul (C^2)

end GaussianCoherent.Quadratic

 

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

 

def stateDistance {n : ℕ} (ψ φ : State n) : ℝ := Real.sqrt (mass (ψ-φ))

theorem normSq_sub_abs_le (z w : ℂ) :
    |Complex.normSq z-Complex.normSq w| ≤ ‖z-w‖*(‖z‖+‖w‖) := by
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,
    show ‖z‖^2-‖w‖^2=(‖z‖-‖w‖)*(‖z‖+‖w‖) by ring,abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

 

theorem sum_abs_normSq_sub_le {n : ℕ} (ψ φ : State n)
    (hψ : mass ψ=1) (hφ : mass φ=1) :
    (∑σ,|Complex.normSq (ψ σ)-Complex.normSq (φ σ)|) ≤ 2*stateDistance ψ φ := by
  have hm (v : State n) : (∑σ,‖v σ‖^2)=mass v := by
    simp only [mass,Complex.normSq_eq_norm_sq]
  calc
    _ ≤ ∑σ,‖ψ σ-φ σ‖*(‖ψ σ‖+‖φ σ‖) := Finset.sum_le_sum fun σ _ => normSq_sub_abs_le _ _
    _=(∑σ,‖ψ σ-φ σ‖*‖ψ σ‖)+(∑σ,‖ψ σ-φ σ‖*‖φ σ‖) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ Real.sqrt (mass (ψ-φ))*Real.sqrt (mass ψ)+
        Real.sqrt (mass (ψ-φ))*Real.sqrt (mass φ) := by
      apply add_le_add
      · simpa only [←hm,Pi.sub_apply] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun σ=>‖ψ σ-φ σ‖) (fun σ=>‖ψ σ‖)
      · simpa only [←hm,Pi.sub_apply] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun σ=>‖ψ σ-φ σ‖) (fun σ=>‖φ σ‖)
    _=_ := by rw [hψ,hφ,Real.sqrt_one]; simp only [mul_one,stateDistance]; ring

 

def spectralWidth (n : ℕ) (J : Disorder n) : ℝ := groundMaximum n J+groundMaximum n (-J)

theorem spectralWidth_nonneg (n : ℕ) (J : Disorder n) : 0 ≤ spectralWidth n J := by
  have h := hamiltonian_le_groundMaximum n J (fun _=>false)
  have h' := hamiltonian_le_groundMaximum n (-J) (fun _=>false)
  rw [hamiltonian_neg_disorder] at h'
  dsimp [spectralWidth]
  linarith

 
def stateEnergy (n : ℕ) (J : Disorder n) (ψ : State n) : ℝ :=
  (∑σ,Complex.normSq (ψ σ)*hamiltonian n J σ)/(n : ℝ)

theorem stateEnergy_sub_bound (n : ℕ) (J : Disorder n) (ψ φ : State n)
    (hψ : mass ψ=1) (hφ : mass φ=1) :
    |stateEnergy n J ψ-stateEnergy n J φ| ≤ 
      2*stateDistance ψ φ*(spectralWidth n J/(n : ℝ)) := by
  have hz : (∑σ,(Complex.normSq (ψ σ)-Complex.normSq (φ σ)))=0 := by
    rw [Finset.sum_sub_distrib]
    change mass ψ-mass φ=0
    rw [hψ,hφ,sub_self]
  have hb (σ : Configuration n) :
      |hamiltonian n J σ+groundMaximum n (-J)| ≤ spectralWidth n J := by
    have hn := hamiltonian_le_groundMaximum n (-J) σ
    rw [hamiltonian_neg_disorder] at hn
    rw [abs_of_nonneg (by linarith : 0 ≤ hamiltonian n J σ+groundMaximum n (-J))]
    exact _root_.add_le_add (hamiltonian_le_groundMaximum n J σ) (le_refl (groundMaximum n (-J)))
  have hs : (∑σ,Complex.normSq (ψ σ)*hamiltonian n J σ)-
      (∑σ,Complex.normSq (φ σ)*hamiltonian n J σ)=
      ∑σ,(Complex.normSq (ψ σ)-Complex.normSq (φ σ))*
        (hamiltonian n J σ+groundMaximum n (-J)) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ←Finset.sum_mul, hz, zero_mul, add_zero]
    simp only [sub_mul, Finset.sum_sub_distrib]
  unfold stateEnergy
  rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n),hs]
  calc
    _ ≤ (∑σ,|(Complex.normSq (ψ σ)-Complex.normSq (φ σ))*
        (hamiltonian n J σ+groundMaximum n (-J))|)/(n : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg n)
    _ ≤ ((∑σ,|Complex.normSq (ψ σ)-Complex.normSq (φ σ)|)*spectralWidth n J)/(n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb σ) (abs_nonneg _)
    _ ≤ (2*stateDistance ψ φ*spectralWidth n J)/(n : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sum_abs_normSq_sub_le ψ φ hψ hφ) (spectralWidth_nonneg n J))
        (Nat.cast_nonneg n)
    _=_ := by ring

end SKQAOA

 

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

theorem spectralWidth_integrable (n : ℕ) : Integrable (spectralWidth n) (disorderLaw n) :=
  (groundMaximum_integrable n).add
    ((disorder_neg_preserving n).integrable_comp_of_integrable (groundMaximum_integrable n))

theorem integral_spectralWidth_div (n : ℕ) :
    (∫J : Disorder n,spectralWidth n J/(n : ℝ) ∂disorderLaw n)=2*expectedGround n := by
  have hn : (∫J : Disorder n,groundMaximum n (-J) ∂disorderLaw n)=
      ∫J : Disorder n,groundMaximum n J ∂disorderLaw n :=
    (disorder_neg_preserving n).integral_comp
      (MeasurableEquiv.neg (Disorder n)).measurableEmbedding (groundMaximum n)
  have hi : Integrable (fun J : Disorder n=>groundMaximum n (-J)) (disorderLaw n) := by
    simpa only [Function.comp_def] using
      (disorder_neg_preserving n).integrable_comp_of_integrable (groundMaximum_integrable n)
  rw [integral_div]
  unfold spectralWidth
  rw [integral_add (groundMaximum_integrable n) hi,hn]
  unfold expectedGround
  ring

 

theorem expectedEnergy_sub_bound_of_stateDistance (n p q : ℕ)
    (γ β : Fin p → ℝ) (γ' β' : Fin q → ℝ) (δ : ℝ)
    (hδ : ∀J : Disorder n,stateDistance (qaoaState n p J γ β) (qaoaState n q J γ' β') ≤ δ) :
    |expectedEnergy n p γ β-expectedEnergy n q γ' β'| ≤ 4*δ*expectedGround n := by
  have hi := (energyDensity_integrable n p γ β).sub (energyDensity_integrable n q γ' β')
  have hb (J : Disorder n) : |energyDensity n p J γ β-energyDensity n q J γ' β'| ≤
      2*δ*(spectralWidth n J/(n : ℝ)) := by
    have h := stateEnergy_sub_bound n J (qaoaState n p J γ β) (qaoaState n q J γ' β')
      (qaoaState_mass n p J γ β) (qaoaState_mass n q J γ' β')
    rw [energyDensity_eq,energyDensity_eq]
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hδ J) (by norm_num))
      (div_nonneg (spectralWidth_nonneg n J) (Nat.cast_nonneg n)))
  unfold expectedEnergy
  rw [←integral_sub (energyDensity_integrable n p γ β) (energyDensity_integrable n q γ' β')]
  calc
    _ ≤ ∫J : Disorder n,|energyDensity n p J γ β-energyDensity n q J γ' β'| ∂disorderLaw n :=
      abs_integral_le_integral_abs
    _ ≤ ∫J : Disorder n,2*δ*(spectralWidth n J/(n : ℝ)) ∂disorderLaw n :=
      integral_mono hi.abs (((spectralWidth_integrable n).div_const (n : ℝ)).const_mul (2*δ)) hb
    _=4*δ*expectedGround n := by rw [integral_const_mul,integral_spectralWidth_div]; ring

 

theorem value_sub_bound_of_stateDistance (p q : ℕ)
    (γ β : Fin p → ℝ) (γ' β' : Fin q → ℝ) (δ : ℝ)
    (hδ : ∀ᶠ n in atTop,∀J : Disorder n,
      stateDistance (qaoaState n p J γ β) (qaoaState n q J γ' β') ≤ δ) :
    |value p γ β-value q γ' β'| ≤ 4*δ*Pstar := by
  apply le_of_tendsto_of_tendsto
    ((tendsto_expectedEnergy_value p γ β).sub (tendsto_expectedEnergy_value q γ' β')).abs
    (tendsto_expectedGround.const_mul (4*δ))
  filter_upwards [hδ] with n hn
  exact expectedEnergy_sub_bound_of_stateDistance n p q γ β γ' β' δ hn

 

theorem unitary_preserves_stateDistance {n : ℕ} {A : Operator n}
    (hA : A ∈ unitary (Operator n)) (ψ φ : State n) :
    stateDistance (A.mulVec ψ) (A.mulVec φ)=stateDistance ψ φ := by
  unfold stateDistance
  rw [←Matrix.mulVec_sub,unitary_preserves_mass hA]

end SKQAOA

 

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

theorem stateDistance_nonneg {n : ℕ} (ψ φ : State n) : 0 ≤ stateDistance ψ φ :=
  Real.sqrt_nonneg _

theorem stateDistance_le_two {n : ℕ} (ψ φ : State n)
    (hψ : mass ψ=1) (hφ : mass φ=1) : stateDistance ψ φ ≤ 2 := by
  have hm : mass (ψ-φ) ≤ 4 := by
    calc
      _ ≤ ∑σ,(2*Complex.normSq (ψ σ)+2*Complex.normSq (φ σ)) := by
        apply Finset.sum_le_sum
        intro σ _
        rw [Pi.sub_apply,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
        have h := norm_sub_le (ψ σ) (φ σ)
        nlinarith [norm_nonneg (ψ σ-φ σ),norm_nonneg (ψ σ),norm_nonneg (φ σ),
          sq_nonneg (‖ψ σ‖-‖φ σ‖)]
      _=4 := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
        change 2*mass ψ+2*mass φ=4
        rw [hψ,hφ]; norm_num
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hm⟩

theorem qaoaStateDistance_continuous (n p q : ℕ) (γ β : Fin p → ℝ) (γ' β' : Fin q → ℝ) :
    Continuous (fun J : Disorder n=>stateDistance (qaoaState n p J γ β) (qaoaState n q J γ' β')) := by
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro σ _
  exact Complex.continuous_normSq.comp
    (((continuous_apply σ).comp (qaoaState_continuous n p γ β)).sub
      ((continuous_apply σ).comp (qaoaState_continuous n q γ' β')))

 

def weightedStateError (n p q : ℕ) (γ β : Fin p → ℝ) (γ' β' : Fin q → ℝ) : ℝ :=
  ∫J : Disorder n,stateDistance (qaoaState n p J γ β) (qaoaState n q J γ' β')*
    (spectralWidth n J/(n : ℝ)) ∂disorderLaw n

theorem weightedStateError_integrable (n p q : ℕ) (γ β : Fin p → ℝ) (γ' β' : Fin q → ℝ) :
    Integrable (fun J : Disorder n=>stateDistance (qaoaState n p J γ β) (qaoaState n q J γ' β')*
      (spectralWidth n J/(n : ℝ))) (disorderLaw n) := by
  apply (((spectralWidth_integrable n).div_const (n : ℝ)).const_mul 2).mono'
  · apply Continuous.aestronglyMeasurable
    apply (qaoaStateDistance_continuous n p q γ β γ' β').mul
    apply Continuous.div_const
    exact (groundMaximum_continuous n).add ((groundMaximum_continuous n).comp continuous_neg)
  · filter_upwards [] with J
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (stateDistance_nonneg _ _)
      (div_nonneg (spectralWidth_nonneg n J) (Nat.cast_nonneg n)))]
    exact mul_le_mul_of_nonneg_right
      (stateDistance_le_two _ _ (qaoaState_mass n p J γ β) (qaoaState_mass n q J γ' β'))
      (div_nonneg (spectralWidth_nonneg n J) (Nat.cast_nonneg n))

 

theorem expectedEnergy_sub_le_weightedStateError (n p q : ℕ)
    (γ β : Fin p → ℝ) (γ' β' : Fin q → ℝ) :
    |expectedEnergy n p γ β-expectedEnergy n q γ' β'| ≤
      2*weightedStateError n p q γ β γ' β' := by
  have hi := (energyDensity_integrable n p γ β).sub (energyDensity_integrable n q γ' β')
  unfold expectedEnergy weightedStateError
  rw [←integral_sub (energyDensity_integrable n p γ β) (energyDensity_integrable n q γ' β'),
    ←integral_const_mul]
  calc
    _ ≤ ∫J : Disorder n,|energyDensity n p J γ β-energyDensity n q J γ' β'| ∂disorderLaw n :=
      abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono hi.abs ((weightedStateError_integrable n p q γ β γ' β').const_mul 2)
      intro J
      dsimp only [Pi.sub_apply]
      rw [energyDensity_eq,energyDensity_eq]
      simpa only [stateEnergy,mul_assoc] using stateEnergy_sub_bound n J
        (qaoaState n p J γ β) (qaoaState n q J γ' β')
        (qaoaState_mass n p J γ β) (qaoaState_mass n q J γ' β')

 

theorem value_eq_of_weightedStateError_tendsto_zero (p q : ℕ)
    (γ β : Fin p → ℝ) (γ' β' : Fin q → ℝ)
    (h : Tendsto (fun n=>weightedStateError n p q γ β γ' β') atTop (𝓝 0)) :
    value p γ β=value q γ' β' := by
  have hz : |value p γ β-value q γ' β'| ≤ 0 := by
    apply le_of_tendsto_of_tendsto
      ((tendsto_expectedEnergy_value p γ β).sub (tendsto_expectedEnergy_value q γ' β')).abs
      (by simpa only [mul_zero] using h.const_mul 2)
    exact Eventually.of_forall fun n=>expectedEnergy_sub_le_weightedStateError n p q γ β γ' β'
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

end SKQAOA

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter

namespace ClassicalGaussian
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

 

theorem phase_weighted_integral_le {q ρ : Ω → ℝ}
    (hq : MemLp q 2 μ) (hρ : MemLp ρ 2 μ) (hρn : ∀x,0≤ρ x) (t : ℝ) :
    (∫x,ρ x*phaseError t (q x) ∂μ)≤
      Real.sqrt (∫x,ρ x^2 ∂μ)*Real.sqrt (4*t^2*∫x,q x^2 ∂μ) := by
  have he : MemLp (fun x=>phaseError t (q x)) 2 μ := by
    apply MemLp.of_bound ((continuous_phaseError t).comp_aestronglyMeasurable hq.aestronglyMeasurable) 4
    exact Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (phaseError_nonneg _ _)]
      exact phaseError_le_four _ _
  have hi : (∫x,phaseError t (q x)^2 ∂μ)≤4*t^2*∫x,q x^2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono he.integrable_sq (hq.integrable_sq.const_mul _)
    intro x
    have ha := phaseError_nonneg t (q x)
    have hb := phaseError_le_four t (q x)
    have hc := phaseError_le_sq t (q x)
    nlinarith
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=μ) Real.HolderConjugate.two_two
    (Eventually.of_forall hρn) (Eventually.of_forall (fun x=>phaseError_nonneg t (q x)))
    (by simpa only [ENNReal.ofReal_ofNat] using hρ)
    (by simpa only [ENNReal.ofReal_ofNat] using he)
  have h' : (∫x,ρ x*phaseError t (q x) ∂μ)≤
      Real.sqrt (∫x,ρ x^2 ∂μ)*Real.sqrt (∫x,phaseError t (q x)^2 ∂μ) := by
    simpa only [Real.rpow_two,Real.sqrt_eq_rpow,one_div] using h
  exact h'.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi) (Real.sqrt_nonneg _))

 

theorem phase_varying_weight_limit
    (Ω : ℕ → Type*) [∀n,MeasurableSpace (Ω n)]
    (μ : ∀n,Measure (Ω n)) [∀n,IsFiniteMeasure (μ n)]
    (q ρ : ∀n,Ω n → ℝ) (hq : ∀n,MemLp (q n) 2 (μ n))
    (hρ : ∀n,MemLp (ρ n) 2 (μ n)) (hρn : ∀n x,0≤ρ n x)
    (C : ℝ) (hC : ∀n,(∫x,ρ n x^2 ∂μ n)≤C)
    (t : ℝ) (hq0 : Tendsto (fun n=>∫x,q n x^2 ∂μ n) atTop (𝓝 0)) :
    Tendsto (fun n=>∫x,ρ n x*phaseError t (q n x) ∂μ n) atTop (𝓝 0) := by
  have ht := ((hq0.const_mul (4*t^2)).sqrt).const_mul (Real.sqrt C)
  apply squeeze_zero (fun n=>integral_nonneg fun x=>mul_nonneg (hρn n x) (phaseError_nonneg _ _))
    (fun n=>(phase_weighted_integral_le (μ n) (hq n) (hρ n) (hρn n) t).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hC n)) (Real.sqrt_nonneg _)))
    (by simpa only [mul_zero,Real.sqrt_zero] using ht)

end ClassicalGaussian

namespace ClassicalGaussian
variable {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem phaseMultiplier_error_integral {q : Ω → ℝ}
    (hq : AEStronglyMeasurable q μ) (t : ℝ) (ψ : Lp E 2 μ) :
    ‖phaseMultiplier μ hq t ψ-ψ‖^2=
      ∫x,‖ψ x‖^2*phaseError t (q x) ∂μ := by
  rw [L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (phaseMultiplier μ hq t ψ) ψ,
    phaseMultiplier_ae μ hq t ψ] with x h1 h2
  simp only [Pi.sub_apply] at h1
  rw [h1,h2,show scalarPhase t (q x) • ψ x-ψ x=
    (scalarPhase t (q x)-1) • ψ x by rw [sub_smul,one_smul]]
  rw [norm_smul,mul_pow]
  exact mul_comm _ _

 

theorem phaseMultiplier_varying_limit
    (Ω E : ℕ → Type*) [∀n,MeasurableSpace (Ω n)]
    [∀n,NormedAddCommGroup (E n)] [∀n,InnerProductSpace ℂ (E n)]
    (μ : ∀n,Measure (Ω n)) [∀n,IsFiniteMeasure (μ n)]
    (q : ∀n,Ω n → ℝ) (hq : ∀n,MemLp (q n) 2 (μ n))
    (ψ : ∀n,Lp (E n) 2 (μ n))
    (hψ : ∀n,MemLp (fun x=>‖ψ n x‖^2) 2 (μ n))
    (C : ℝ) (hC : ∀n,(∫x,(‖ψ n x‖^2)^2 ∂μ n)≤C)
    (t : ℝ) (hq0 : Tendsto (fun n=>∫x,q n x^2 ∂μ n) atTop (𝓝 0)) :
    Tendsto (fun n=>‖phaseMultiplier (μ n) (hq n).aestronglyMeasurable t (ψ n)-ψ n‖)
      atTop (𝓝 0) := by
  have h := phase_varying_weight_limit Ω μ q (fun n x=>‖ψ n x‖^2) hq hψ
    (fun n x=>sq_nonneg _) C hC t hq0
  have he (n : ℕ) : (∫x,‖ψ n x‖^2*phaseError t (q n x) ∂μ n)=
      ‖phaseMultiplier (μ n) (hq n).aestronglyMeasurable t (ψ n)-ψ n‖^2 :=
    (phaseMultiplier_error_integral (μ n) (hq n).aestronglyMeasurable t (ψ n)).symm
  have hs := h.sqrt
  simp only [he,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
  exact hs

end ClassicalGaussian

namespace GaussianCoherent.Quadratic

 

theorem varying_dimension_L4_limit
    (κ ι : ℕ → Type*) [∀n,Fintype (κ n)]
    (s : ∀n,Finset (ι n)) (d e : ∀n,ι n → RealMode (κ n))
    (ho : ∀n,∀i∈s n,∀j∈s n,i≠j → ⟪d n i,d n j⟫=0 ∧ ⟪d n i,e n j⟫=0)
    (hk : Tendsto (fun n=>ClassicalGaussian.Shifted.kernelSq (RealMode (κ n)) (s n) (d n) (e n))
      atTop (𝓝 0)) (t : ℝ)
    (ψ : ∀n,CoherentFock.Space (Mode (κ n)))
    (hψ : ∀n,MemLp (fun g=>‖gaussianUnitary (ψ n) g‖^2) 2 (GaussianFourier.law (κ n)))
    (C : ℝ) (hC : ∀n,(∫g,(‖gaussianUnitary (ψ n) g‖^2)^2 ∂GaussianFourier.law (κ n))≤C) :
    Tendsto (fun n=>‖unitary (s n) (d n) (e n) t (ψ n)-ψ n‖) atTop (𝓝 0) := by
  have hq : Tendsto (fun n=>∫g,symbol (s n) (d n) (e n) g^2 ∂GaussianFourier.law (κ n))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>integral_nonneg fun g=>sq_nonneg _)
      (fun n=>symbol_second_moment_le (s n) (d n) (e n) (ho n))
    simpa only [mul_zero] using hk.const_mul 2
  have h := ClassicalGaussian.phaseMultiplier_varying_limit
    (fun n=>κ n → ℝ) (fun _=>ℂ) (fun n=>GaussianFourier.law (κ n))
    (fun n=>symbol (s n) (d n) (e n)) (fun n=>memLp_symbol (s n) (d n) (e n))
    (fun n=>gaussianUnitary (ψ n)) hψ C hC t hq
  have hn (n : ℕ) : ‖unitary (s n) (d n) (e n) t (ψ n)-ψ n‖=
      ‖ClassicalGaussian.phaseMultiplier (GaussianFourier.law (κ n))
        (memLp_symbol (s n) (d n) (e n)).aestronglyMeasurable t (gaussianUnitary (ψ n))-
        gaussianUnitary (ψ n)‖ := by
    rw [←gaussianUnitary.norm_map (unitary (s n) (d n) (e n) t (ψ n)-ψ n)]
    rw [map_sub,gaussian_unitary_apply]
  simpa only [hn] using h

end GaussianCoherent.Quadratic

 

open scoped Topology
open MeasureTheory Filter

namespace SKQAOA

 

theorem tendsto_integral_groundMaximum_atTop :
    Tendsto (fun n => ∫ J : Disorder n, groundMaximum n J ∂disorderLaw n) atTop atTop := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos
    Pstar_pos tendsto_expectedGround
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  dsimp only [expectedGround]
  rw [mul_div_cancel₀ _ hne]

 

theorem not_bddAbove_integral_groundMaximum :
    ¬ BddAbove (Set.range (fun n => ∫ J : Disorder n, groundMaximum n J ∂disorderLaw n)) :=
  not_bddAbove_of_tendsto_atTop tendsto_integral_groundMaximum_atTop

end SKQAOA

end

end OAI
