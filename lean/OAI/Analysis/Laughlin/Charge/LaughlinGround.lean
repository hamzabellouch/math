import OAI.Analysis.Laughlin.Charge.Tensor
import OAI.Analysis.Laughlin.Charge.Recursion

namespace OAI

namespace Laughlin

theorem haldaneKernelInput : HaldaneKernelInput := by
  intro N hN ψ hψ hE
  exact (physical_Laughlin_kernel hN ψ hψ).mp hE

namespace Charge
open Fock
open scoped BigOperators InnerProductSpace

noncomputable def physicalLaughlin (n : ℕ) : Hilbert (3*(n-1)) :=
  occupationEuclidean (3*(n-1))
    (normalizedTensorExterior n (3*(n-1)) (laughlinVector n (3*(n-1))))

theorem physicalLaughlin_sector (n : ℕ) :
    physicalLaughlin n ∈ particleSector (3*(n-1)) n := by
  intro A hA
  exact normalizedTensorExterior_fockDegree n (3*(n-1)) _ A (by exact_mod_cast hA)

theorem physicalLaughlin_ne_zero (n : ℕ) : physicalLaughlin n ≠ 0 := by
  intro hz
  have hx : normalizedTensorExterior n (3*(n-1)) (laughlinVector n (3*(n-1)))=0 := by
    apply (occupationEuclidean (3*(n-1))).injective
    simpa only [physicalLaughlin,map_zero] using hz
  have hread := normalizedTensorReadout_left_inverse n (3*(n-1))
    (laughlinVector n (3*(n-1))) (laughlinVector_antisymmetric n)
  rw [hx] at hread
  have hzero : normalizedTensorReadout n (3*(n-1)) 0=0 := by
    funext a
    simp [normalizedTensorReadout,occupationInner]
  rw [hzero] at hread
  exact laughlinVector_ne_zero n hread.symm

theorem physicalLaughlin_zero_energy (n : ℕ) (hn : 2≤n) :
    energy (3*(n-1)) (physicalLaughlin n)=0 := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+2 := ⟨n-2,by omega⟩
  change sourceFockEnergy _ ((occupationEuclidean _).symm (occupationEuclidean _ _))=0
  rw [LinearEquiv.symm_apply_apply,normalizedTensorExterior_energy k _ _
    (laughlinVector_antisymmetric (k+2)),laughlinVector_zero_energy (by omega)]

theorem normalizedTensorExterior_smul (n Q : ℕ) (c : ℂ) (ψ : State n Q) :
    normalizedTensorExterior n Q (fun a => c*ψ a) = c • normalizedTensorExterior n Q ψ := by
  simp only [normalizedTensorExterior,tensorExterior_smul,smul_smul,mul_comm]

theorem physical_kernel_eq_laughlin (n : ℕ) (hn : 2≤n)
    (x : Hilbert (3*(n-1))) (hx : x ∈ groundKernel (3*(n-1)) n) :
    ∃ c : ℂ, x=c • physicalLaughlin n := by
  let Q := 3*(n-1)
  let y := (occupationEuclidean Q).symm x
  have hy : FockDegree Q (n : ℤ) y := by
    intro A hA
    have hv := congrArg (fun z : Hilbert Q => z A) ((occupationEuclidean Q).apply_symm_apply x)
    change (occupationBasis Q).repr y A = x A at hv
    exact hv.trans (hx.1 A (by exact_mod_cast hA))
  have hE : sourceFockEnergy Q y=0 := (energy_eq_zero_iff Q x).mpr hx.2
  have hreadE : Laughlin.energy (normalizedTensorReadout n Q y)=0 := by
    obtain ⟨k,hk⟩ : ∃ k, n=k+2 := ⟨n-2,by omega⟩
    rw [hk]
    exact normalizedTensorReadout_zero_energy k Q y hE
  obtain ⟨c,hc⟩ := (physical_Laughlin_kernel hn _
    (normalizedTensorReadout_antisymmetric n Q y)).mp hreadE
  refine ⟨c,?_⟩
  apply (occupationEuclidean Q).symm.injective
  change y=(occupationEuclidean Q).symm (c • occupationEuclidean Q _)
  rw [map_smul,LinearEquiv.symm_apply_apply]
  rw [← normalizedTensorExterior_readout n Q y hy,hc,normalizedTensorExterior_smul]

theorem physical_groundKernel_finrank (n : ℕ) (hn : 2≤n) :
    Module.finrank ℂ (groundKernel (3*(n-1)) n)=1 := by
  have hvK : physicalLaughlin n ∈ groundKernel (3*(n-1)) n :=
    ⟨physicalLaughlin_sector n,(energy_eq_zero_iff _ _).mp (physicalLaughlin_zero_energy n hn)⟩
  apply finrank_eq_one_iff'.mpr
  refine ⟨⟨physicalLaughlin n,hvK⟩,?_,?_⟩
  · intro hz
    exact physicalLaughlin_ne_zero n (congrArg Subtype.val hz)
  · intro w
    obtain ⟨c,hc⟩ := physical_kernel_eq_laughlin n hn w w.property
    exact ⟨c,Subtype.ext hc.symm⟩

theorem physicalLaughlin_unit_zero_mode (n : ℕ) (hn : 2≤n) :
    ∃ u : Hilbert (3*(n-1)), u ∈ unitSector (3*(n-1)) n ∧ energy (3*(n-1)) u=0 := by
  let v := physicalLaughlin n
  let u := (‖v‖ : ℂ)⁻¹ • v
  have hv : ‖v‖≠0 := norm_ne_zero_iff.mpr (physicalLaughlin_ne_zero n)
  refine ⟨u,⟨(particleSector _ _).smul_mem _ (physicalLaughlin_sector n),?_⟩,?_⟩
  · dsimp [u]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hv]
    norm_num
  · rw [energy_smul,physicalLaughlin_zero_energy n hn,mul_zero]

theorem laughlinChargeGroundInput : LaughlinChargeGroundInput := by
  intro n hn
  obtain ⟨u,hu,hE⟩ := physicalLaughlin_unit_zero_mode n hn
  refine ⟨groundEnergy_eq_zero_of_zero_mode _ _ u hu hE,?_,physical_groundKernel_finrank n hn⟩
  apply groundEnergy_predecessor_zero (3*(n-1)) (n-1) u
  · simpa only [Nat.sub_add_cancel (show 1≤n by omega)] using hu
  · exact hE

end Charge
end Laughlin

end OAI
