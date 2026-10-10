import OAI.Analysis.Laughlin.Charge.Number
import OAI.Analysis.Laughlin.Charge.Comparison

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators InnerProductSpace

theorem energy_smul (Q : ℕ) (c : ℂ) (x : Hilbert Q) :
    energy Q (c • x)=‖c‖^2*energy Q x := by
  simp only [energy,map_smul,sourceFockEnergy,
    occupationNormSq_smul,Finset.mul_sum]

theorem energy_sub_kernel (Q : ℕ) (x y : Hilbert Q)
    (hy : euclideanFockHamiltonian Q y=0) : energy Q (x-y)=energy Q x := by
  rw [energy_eq_inner,energy_eq_inner,map_sub,hy,sub_zero,inner_sub_right,
    euclideanFockHamiltonian_symmetric Q x y,hy,inner_zero_right,sub_zero]

theorem neutralGap_mul_norm_le (Q n : ℕ) (x : Hilbert Q)
    (hxS : x ∈ particleSector Q n) (hxK : x ∈ (groundKernel Q n)ᗮ) :
    neutralGap Q n*‖x‖^2≤energy Q x := by
  by_cases hx : x=0
  · subst x
    simp [energy,sourceFockEnergy,occupationNormSq]
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  let u := (‖x‖ : ℂ)⁻¹ • x
  have hu : u ∈ unitSector Q n := by
    refine ⟨(particleSector Q n).smul_mem _ hxS,?_⟩
    dsimp [u]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x),inv_mul_cancel₀ hn]
    norm_num
  have hg : neutralGap Q n≤energy Q u := by
    apply csInf_le
    · exact ⟨0,by rintro t ⟨v,hv,rfl⟩; exact energy_nonneg Q v⟩
    · exact ⟨u,⟨hu,(groundKernel Q n)ᗮ.smul_mem _ hxK⟩,rfl⟩
  dsimp [u] at hg
  rw [energy_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x)] at hg
  have hm := mul_le_mul_of_nonneg_left hg (sq_nonneg ‖x‖)
  field_simp [hn] at hm
  nlinarith

theorem neutralGap_projection_bound (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ particleSector Q n) :
    neutralGap Q n*(‖x‖^2-‖(groundKernel Q n).starProjection x‖^2)≤energy Q x := by
  let K := groundKernel Q n
  have hpK := K.starProjection_apply_mem x
  have hpS : K.starProjection x ∈ particleSector Q n := hpK.1
  have h := neutralGap_mul_norm_le Q n (x-K.starProjection x)
    ((particleSector Q n).sub_mem hx hpS) (K.sub_starProjection_mem_orthogonal x)
  rw [energy_sub_kernel Q x (K.starProjection x) hpK.2] at h
  have hnorm : ‖x-K.starProjection x‖^2=‖x‖^2-‖K.starProjection x‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),inner_re_symm]
    have hp := K.re_inner_starProjection_eq_normSq x
    change RCLike.re (inner ℂ (K.starProjection x) x)=‖K.starProjection x‖^2 at hp
    rw [hp]
    ring
  rwa [hnorm] at h

theorem lnwyRecursionInput : LNWYRecursionInput := by
  intro Q n hn hzero x hx
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (Q+1))))
    (fun i _ => neutralGap_projection_bound Q n (annihilator Q i x)
      (annihilator_mem_sector Q n x hx.1 i))
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,annihilator_norm_sum Q (n+1) x hx.1,
    hx.2,mul_one,annihilator_energy_sum Q n x hx.1] at hs
  simpa only [groundOverlap,hzero,mul_zero,zero_add,Nat.cast_add,Nat.cast_one] using hs

theorem groundEnergy_predecessor_zero (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ unitSector Q (n+1)) (hE : energy Q x=0) : groundEnergy Q n=0 := by
  have hsum := annihilator_norm_sum Q (n+1) x hx.1
  have hi : ∃ i : Fin (Q+1), annihilator Q i x≠0 := by
    by_contra h
    push Not at h
    simp only [h,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,
      hx.2,mul_one,Nat.cast_add,Nat.cast_one] at hsum
    have hn : (0 : ℝ)≤n := Nat.cast_nonneg n
    linarith
  obtain ⟨i,hi⟩ := hi
  have hsumE : (∑ j : Fin (Q+1), energy Q (annihilator Q j x))=0 := by
    rw [annihilator_energy_sum Q n x hx.1,hE,mul_zero]
  have hEi : energy Q (annihilator Q i x)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => energy_nonneg Q _)).mp hsumE i
      (Finset.mem_univ i)
  let v := annihilator Q i x
  let u := (‖v‖ : ℂ)⁻¹ • v
  have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hi
  have hu : u ∈ unitSector Q n := by
    refine ⟨(particleSector Q n).smul_mem _ (annihilator_mem_sector Q n x hx.1 i),?_⟩
    dsimp [u]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hn]
    norm_num
  apply groundEnergy_eq_zero_of_zero_mode Q n u hu
  dsimp only [u]
  rw [energy_smul]
  change ‖(‖v‖ : ℂ)⁻¹‖^2*energy Q (annihilator Q i x)=0
  rw [hEi,mul_zero]

end Laughlin.Charge

end OAI
