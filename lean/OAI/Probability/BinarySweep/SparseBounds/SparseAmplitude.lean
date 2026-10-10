import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.SparseKernel
import OAI.Probability.BinarySweep.Trajectories.EndpointPlacement

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma placementProbability_uniform_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    (gridSize bits : ℝ)^k * placementProbability H z x y ≤
      Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hp := placementProbability_nonneg H hz hz1 x y
  by_cases hp0 : placementProbability H z x y=0
  · rw [hp0,mul_zero]; exact (Real.exp_pos _).le
  have hp' : 0<placementProbability H z x y := lt_of_le_of_ne hp (Ne.symm hp0)
  have hb := placement_probability_cost_of_pos H hd hz hzr x y hp'
  have hc : placementTransitionCost H z x y ≤ (b:ℝ)*(h+k) := by
    unfold placementTransitionCost
    rw [dite_eq_left hp']
    simpa only [Nat.cast_add] using pathCost_le
      (augmentByChoice H x (realizePlacement H z x y hp'))
  have hpow : (gridSize bits:ℝ)^k * (gridSize bits:ℝ)^(-(k:ℝ))=1 := by
    rw [Real.rpow_neg hs.le,Real.rpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ hs.ne')
  calc
    _ ≤ (gridSize bits:ℝ)^k * ((gridSize bits:ℝ)^(-(k:ℝ)) *
        Real.exp (placementTransitionCost H z x y-pathCost H+Real.log 4*k*b)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs.le _)
    _ = Real.exp (placementTransitionCost H z x y-pathCost H+Real.log 4*k*b) := by
      rw [← mul_assoc,hpow,one_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [pathCost_nonneg H])

lemma endpointProbability_scaled_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H z A (fun i => ((x i).val,(y i).val)) ≤
      Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  rw [endpointProbability_placement]
  have hb := placementProbability_uniform_bound H hd hz hzr hz1
    (restrictPlacement H x A) (restrictPlacement H y A)
  simp only [Fintype.card_coe] at hb
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  have hk : (A.card:ℝ) ≤ k := by exact_mod_cast (show A.card ≤ k from (by simpa only [Fintype.card_fin] using A.card_le_univ))
  have hl : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hbk := mul_le_mul_of_nonneg_left hk (show (0:ℝ)≤b by positivity)
  have hbkl := mul_le_mul_of_nonneg_left hbk hl
  nlinarith

lemma alternatingSubsetSum_abs_le {I : Type*} [DecidableEq I] (U : Finset I)
    (s : ℝ) (p : Finset I → ℝ) (C : ℝ)
    (hp : ∀ A ⊆ U, 0 ≤ s^A.card*p A ∧ s^A.card*p A ≤ C) :
    |alternatingSubsetSum U s p|≤(2:ℝ)^U.card*C := by
  unfold alternatingSubsetSum
  calc
    _ ≤ ∑A ∈ U.powerset, |(-1:ℝ)^(U.card-A.card)*s^A.card*p A| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_A ∈ U.powerset, C := by
      apply Finset.sum_le_sum
      intro A hA
      rw [mul_assoc,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
        abs_of_nonneg (hp A (Finset.mem_powerset.mp hA)).1]
      exact (hp A (Finset.mem_powerset.mp hA)).2
    _ = _ := by simp

theorem centeredEndpointKernel_amplitude (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    |(gridSize bits:ℝ)^k * centeredEndpointKernel H z (fun i => ((x i).val,(y i).val))| ≤
      (2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  unfold centeredEndpointKernel
  simp only [Fintype.card_fin]
  rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ (by exact_mod_cast (gridSize_pos bits).ne'),
    one_pow,one_mul]
  have hb := alternatingSubsetSum_abs_le Finset.univ (gridSize bits)
    (fun A => endpointProbability H z A (fun i => ((x i).val,(y i).val)))
    (Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b)) (by
      intro A _
      constructor
      · rw [endpointProbability_placement]
        exact mul_nonneg (by positivity) (placementProbability_nonneg H hz hz1 _ _)
      · exact endpointProbability_scaled_bound H hd hz hzr hz1 x y A)
  simpa only [Finset.card_univ,Fintype.card_fin] using hb

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {P Ω I : Type*} [Fintype P] [Fintype Ω] [Fintype I] [DecidableEq I]

lemma productProbability_uniform (E : (I → Ω) → Prop) :
    productProbability uniformWeight E=finiteProbability uniformWeight E := by
  unfold productProbability finiteProbability productWeight uniformWeight
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,one_div,inv_pow]

lemma sum_injective_le (f : P → Ω) (hi : Function.Injective f) (w : Ω → ℝ)
    (hw : ∀u, 0≤w u) : ∑i, w (f i) ≤ ∑u, w u := by
  classical
  rw [← Finset.sum_image (fun x _ y _ hxy => hi hxy)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u _ _ => hw u)

theorem sum_square_le_uniform_event (f : P → Ω) (hi : Function.Injective f)
    (Q : Ω → ℝ) (a C : ℝ) (ha : 0<a) (hC : 0≤C)
    (hN : (Fintype.card Ω:ℝ)=a^2) (hb : ∀i, |a*Q (f i)|≤C) :
    ∑i, (Q (f i))^2 ≤ C^2 * finiteProbability uniformWeight (fun u => Q u≠0) := by
  have hcard : (Fintype.card Ω:ℝ)≠0 := by rw [hN]; positivity
  have hp : (Fintype.card Ω:ℝ)*finiteProbability uniformWeight (fun u => Q u≠0) =
      ∑u : Ω, if Q u≠0 then (1:ℝ) else 0 := by
    unfold finiteProbability uniformWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [← mul_assoc,mul_one_div_cancel hcard,one_mul]
    split_ifs <;> rfl
  have hle : a^2*(∑i, (Q (f i))^2) ≤
      ∑u : Ω, if Q u≠0 then C^2 else 0 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans
      (sum_injective_le f hi (fun u => if Q u≠0 then C^2 else 0)
        (fun u => by
          split_ifs
          · exact pow_nonneg hC 2
          · exact le_rfl))
    by_cases hz : Q (f i)=0
    · simp only [hz,ne_eq,not_true_eq_false,ite_false,zero_pow (by decide : 2≠0),mul_zero]
      exact le_rfl
    · rw [ite_eq_left hz,← mul_pow]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
  have he : (∑u : Ω, if Q u≠0 then C^2 else 0)=
      C^2 * ((Fintype.card Ω:ℝ)*finiteProbability uniformWeight (fun u => Q u≠0)) := by
    rw [hp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  rw [he,hN] at hle
  nlinarith [sq_pos_of_pos ha]

end BinaryCoordinateSweeps.Sparse
namespace BinaryCoordinateSweeps
open Sparse

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

 def placementEndpointArray (xy : Placement H k 0 × Placement H k (Fin.last b)) :
    Fin k → GridSlot bits × GridSlot bits := fun i => ((xy.1 i).val,(xy.2 i).val)

lemma placementEndpointArray_injective : Function.Injective (placementEndpointArray (k:=k) H) := by
  intro x y he
  apply Prod.ext
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun z => (z i).1) he
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun z => (z i).2) he

theorem centeredEndpointKernel_hs_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (hsmall : ((k+h:ℕ):ℝ) * (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) ≤ 1) :
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) ≤
      ((2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
        ((2:ℝ)^k * (((k+h:ℕ):ℝ) *
          (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)))^((k+1)/2)) := by
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hN : (Fintype.card (Fin k → GridSlot bits × GridSlot bits):ℝ)=((gridSize bits:ℝ)^k)^2 := by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,card_gridSlot,Nat.cast_pow,Nat.cast_mul,mul_pow,pow_two]
  have he := sum_square_le_uniform_event (placementEndpointArray (k:=k) H)
    (placementEndpointArray_injective H) (centeredEndpointKernel H z)
    ((gridSize bits:ℝ)^k) ((2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))
    (pow_pos hs _) (by positivity) hN (fun xy => centeredEndpointKernel_amplitude H hd hz hzr hz1 xy.1 xy.2)
  rw [← productProbability_uniform] at he
  have hp := centeredEndpointKernel_exceptional_probability (I:=Fin k) H z
    (by simpa only [Fintype.card_fin] using hsmall)
  simp only [Fintype.card_fin] at hp
  have heq : (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) =
      ∑xy : Placement H k 0 × Placement H k (Fin.last b),
        (centeredEndpointKernel H z (placementEndpointArray H xy))^2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr
    · ext x; simp only [Finset.mem_univ]
    intro x _
    apply Finset.sum_congr
    · ext y; simp only [Finset.mem_univ]
    intro y _
    rfl
  rw [heq]
  exact he.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg _))

end BinaryCoordinateSweeps

end

end OAI
