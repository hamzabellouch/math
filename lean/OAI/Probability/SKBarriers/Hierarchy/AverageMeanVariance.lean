import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinFieldVariance
import OAI.Probability.SKBarriers.Gaussian.BlockStein

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fieldIndex_eq_natAdd (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    fieldIndex D N k b i = Fin.natAdd D (finProdFinEquiv (b,i)) := by
  apply Fin.ext
  change D+b.val*N+i.val = D+(i.val+N*b.val)
  ring

def blockInteraction {D N k : ℕ} (I : Fin D → Finset (Fin N)) :
    Fin (blockDimension D N k) → Finset (Fin N) :=
  Fin.addCases I (fun t => {(finProdFinEquiv.symm t).2})

def blockCoefficients {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    Fin (blockDimension D N k) → ℝ := Fin.addCases a (fun t => v (finProdFinEquiv.symm t).1)

@[simp] theorem blockInteraction_field {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (b : Fin (k+1)) (i : Fin N) : blockInteraction (k := k) I (fieldIndex D N k b i) = {i} := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockInteraction,Fin.addCases_right,Equiv.symm_apply_apply]

@[simp] theorem blockCoefficients_field {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ)
    (b : Fin (k+1)) (i : Fin N) : blockCoefficients (N := N) a v (fieldIndex D N k b i) = v b := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockCoefficients,Fin.addCases_right,Equiv.symm_apply_apply]

def blockExponent {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) := spinExponent (blockDimension D N k) (blockCoefficients a v) (blockInteraction I)

theorem blockExponent_field {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) (b : Fin (k+1)) (i : Fin N) (s : Config N) :
    blockExponent I a v s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) = v b*spin (s i) := by
  simp only [blockExponent,spinExponent,coordinateLinear_coordinateAxis,blockCoefficients_field,
    blockInteraction_field,spinMonomial,Finset.prod_singleton]

theorem blockCoefficients_squares {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ) :
    (∑ t, (blockCoefficients (N := N) a v t)^2) =
      (∑ t, (a t)^2)+(N : ℝ)*∑ b, (v b)^2 := by
  rw [Fin.sum_univ_add]
  simp only [blockCoefficients,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => (v (finProdFinEquiv.symm t).1)^2)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Finset.mul_sum]

theorem blockExponent_expansion {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) (s : Config N) (z : ParameterSpace (blockDimension D N k)) :
    blockExponent I a v s z =
      (∑ t : Fin D, a t*spinMonomial s (I t)*coordinateProjection (blockDimension D N k) (Fin.castAdd ((k+1)*N) t) z)+
      ∑ b : Fin (k+1), ∑ i : Fin N, v b*spin (s i)*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) z := by
  unfold blockExponent spinExponent
  rw [coordinateLinear_apply,Fin.sum_univ_add]
  simp only [blockCoefficients,blockInteraction,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => v (finProdFinEquiv.symm t).1*
    spinMonomial s {(finProdFinEquiv.symm t).2}*
      coordinateProjection (blockDimension D N k) (Fin.natAdd D t) z)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,spinMonomial,Finset.prod_singleton,
    fieldIndex_eq_natAdd]

def blockFieldEnergy {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (sz : Config N × ParameterSpace (blockDimension D N k)) : ℝ :=
  (∑ b : Fin (k+1), ∑ i : Fin N,
    v b*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) sz.2*spin (sz.1 i))/(N : ℝ)

theorem blockFieldEnergy_exponent {D N k : ℕ} (I : Fin D → Finset (Fin N)) (v : Fin (k+1) → ℝ)
    (sz : Config N × ParameterSpace (blockDimension D N k)) :
    blockFieldEnergy v sz = blockExponent I (fun _ => 0) (fun b => v b/(N : ℝ)) sz.1 sz.2 := by
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,blockFieldEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem blockFieldEnergy_variance {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v w : Fin (k+1) → ℝ) :
    ProbabilityTheory.variance (blockFieldEnergy (D := D) (N := N) w)
      (hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) (blockExponent I a v)) ≤
        (∑ b, (w b)^2)/(N : ℝ) := by
  have hm := blockMass_valid D N k
  rw [hierarchyGaussianLaw_eq _ _ hm.1 hm.2.1 hm.2.2]
  have he : blockFieldEnergy (D := D) (N := N) w = fun sz =>
      blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ)) sz.1 sz.2 :=
    funext (blockFieldEnergy_exponent I w)
  rw [he]
  simp only [blockExponent]
  have H := hierarchy_spin_variance_probability (blockDimension D N k) (blockMass D N k)
    hm.1 hm.2.1 hm.2.2 (blockCoefficients a v) (blockCoefficients (fun _ => 0) (fun b => w b/(N : ℝ)))
    (blockInteraction I)
  change _ ≤ _ at H
  rw [blockCoefficients_squares] at H
  simp only [zero_pow (by omega : 2 ≠ 0),Finset.sum_const_zero,zero_add,div_pow,← Finset.sum_div] at H
  by_cases hN : N=0
  · subst N
    simpa only [Nat.cast_zero,mul_zero,zero_mul,div_zero] using H
  · have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    exact H.trans_eq (by field_simp)
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section PathMarginal
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
theorem hierarchyGaussian_probability (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) : IsProbabilityMeasure (hierarchyGaussianLaw n m U) := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  exact spinGaussianLaw_probability n _ (hierarchyPotential_boundedDerivs n m U)

theorem hierarchyGaussian_path_marginal (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (h : ParameterSpace n → ℝ)
    (hc : Continuous h) (hg : HasExpGrowth h) :
    (∫ sz, h sz.2 ∂hierarchyGaussianLaw n m U) =
      ∫ z, h z ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  have H := hierarchyGaussian_terminal_marginal n m U (fun _ => 1) h hc hg
  simpa only [affineMoment,mul_one,affineGibbs_sum,one_mul] using H
end PathMarginal

theorem pairCoefficients_squared_sum (n : ℕ) (p q : Fin n) (hpq : p ≠ q) (a b : ℝ) :
    (∑ t, (pairCoefficients n p q a b t)^2) = a^2+b^2 := by
  have he (t : Fin n) : (pairCoefficients n p q a b t)^2 =
      (if t=p then a^2 else 0)+(if t=q then b^2 else 0) := by
    unfold pairCoefficients
    split_ifs with h₁ h₂ h₂
    · exact (hpq (h₁.symm.trans h₂)).elim
    · ring
    · ring
    · ring
  simp only [he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

def sharedBlockWeights (k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k) :=
  pairCoefficients (k+1) j.castSucc j.succ (Real.sqrt (Δ j.castSucc))⁻¹ (-(Real.sqrt (Δ j.succ))⁻¹)

def sharedFieldEnergy (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k) :=
  blockFieldEnergy (D := D) (N := N) (sharedBlockWeights k Δ j)

theorem sharedFieldEnergy_expansion (D N k : ℕ) (Δ : Fin (k+1) → ℝ) (j : Fin k)
    (sz : Config N × ParameterSpace (blockDimension D N k)) :
    sharedFieldEnergy D N k Δ j sz =
      (∑ i, coordinateLinear (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i) sz.2*spin (sz.1 i))/(N : ℝ) := by
  unfold sharedFieldEnergy blockFieldEnergy
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sharedBlockWeights,pairCoefficients,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,sharedFieldCoefficients,coordinateLinear_pair]

theorem sharedFieldEnergy_variance {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b) (j : Fin k) :
    ProbabilityTheory.variance (sharedFieldEnergy D N k Δ j)
      (hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k)
        (blockExponent I a (fun b => Real.sqrt (Δ b)))) ≤
      ((Δ j.castSucc)⁻¹+(Δ j.succ)⁻¹)/(N : ℝ) := by
  have H := blockFieldEnergy_variance I a (fun b => Real.sqrt (Δ b)) (sharedBlockWeights k Δ j)
  have hpq : j.castSucc ≠ j.succ := by
    intro hh
    have h := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_succ] at h
    omega
  simp only [sharedBlockWeights,pairCoefficients_squared_sum _ _ _ hpq,neg_sq,inv_pow,
    Real.sq_sqrt (hΔ _).le] at H
  exact H

theorem blockFieldEnergy_memLp_two {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v w : Fin (k+1) → ℝ) :
    MemLp (blockFieldEnergy (D := D) (N := N) w) 2
      (hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) (blockExponent I a v)) := by
  have he : blockFieldEnergy (D := D) (N := N) w = fun sz =>
      blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ)) sz.1 sz.2 :=
    funext (blockFieldEnergy_exponent I w)
  rw [he]
  let L : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ :=
    blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ))
  have hg (s : Config N) : HasExpGrowth (fun z => L s z) := HasExpGrowth.linear (L s)
  have hc (s : Config N) : Continuous (fun z => L s z) := (L s).continuous
  exact hierarchyGaussian_memLp_two (blockDimension D N k) (blockMass D N k)
    (blockExponent I a v) (fun s z => L s z) hg hc
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Integrals
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
theorem integral_normalized_sum_identity {N : ℕ} (A : Fin N → Ω → ℝ) (B : Fin N → Ω' → ℝ)
    (w : ℝ) (hA : ∀ i, Integrable (A i) μ) (hB : ∀ i, Integrable (B i) ν)
    (hid : ∀ i, (∫ z, A i z ∂μ) = -w*(∫ z, B i z ∂ν)) :
    (∫ z, (∑ i, A i z)/(N : ℝ) ∂μ) = -w*(∫ z, (∑ i, B i z)/(N : ℝ) ∂ν) := by
  rw [integral_div,integral_div,integral_finsetSum _ (fun i _ => hA i),
    integral_finsetSum _ (fun i _ => hB i)]
  simp only [hid,← Finset.mul_sum,mul_div_assoc]
end Integrals

section BlockMean
variable {D N k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem blockField_coordinate_mean (j : Fin k) (i : Fin N) :
    (∫ sz, coordinateLinear (blockDimension D N k) (sharedFieldCoefficients D N k Δ j i) sz.2*
      spin (sz.1 i) ∂hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) U) =
      -hierarchyAtom (blockDimension D N k) (blockMass D N k) 1 (blockLevel D N k j.castSucc) *
        ∫ z, (hierarchySpinMean (blockDimension D N k) (blockMass D N k) U (fun s => spin (s i))
          (blockLevel D N k j.castSucc) z)^2
        ∂hierarchyPathLaw (blockDimension D N k) (blockMass D N k) (affineLogPartition (fun _ => 0) U) 0 := by
  let n := blockDimension D N k
  let J := blockLevel D N k j.castSucc
  let u := retainedFieldDirection D N k Δ j.castSucc i
  let v := -retainedFieldDirection D N k Δ j.succ i
  have hu : TailZero n J u :=
    (tailZero_coordinateAxis n _ _ (fieldIndex_lt_level D N k j.castSucc i)).smul _
  have hv : PrefixZero n J v := by
    simpa only [v,retainedFieldDirection,neg_smul] using
      (prefixZero_coordinateAxis n _ _ (blockLevel_prefix_second D N k j i)).smul (-(Real.sqrt (Δ j.succ))⁻¹)
  have ha : coordinateVector n (sharedFieldCoefficients D N k Δ j i) = u+v := by
    dsimp only [n]
    simp only [sharedFieldCoefficients,coordinateVector_pair,u,v,retainedFieldDirection,neg_smul]
  have hf : hierarchyMomentLevel n (blockMass D N k) (affineLogPartition (fun _ => 0) U)
      (fun _ => (1 : ℝ)) J = fun _ => 1 := by
    exact hierarchyMomentLevel_family n (blockMass D N k) _ (fun (_ : Unit) (_ : ParameterSpace n) => (0 : ℝ))
      (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun _ => 1) J
  have H := hierarchyGaussian_retained_stein n (blockMass D N k) U (fun s => spin (s i))
    (fun _ => 1) (C := 1) (D := 1) (by norm_num) (by norm_num)
    (by intro s; cases s i <;> norm_num [spin]) (by intro z; norm_num) contDiff_const
    (by have he : fderiv ℝ (fun _ : ParameterSpace n => (1 : ℝ)) = fun _ => 0 := by
          funext z
          exact fderiv_const_apply 1
        rw [he]
        exact HasExpGrowth.const (E := ParameterSpace n) (0 : ParameterSpace n →L[ℝ] ℝ))
    (sharedFieldCoefficients D N k Δ j i) J J le_rfl u v ha hu hv
    (retainedFieldDirection_spin U Δ hΔ hU j.castSucc i)
    (sharedField_termination U Δ hΔ hU j i)
    (sharedField_atom_cancellation U Δ hΔ hU j i)
    (by intro z t; rfl) hf
  simpa only [mul_one,← pow_two] using H

theorem sharedFieldEnergy_mean (hN : 0 < N) (j : Fin k) :
    (∫ sz, sharedFieldEnergy D N k Δ j sz
      ∂hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) U) =
      -((k+1 : ℕ) : ℝ)⁻¹ *
        hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k) U (fun i s => spin (s i))
          (blockLevel D N k j.castSucc) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let J := blockLevel D N k j.castSucc
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hA (i : Fin N) : Integrable
      (fun sz => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) sz.2*c i sz.1)
      (hierarchyGaussianLaw n m U) := by
    apply hierarchyGaussian_integrable n m U (fun s z => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) z*c i s)
    · intro s
      exact (HasExpGrowth.linear _).mul (HasExpGrowth.const _)
    · intro s
      exact (coordinateLinear n _).continuous.mul continuous_const
  have hB (i : Fin N) : Integrable
      (fun z => (hierarchySpinMean n m U (c i) J z)^2)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
    have hr := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) J
    apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
      (hr.1.pow 2) (C := 1) _ 0
    intro z
    dsimp only [Pi.pow_apply]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hr.2 z)
  have H := integral_normalized_sum_identity _ _ (hierarchyAtom n m 1 J) hA hB
    (blockField_coordinate_mean U Δ hΔ hU j)
  simp only [sharedFieldEnergy_expansion]
  change _ = -((k+1 : ℕ) : ℝ)⁻¹ * ∫ z, (∑ i, (hierarchySpinMean n m U (c i) J z)^2)/(N : ℝ)
    ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  rw [H]
  rw [show hierarchyAtom n m 1 J = ((k+1 : ℕ) : ℝ)⁻¹ by
    exact (hierarchyAtom_blockMass D N k J).trans (blockAtom_at D N k hN j.castSucc)]
end BlockMean
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section BoundedMeanObservable
variable {S : Type} [Fintype S] [Nonempty S]
theorem hierarchyMeanSquare_norm_le_one {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (z : ParameterSpace n) :
    ‖hierarchyMeanSquare n m U c j z‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc j z).1]
  exact (hierarchyMeanSquare_bounds n m U c hc j z).2

variable [MeasurableSpace S] [MeasurableSingletonClass S]
theorem hierarchyMeanSquare_joint_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    Integrable (fun sz => hierarchyMeanSquare n m U c j sz.2) (hierarchyGaussianLaw n m U) := by
  exact hierarchyGaussian_integrable n m U (fun _ => hierarchyMeanSquare n m U c j)
    (fun _ => HasExpGrowth.of_bounded (by norm_num) (hierarchyMeanSquare_norm_le_one n m U c hc j))
    (fun _ => hierarchyMeanSquare_continuous n m U c hc j)
end BoundedMeanObservable

section BlockTest
variable {D N k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem sharedFieldEnergy_meanSquare_test (hN : 0 < N) (j : Fin k) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    (∫ sz, sharedFieldEnergy D N k Δ j sz*hierarchyMeanSquare n m U c L sz.2
      ∂hierarchyGaussianLaw n m U) = -((k+1 : ℕ) : ℝ)⁻¹ *
        ∫ z, normalizedDot (fun i => hierarchySpinMean n m U (c i) J z)
          (fun i => hierarchySpinMean n m U (c i) L z)*hierarchyMeanSquare n m U c L z
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let J := blockLevel D N k j.castSucc
  let L := blockLevel D N k j.succ
  let M := hierarchyMeanSquare n m U c L
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hMc : Continuous M := hierarchyMeanSquare_continuous n m U c hc L
  have hMb : ∀ z, ‖M z‖ ≤ 1 := hierarchyMeanSquare_norm_le_one n m U c hc L
  have hMg : HasExpGrowth M := HasExpGrowth.of_bounded (by norm_num) hMb
  have hmreg (b : Fin (n+1)) (i : Fin N) := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) b
  have hA (i : Fin N) : Integrable
      (fun sz => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) sz.2*(c i sz.1*M sz.2))
      (hierarchyGaussianLaw n m U) := by
    apply hierarchyGaussian_integrable n m U (fun s z => coordinateLinear n (sharedFieldCoefficients D N k Δ j i) z*(c i s*M z))
    · intro s
      exact (HasExpGrowth.linear _).mul ((HasExpGrowth.const _).mul hMg)
    · intro s
      exact (coordinateLinear n _).continuous.mul (continuous_const.mul hMc)
  have hB (i : Fin N) : Integrable
      (fun z => (hierarchySpinMean n m U (c i) J z*hierarchySpinMean n m U (c i) L z)*M z)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
    apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
      (((hmreg J i).1.mul (hmreg L i).1).mul hMc) (C := 1) _ 0
    intro z
    simp only [Pi.mul_apply,norm_mul]
    have hp := mul_le_mul ((hmreg J i).2 z) ((hmreg L i).2 z) (norm_nonneg _) zero_le_one
    have hq := mul_le_mul hp (hMb z) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1*1)
    simpa only [one_mul] using hq
  have hId (i : Fin N) := blockMeanSquare_stein U Δ hΔ hU j i
  dsimp only at hId
  have H := integral_normalized_sum_identity _ _ (hierarchyAtom n m 1 J) hA hB hId
  have hAtom : hierarchyAtom n m 1 J = ((k+1 : ℕ) : ℝ)⁻¹ :=
    (hierarchyAtom_blockMass D N k J).trans (blockAtom_at D N k hN j.castSucc)
  rw [hAtom] at H
  simpa only [sharedFieldEnergy_expansion,normalizedDot,
    div_mul_eq_mul_div,Finset.sum_mul,mul_assoc] using H
end BlockTest
end SK.Analytic

namespace SK.Analytic
section Cauchy
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem abs_integral_mul_le_sqrt (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ z, f z*g z ∂μ| ≤ Real.sqrt (∫ z, (f z)^2 ∂μ)*Real.sqrt (∫ z, (g z)^2 ∂μ) := by
  have H := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num : (2 : ℝ).HolderConjugate 2) (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,← Real.sqrt_eq_rpow] at H
  calc
    |∫ z, f z*g z ∂μ| = ‖∫ z, f z*g z ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ‖f z*g z‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ z, |f z| * |g z| ∂μ := by simp only [norm_mul,Real.norm_eq_abs]
    _ ≤ _ := H

theorem abs_integral_mul_le_sqrt_of_bound [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ᵐ z ∂μ, |g z| ≤ 1) :
    |∫ z, f z*g z ∂μ| ≤ Real.sqrt (∫ z, (f z)^2 ∂μ) := by
  have hg₂ : MemLp g 2 μ := (memLp_const (1 : ℝ)).mono' hg hb
  have hsq : (∫ z, (g z)^2 ∂μ) ≤ 1 := by
    calc
      (∫ z, (g z)^2 ∂μ) ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hg₂.integrable_sq (integrable_const 1)
        filter_upwards [hb] with z hz
        nlinarith [abs_nonneg (g z),sq_abs (g z)]
      _ = 1 := by simp
  calc
    _ ≤ Real.sqrt (∫ z, (f z)^2 ∂μ)*Real.sqrt (∫ z, (g z)^2 ∂μ) :=
      abs_integral_mul_le_sqrt f g hf hg₂
    _ ≤ Real.sqrt (∫ z, (f z)^2 ∂μ)*1 :=
      mul_le_mul_of_nonneg_left (by simpa using Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)
    _ = _ := mul_one _

theorem centered_bounded_test [IsProbabilityMeasure μ]
    (Y B : Ω → ℝ) (hY : MemLp Y 2 μ) (hB : AEStronglyMeasurable B μ)
    (hb : ∀ᵐ z ∂μ, |B z| ≤ 1) :
    |(∫ z, Y z*B z ∂μ)-(∫ z, Y z ∂μ)*(∫ z, B z ∂μ)| ≤
      Real.sqrt ((∫ z, (Y z)^2 ∂μ)-(∫ z, Y z ∂μ)^2) := by
  have hB₂ : MemLp B 2 μ := (memLp_const (1 : ℝ)).mono' hB hb
  have hB₁ := hB₂.integrable (by norm_num)
  have hc := hY.sub (memLp_const (∫ z, Y z ∂μ))
  have H := abs_integral_mul_le_sqrt_of_bound (μ := μ)
    (fun z => Y z-∫ z, Y z ∂μ) B hc hB hb
  have hl : (∫ z, (Y z-∫ z, Y z ∂μ)*B z ∂μ) =
      (∫ z, Y z*B z ∂μ)-(∫ z, Y z ∂μ)*(∫ z, B z ∂μ) := by
    simp_rw [sub_mul]
    rw [integral_sub (f := fun z => Y z*B z) (g := fun z => (∫ z, Y z ∂μ)*B z)
      (hY.integrable_mul hB₂) (hB₁.const_mul _),integral_const_mul]
  rw [hl] at H
  have hr : (∫ z, (Y z-∫ z, Y z ∂μ)^2 ∂μ) =
      (∫ z, (Y z)^2 ∂μ)-(∫ z, Y z ∂μ)^2 := by
    rw [← variance_eq_integral hY.aemeasurable]
    exact variance_eq_sub hY
  rwa [hr] at H
end Cauchy
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section JointBlockLp
variable {D N k : ℕ}
theorem sharedFieldEnergy_memLp_two
    (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
    (Δ : Fin (k+1) → ℝ) (j : Fin k) :
    MemLp (sharedFieldEnergy D N k Δ j) 2
      (hierarchyGaussianLaw (blockDimension D N k) (blockMass D N k) U) := by
  let w := sharedBlockWeights k Δ j
  let I : Fin D → Finset (Fin N) := fun _ => ∅
  have he : sharedFieldEnergy D N k Δ j = fun sz =>
      blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ)) sz.1 sz.2 :=
    funext (blockFieldEnergy_exponent I w)
  rw [he]
  let L : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ :=
    blockExponent I (fun _ => 0) (fun b => w b/(N : ℝ))
  have hg (s : Config N) : HasExpGrowth (fun z => L s z) := HasExpGrowth.linear (L s)
  have hc (s : Config N) : Continuous (fun z => L s z) := (L s).continuous
  exact hierarchyGaussian_memLp_two (blockDimension D N k) (blockMass D N k) U (fun s z => L s z) hg hc
end JointBlockLp

section CenteredBlockTest
variable {D N k : ℕ}
variable (U : Config N → ParameterSpace (blockDimension D N k) →L[ℝ] ℝ)
  (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b)
  (hU : ∀ b i s, U s (coordinateAxis (blockDimension D N k) (fieldIndex D N k b i)) =
      Real.sqrt (Δ b)*spin (s i))

include hΔ hU

theorem sharedFieldEnergy_centered_test (hN : 0 < N) (j : Fin k) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    |(∫ z, normalizedDot (fun i => hierarchySpinMean n m U (c i) J z)
          (fun i => hierarchySpinMean n m U (c i) L z)*hierarchyMeanSquare n m U c L z
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)-
      hierarchyMeanOverlap n m U c J * hierarchyMeanOverlap n m U c L| ≤
      ((k+1 : ℕ) : ℝ)*Real.sqrt (ProbabilityTheory.variance (sharedFieldEnergy D N k Δ j)
        (hierarchyGaussianLaw n m U)) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let L := blockLevel D N k j.succ
  let μ := hierarchyGaussianLaw n m U
  let M := hierarchyMeanSquare n m U c L
  let := hierarchyGaussian_probability n m U
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hMb : ∀ z, ‖M z‖ ≤ 1 := hierarchyMeanSquare_norm_le_one n m U c hc L
  have hY := sharedFieldEnergy_memLp_two U Δ j
  have hM := hierarchyMeanSquare_joint_integrable n m U c hc L
  have H := centered_bounded_test (μ := μ) (sharedFieldEnergy D N k Δ j) (fun sz => M sz.2)
    hY hM.aestronglyMeasurable (by filter_upwards [] with sz; exact hMb sz.2)
  have hp : (∫ sz, M sz.2 ∂μ) = hierarchyMeanOverlap n m U c L :=
    hierarchyGaussian_path_marginal n m U M (hierarchyMeanSquare_continuous n m U c hc L)
      (HasExpGrowth.of_bounded (by norm_num) hMb)
  have hv := variance_eq_sub hY
  dsimp only [Pi.pow_apply] at hv
  rw [← hv] at H
  rw [hp] at H
  have hmean := sharedFieldEnergy_mean U Δ hΔ hU hN j
  have htest := sharedFieldEnergy_meanSquare_test U Δ hΔ hU hN j
  dsimp only at htest
  rw [hmean,htest] at H
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  have hK : 0 < K := by dsimp only [K]; positivity
  have he (I r s : ℝ) : -K⁻¹*I-(-K⁻¹*r)*s = -K⁻¹*(I-r*s) := by ring
  rw [he,abs_mul,abs_neg,abs_inv,abs_of_pos hK] at H
  have H' := mul_le_mul_of_nonneg_left H hK.le
  rw [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] at H'
  exact H'
end CenteredBlockTest
end SK.Analytic
namespace SK.Analytic
section SqrtIntegral
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_sqrt_le_sqrt_integral (d : Ω → ℝ) (hd : Integrable d μ) (hpos : ∀ z, 0 ≤ d z) :
    (∫ z, Real.sqrt (d z) ∂μ) ≤ Real.sqrt (∫ z, d z ∂μ) := by
  have hsm : AEStronglyMeasurable (fun z => Real.sqrt (d z)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hd.aestronglyMeasurable
  have hsq : (fun z => (Real.sqrt (d z))^2) = d := funext (fun z => Real.sq_sqrt (hpos z))
  have h₂ : MemLp (fun z => Real.sqrt (d z)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsm,hsq]
    exact hd
  have H := abs_integral_mul_le_sqrt_of_bound (μ := μ) (fun z => Real.sqrt (d z)) (fun _ => 1)
    h₂ aestronglyMeasurable_const (by filter_upwards [] with z; norm_num)
  simp only [mul_one] at H
  rw [hsq] at H
  exact (le_abs_self _).trans H
end SqrtIntegral

section MeanVariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem normalizedSquare_le_const {N : ℕ} (a : Fin N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) : normalizedSquare a ≤ C^2 := by
  by_cases hN : N=0
  · simp [normalizedSquare,hN,sq_nonneg C]
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  apply (div_le_iff₀ hn).2
  calc
    (∑ i, (a i)^2) ≤ ∑ _ : Fin N, C^2 := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [ha i,sq_abs (a i),abs_nonneg (a i)]
    _ = C^2*(N : ℝ) := by simp [mul_comm]

theorem normalizedSquare_measurable {N : ℕ} (a : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) : Measurable (fun z => normalizedSquare (a z)) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => (ha i).pow_const 2)

theorem normalizedDot_measurable {N : ℕ} (a b : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (hb : ∀ i, Measurable (fun z => b z i)) :
    Measurable (fun z => normalizedDot (a z) (b z)) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => (ha i).mul (hb i))

theorem normalizedSquare_memLp {N : ℕ} (a : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ z i, |a z i| ≤ C) :
    MemLp (fun z => normalizedSquare (a z)) 2 μ := by
  apply (memLp_const (C^2)).mono' (normalizedSquare_measurable a ha).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (normalizedSquare_nonneg _)]
  exact normalizedSquare_le_const (a z) C hC (hb z)

theorem abs_normalizedDot_le_one {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) : |normalizedDot a b| ≤ 1 := by
  have h₁ : Real.sqrt (normalizedSquare a) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one a ha)
  have h₂ : Real.sqrt (normalizedSquare b) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one b hb)
  exact (abs_normalizedDot_le a b).trans (by nlinarith [Real.sqrt_nonneg (normalizedSquare a),Real.sqrt_nonneg (normalizedSquare b)])

theorem mean_variance_from_test {N : ℕ} (a b : Ω → Fin N → ℝ)
    (ha : ∀ i, Measurable (fun z => a z i)) (hb : ∀ i, Measurable (fun z => b z i))
    (ha₁ : ∀ z i, |a z i| ≤ 1) (hb₁ : ∀ z i, |b z i| ≤ 1) :
    let M := fun z => normalizedSquare (a z)
    let T := fun z => normalizedSquare (b z)
    let r := ∫ z, M z ∂μ
    ProbabilityTheory.variance M μ ≤
      |(∫ z, normalizedDot (a z) (b z)*T z ∂μ)-r*(∫ z, T z ∂μ)|+
        3*Real.sqrt (∫ z, normalizedSquare (fun i => b z i-a z i) ∂μ) := by
  let M := fun z => normalizedSquare (a z)
  let T := fun z => normalizedSquare (b z)
  let Q := fun z => normalizedDot (a z) (b z)
  let d := fun z => normalizedSquare (fun i => b z i-a z i)
  let r := ∫ z, M z ∂μ
  have hM : MemLp M 2 μ := normalizedSquare_memLp a ha 1 (by norm_num) ha₁
  have hT : MemLp T 2 μ := normalizedSquare_memLp b hb 1 (by norm_num) hb₁
  have hQ : MemLp Q 2 μ := by
    apply (memLp_const (1 : ℝ)).mono' (normalizedDot_measurable a b ha hb).aestronglyMeasurable
    filter_upwards [] with z
    exact abs_normalizedDot_le_one (a z) (b z) (ha₁ z) (hb₁ z)
  have hd : Integrable d μ := by
    apply (normalizedSquare_memLp (fun z i => b z i-a z i)
      (fun i => (hb i).sub (ha i)) 2 (by norm_num) ?_).integrable (by norm_num)
    intro z i
    exact (abs_sub (b z i) (a z i)).trans (by linarith [ha₁ z i,hb₁ z i])
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨integral_nonneg (fun z => normalizedSquare_nonneg _),?_⟩
    calc
      r ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := integral_mono (hM.integrable (by norm_num)) (integrable_const 1)
        (fun z => normalizedSquare_le_one _ (ha₁ z))
      _ = 1 := by simp
  let F := fun z => (Q z-r)*T z
  let G := fun z => (M z-r)*M z
  have hF : Integrable F μ := (hQ.sub (memLp_const r)).integrable_mul hT
  have hG : Integrable G μ := (hM.sub (memLp_const r)).integrable_mul hM
  have hFid : (∫ z, F z ∂μ) = (∫ z, Q z*T z ∂μ)-r*(∫ z, T z ∂μ) := by
    simp only [F,sub_mul]
    rw [integral_sub (f := fun z => Q z*T z) (g := fun z => r*T z) (hQ.integrable_mul hT) ((hT.integrable (by norm_num)).const_mul r),integral_const_mul]
  have hGid : (∫ z, G z ∂μ) = ProbabilityTheory.variance M μ := by
    simp only [G,sub_mul]
    rw [integral_sub (f := fun z => M z*M z) (g := fun z => r*M z) (hM.integrable_mul hM) ((hM.integrable (by norm_num)).const_mul r),integral_const_mul]
    rw [variance_eq_sub hM]
    simp only [pow_two,Pi.mul_apply,r]
  have hsqrt : Integrable (fun z => Real.sqrt (d z)) μ := by
    have hm : AEStronglyMeasurable (fun z => Real.sqrt (d z)) μ := Real.continuous_sqrt.comp_aestronglyMeasurable hd.aestronglyMeasurable
    have h₂ : MemLp (fun z => Real.sqrt (d z)) 2 μ := by
      rw [memLp_two_iff_integrable_sq hm]
      have he : (fun z => (Real.sqrt (d z))^2) = d := by
        funext z
        exact Real.sq_sqrt (normalizedSquare_nonneg _)
      rw [he]
      exact hd
    exact h₂.integrable (by norm_num)
  have Herr : |(∫ z, F z ∂μ)-(∫ z, G z ∂μ)| ≤ 3*Real.sqrt (∫ z, d z ∂μ) := by
    rw [← integral_sub hF hG]
    calc
      _ ≤ ∫ z, |F z-G z| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => F z-G z)
      _ ≤ ∫ z, 3*Real.sqrt (d z) ∂μ := integral_mono (hF.sub hG).norm (hsqrt.const_mul 3)
        (fun z => mean_variance_replacement (a z) (b z) r (ha₁ z) (hb₁ z) hr)
      _ = 3*(∫ z, Real.sqrt (d z) ∂μ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_sqrt_le_sqrt_integral d hd (fun z => normalizedSquare_nonneg _)) (by norm_num)
  rw [hFid,hGid] at Herr
  have H := (abs_le.mp Herr).1
  dsimp only
  change ProbabilityTheory.variance M μ ≤ |(∫ z, Q z*T z ∂μ)-r*(∫ z, T z ∂μ)|+3*Real.sqrt (∫ z, d z ∂μ)
  linarith [le_abs_self ((∫ z, Q z*T z ∂μ)-r*(∫ z, T z ∂μ))]
end MeanVariance
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockMeanSquare_variance {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) (hΔ : ∀ b, 0 < Δ b) (j : Fin k) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    let J := blockLevel D N k j.castSucc
    let L := blockLevel D N k j.succ
    ProbabilityTheory.variance (hierarchyMeanSquare n m U c J)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) ≤
      ((k+1 : ℕ) : ℝ)*Real.sqrt (((Δ j.castSucc)⁻¹+(Δ j.succ)⁻¹)/(N : ℝ))+
        3*Real.sqrt (hierarchyMeanOverlap n m U c L-hierarchyMeanOverlap n m U c J) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let U := blockExponent I a (fun b => Real.sqrt (Δ b))
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let J := blockLevel D N k j.castSucc
  let L := blockLevel D N k j.succ
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by dsimp only [c]; cases s i <;> norm_num [spin]
  have hr (b : Fin (n+1)) (i : Fin N) := hierarchySpinMean_regular n m U (c i) (by norm_num) (hc i) b
  have H := mean_variance_from_test (μ := μ)
    (fun z i => hierarchySpinMean n m U (c i) J z)
    (fun z i => hierarchySpinMean n m U (c i) L z)
    (fun i => (hr J i).1.measurable) (fun i => (hr L i).1.measurable)
    (fun z i => (hr J i).2 z) (fun z i => (hr L i).2 z)
  dsimp only at H
  have hJL : J ≤ L := blockLevel_mono D N k (show j.castSucc ≤ j.succ from Nat.le_succ _)
  have hinc := hierarchyMean_increment_identity n m U c hc J L hJL
  rw [hinc] at H
  have ht := sharedFieldEnergy_centered_test U Δ hΔ
    (blockExponent_field I a (fun b => Real.sqrt (Δ b))) hN j
  dsimp only at ht
  have hvar := sharedFieldEnergy_variance I a Δ hΔ j
  have hK : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  exact H.trans (add_le_add (ht.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) hK)) le_rfl)
end SK.Analytic

namespace SK.Analytic

theorem sum_sqrt_increments_le {k : ℕ} (r : Fin (k+1) → ℝ)
    (hr : Monotone r) (hr0 : 0 ≤ r 0) (hr1 : r (Fin.last k) ≤ 1) :
    (∑ j : Fin k, Real.sqrt (r j.succ-r j.castSucc)) ≤ Real.sqrt (k : ℝ) := by
  have hnon (j : Fin k) : 0 ≤ r j.succ-r j.castSucc := sub_nonneg.mpr (hr (Nat.le_succ _))
  have ht : (∑ j : Fin k, (r j.succ-r j.castSucc)) = r (Fin.last k)-r 0 := by
    rw [Finset.sum_sub_distrib]
    have H := Fin.sum_univ_succ r
    have G := Fin.sum_univ_castSucc r
    linarith
  have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin k => Real.sqrt (r j.succ-r j.castSucc)) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
  simp_rw [Real.sq_sqrt (hnon _)] at H
  rw [ht] at H
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have H' : (∑ j : Fin k, Real.sqrt (r j.succ-r j.castSucc))^2 ≤ (k : ℝ) := by nlinarith
  exact (Real.le_sqrt (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)) hk).mpr H'
end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockMeanSquare_average_variance {D N k : ℕ} (hN : 0 < N)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (Δ : Fin (k+1) → ℝ) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ b, δ ≤ Δ b) :
    let n := blockDimension D N k
    let m := blockMass D N k
    let U := blockExponent I a (fun b => Real.sqrt (Δ b))
    let c : Fin N → Config N → ℝ := fun i s => spin (s i)
    (∑ j : Fin k, ((k+1 : ℕ) : ℝ)⁻¹ *
      ProbabilityTheory.variance (hierarchyMeanSquare n m U c (blockLevel D N k j.castSucc))
        (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)) ≤
      (k : ℝ)*Real.sqrt (2/((N : ℝ)*δ)) + 3*Real.sqrt (k : ℝ)/((k+1 : ℕ) : ℝ) := by
  let n := blockDimension D N k
  let m := blockMass D N k
  let U := blockExponent I a (fun b => Real.sqrt (Δ b))
  let c : Fin N → Config N → ℝ := fun i s => spin (s i)
  let r : Fin (k+1) → ℝ := fun j => hierarchyMeanOverlap n m U c (blockLevel D N k j)
  have hc (i : Fin N) (s : Config N) : ‖c i s‖ ≤ 1 := by
    dsimp only [c]; cases s i <;> norm_num [spin]
  have hm : Monotone r := fun i j hij => hierarchyMeanOverlap_mono n m U c hc (blockLevel_mono D N k hij)
  have hr0 : 0 ≤ r 0 := (hierarchyMeanOverlap_bounds n m U c hc _).1
  have hr1 : r (Fin.last k) ≤ 1 := (hierarchyMeanOverlap_bounds n m U c hc _).2
  have hsum := sum_sqrt_increments_le r hm hr0 hr1
  have hpos (b) : 0 < Δ b := hδ.trans_le (hΔ b)
  have hN' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hK : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  let K : ℝ := ((k+1 : ℕ) : ℝ)
  have hbound (j : Fin k) : ((Δ j.castSucc)⁻¹+(Δ j.succ)⁻¹)/(N : ℝ) ≤ 2/((N : ℝ)*δ) := by
    calc
      _ ≤ (δ⁻¹+δ⁻¹)/(N : ℝ) := div_le_div_of_nonneg_right
        (add_le_add (inv_anti₀ hδ (hΔ _)) (inv_anti₀ hδ (hΔ _))) hN'.le
      _ = _ := by field_simp; ring
  have H := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ =>
    mul_le_mul_of_nonneg_left
      ((blockMeanSquare_variance hN I a Δ hpos j).trans
        (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hbound j)) hK.le) le_rfl))
      (inv_nonneg.mpr hK.le))
  change (∑ j : Fin k, K⁻¹ * _ ) ≤ _
  apply H.trans
  change (∑ j : Fin k, K⁻¹*(K*Real.sqrt (2/((N : ℝ)*δ)) + 3*Real.sqrt (r j.succ-r j.castSucc))) ≤ _
  have he (t s : ℝ) : K⁻¹*(K*t+3*s) = t+(K⁻¹*3)*s := by
    rw [mul_add,← mul_assoc,inv_mul_cancel₀ (show K ≠ 0 from hK.ne'),one_mul]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,← Finset.mul_sum]
  have hs := mul_le_mul_of_nonneg_left hsum (show 0 ≤ K⁻¹*3 by positivity)
  dsimp only [K] at hs ⊢
  simp only [div_eq_mul_inv]
  nlinarith
end SK.Analytic

end
end

end

end OAI
