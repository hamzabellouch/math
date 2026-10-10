import OAI.NumberTheory.DirichletL.Moments.FirstAllocationGaussEnergy
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import OAI.NumberTheory.DirichletL.Moments.AllocationCost

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocationControlDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma frozen_live_control (B : Tuple ι) (M : ι→ℝ) :
    frozenControl B M * (∏i : liveIndices B,M i.val) = ∏i,M i := by
  rw [Finset.prod_coe_sort (liveIndices B) M]
  unfold frozenControl liveIndices
  rw [mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=>B (Sum.inl i)=1) M

lemma frozen_child_control (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t : ℝ) :
    (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2 = (∏i,s.M i)^2 := by
  rw [←mul_pow]
  exact congrArg (fun x:ℝ=>x^2) (frozen_live_control B.val s.M)

lemma allocated_control_sum (s : Input ι) (C R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) :
    (∑B : actualAllocations s.pools C,
      (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) =
      ((actualAllocations s.pools C).card:ℝ) * (∏i,s.M i)^2 := by
  simp only [frozen_child_control,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    nsmul_eq_mul]

theorem allocated_control_mass (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{κ : Type*}[Fintype κ],Fintype.card κ≤N →
      ∀(s : Input κ)(C R : Ideal O),C≠0 →
      ∀(τ : HeckeFamily.Character)(t : ℝ),
        ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          (∑B : actualAllocations s.pools C,
            (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) ≤
          D*(Ideal.absNorm C:ℝ)^(ε-1)*(∏i,s.M i)^2 := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro κ _ hn s C R hC τ t
  have hN : (0:ℝ)<Ideal.absNorm C := CenteredMomentFirstScale.norm_pos C hC
  have hh := hcard (ι:=κ⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega)
    s.pools C hC
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hh 2
  rw [mul_pow,←Real.rpow_mul_natCast hN.le,show ε/2*(2:ℕ)=ε by norm_num] at hs
  rw [allocated_control_sum]
  calc
    _ = (((actualAllocations s.pools C).card:ℝ)^2/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 := by ring
    _ ≤ (D^2*(Ideal.absNorm C:ℝ)^ε/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hN.le) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub hN,Real.rpow_one];ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
