import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.LinearEvenMoment
import OAI.Probability.BinarySweep.GridBounds.BoardOverlap

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

lemma prod_pos_log_exp {I : Type*} [Fintype I] (d : I → ℝ) (hd : ∀i, 0<d i) :
    (∏i, d i)=Real.exp (∑i, Real.log (d i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (hd i)).symm

lemma natShift_pow_exp (n t : ℕ) :
    (n+1:ℝ)^t=Real.exp ((t:ℝ)*Real.log (n+1:ℝ)) := by
  rw [Real.exp_nat_mul,Real.exp_log (by positivity)]

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

theorem grouped_projected_exp_bound (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) [∀i, (ρ i).IsIrreducible]
    (hρ : ∀i a v, ‖ρ i a v‖=‖v‖) (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ)
    {q : ℕ} (hq : 0<q) (B : I → ℝ)
    (hB : ∀i, evenMoment q (groupAverage (ρ i) (w i))≤Real.exp (B i)) :
    matrixMoment q (groupedProjection e g p ρ*groupedAverage e g p w) ≤
      Real.exp (∑i, ((((Fintype.card A)^2:ℕ):ℝ)*Real.log (n i+1:ℝ)+B i)) := by
  refine (grouped_projected_moment_le e g p ρ hρ w hq).trans ?_
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i _; exact mul_nonneg (by positivity) (evenMoment_nonneg _ _)
  · intro i _
    rw [Real.exp_add,←natShift_pow_exp]
    exact mul_le_mul_of_nonneg_left (hB i) (by positivity)

omit [∀ i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_overlap_contract
    {J W : Type*} [Fintype J] [LinearOrder J]
    {m : J → ℕ} {U : J → Type*} [∀j,NormedAddCommGroup (U j)]
    [∀j,InnerProductSpace ℂ (U j)] [∀j,FiniteDimensional ℂ (U j)]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) W)
    (α : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (β : ∀j, Representation ℂ (Equiv.Perm (Fin (m j))) (U j)) :
    ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖≤1 := by
  have hP : ‖isotypicProjection p ρ‖≤1 := IsStarProjection.norm_le _
    ⟨projectionMatrix_idempotent _,(isotypicProjection_psd p ρ).isHermitian⟩
  calc
    _ ≤ (‖groupedProjection eC gC p β‖*‖isotypicProjection p ρ‖)*‖groupedProjection eR gR p α‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*1)*1 := mul_le_mul
      (mul_le_mul (groupedProjection_norm_le eC gC p β) hP (norm_nonneg _) zero_le_one)
      (groupedProjection_norm_le eR gR p α) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

lemma prod_dimension_shift {K : Type*} [Fintype K] (d : K → ℝ) (hd : ∀i, 0<d i)
    (n : K → ℕ) (t : ℕ) :
    (∏i, d i*(n i+1:ℝ)^t)=
      Real.exp ((∑i, Real.log (d i))+(t:ℝ)*(∑i, Real.log (n i+1:ℝ))) := by
  rw [Finset.prod_mul_distrib,prod_pos_log_exp d hd,Real.exp_add,Finset.mul_sum,Real.exp_sum]
  congr 1
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact natShift_pow_exp (n i) t

lemma grouped_density_card_exp [Nonempty A] (p : A → Bool) :
    (Fintype.card (∀i, LocalDensityIndex p (n i)):ℝ) ≤
      Real.exp ((2*(Fintype.card A)^2:ℕ)*(∑i, Real.log (n i+1:ℝ))) := by
  have hc : (Fintype.card (∀i, LocalDensityIndex p (n i)):ℝ) ≤
      ∏i, (n i+1:ℝ)^(2*(Fintype.card A)^2) := by
    exact_mod_cast grouped_density_card_bound (n:=n) p
  refine hc.trans_eq ?_
  rw [Finset.mul_sum,Real.exp_sum]
  exact Finset.prod_congr rfl (fun i _ => natShift_pow_exp (n i) _)

lemma irreducible_finrank_pos {G W : Type*} [Group G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] : 0<Module.finrank ℂ W := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  rw [← ρ.asModuleEquiv.finrank_eq]
  exact Module.finrank_pos

theorem actual_board_overlap_exp
    [Nonempty A] [Nonempty I]
    {J W : Type*} [Fintype J] [LinearOrder J]
    {m : J → ℕ} {U : J → Type*} [∀j,NormedAddCommGroup (U j)]
    [∀j,InnerProductSpace ℂ (U j)] [∀j,FiniteDimensional ℂ (U j)]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (board : Fin N ↪ I × J) (p : A → Bool)
    (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N))
    (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) W) [ρ.IsIrreducible]
    (α : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) [∀i, (α i).IsIrreducible]
    (β : ∀j, Representation ℂ (Equiv.Perm (Fin (m j))) (U j)) [∀j, (β j).IsIrreducible] :
    ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖^2 ≤
      Real.exp ((∑i, Real.log (Module.finrank ℂ (V i):ℝ))+
        (∑j, Real.log (Module.finrank ℂ (U j):ℝ))-Real.log (Module.finrank ℂ W:ℝ)+
        (Fintype.card I*Fintype.card J-(N:ℝ))+
        4*(Fintype.card A:ℝ)^2*((∑i, Real.log (n i+1:ℝ))+(∑j, Real.log (m j+1:ℝ)))) := by
  have hd : 0<(Module.finrank ℂ W:ℝ) := by exact_mod_cast irreducible_finrank_pos ρ
  have hdR (i : I) : 0<(Module.finrank ℂ (V i):ℝ) := by exact_mod_cast irreducible_finrank_pos (α i)
  have hdC (j : J) : 0<(Module.finrank ℂ (U j):ℝ) := by exact_mod_cast irreducible_finrank_pos (β j)
  have hb := actual_board_overlap board p eR eC gR gC hR hC ρ α β
  rw [prod_dimension_shift _ hdR,prod_dimension_shift _ hdC] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul ((mul_le_mul_of_nonneg_left (grouped_density_card_exp (n:=n) p)
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)))
      (grouped_density_card_exp (n:=m) p) (by positivity)
      (by positivity)) (Real.exp_pos _).le)
  apply (mul_le_mul_iff_right₀ hd).mp
  refine hb'.trans_eq ?_
  rw [←Real.exp_log hd]
  simp only [←Real.exp_add,Real.log_exp]
  congr 1
  push_cast
  ring

end BinaryCoordinateSweeps.Signed

end

end OAI
