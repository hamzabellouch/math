import OAI.Combinatorics.ContingencyTables.Transport.BalancedBox

namespace OAI

/-! # Balanced marginal closure at capacities zero and one

Capacity one has two old quadratic blocks with a common mixed
functional. Each fresh coordinate is isotropic. This proves closure
directly on the raw integer forms, including the small cells that must
be eliminated to obtain an actual tree-coordinate marginal.
-/

namespace ContingencyTables

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)

theorem isotropic_kernel_nonpositive
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : BilinForm ℝ V) (hsymm : ∀ x y, B x y=B y x)
    (hsig : OnePositiveDirection B) (e w : V)
    (hee : B e e=0) (hew : B e w≠0)
    (v : V) (hev : B e v=0) : B v v ≤ 0 := by
  by_contra hn
  have hv : 0 < B v v := lt_of_not_ge hn
  let u := w-(B v w/B v v) • v
  have hvu : B v u=0 := by
    simp only [u,LinearMap.BilinForm.sub_right,LinearMap.BilinForm.smul_right]
    field_simp [hv.ne']
    ring
  have heu : B e u=B e w := by
    simp only [u,LinearMap.BilinForm.sub_right,LinearMap.BilinForm.smul_right,hev,
      mul_zero,sub_zero]
  have hue : B u e=B e w := by rw [hsymm,heu]
  have hve : B v e=0 := by rw [hsymm,hev]
  let t := (1-B u u)/(2*B e w)
  have horth : B v (u+t • e)=0 := by
    simp only [LinearMap.BilinForm.add_right,LinearMap.BilinForm.smul_right,hvu,hve,
      mul_zero,add_zero]
  have hsquare : B (u+t • e) (u+t • e)=1 := by
    simp only [LinearMap.BilinForm.add_left,LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left,LinearMap.BilinForm.smul_right,hee,heu,hue,mul_zero,add_zero]
    dsimp only [t]
    field_simp [hew]
    ring
  have hh := hsig v hv (u+t • e) horth
  rw [hsquare] at hh
  norm_num at hh

namespace IntegerMarginal

open CommonBasesFPRAS FactorialSignatures BalancedBox

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem marginal_zero_removal_slice (F : ((I⊕Bool) → ℕ) → ℝ)
    (m : I → ℕ) (R : ℕ)
    (hsig : RemovalSlice F (profile m 0 0) R) :
    RemovalSlice (marginal F 0) m R := by
  intro z hz ht
  have hs := hsig (profile z 0 0)
    (profile_inBox m z 0 0 0 hz le_rfl le_rfl)
    (by simp only [profile_total,ht,add_zero])
  rw [marginal_old_block]
  simp only [Nat.zero_add,Finset.sum_range_one]
  intro u hu v huv
  exact hs (old u) hu (old v) huv

lemma removeOne_total (z : I → ℕ) (i : I) (hi : 0 < z i) :
    (∑ u,removeOne z i u)+1=∑ u,z u := by
  have he : ∀ u,removeOne z i u+(if u=i then 1 else 0)=z u := by
    intro u
    by_cases hu : u=i
    · subst u
      simp only [removeOne,ite_true]
      omega
    · simp [removeOne,hu]
  have hh := congrArg (fun f : I → ℕ => ∑ u,f u) (funext he)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

theorem marginal_one_removal_slice (F : ((I⊕Bool) → ℕ) → ℝ)
    (m : I → ℕ) (R : ℕ)
    (hpos : PositiveSlice F (profile m 1 1) (R+1))
    (hsig : RemovalSlice F (profile m 1 1) (R+1)) :
    RemovalSlice (marginal F 1) m R := by
  intro z hz ht
  have hex : ∃ i,0 < z i := by
    by_contra hn
    push Not at hn
    have hz0 : ∀ i,z i=0 := fun i => Nat.eq_zero_of_le_zero (hn i)
    simp only [hz0,Finset.sum_const_zero] at ht
    omega
  obtain ⟨i,hi⟩ := hex
  let B (j : ℕ) := (pairMatrix F 1 z j).toBilin'
  let ell : (I → ℝ) →ₗ[ℝ] ℝ := cross F 1 z 1
  have hsigB (j : ℕ) (hj : j ≤ 1) : OnePositiveDirection (B j) := by
    apply hsig _ (profile_inBox m z 1 j (1-j) hz hj (Nat.sub_le _ _))
    rw [profile_total,ht]
    omega
  have he0 : B 0 (Pi.single (.inr true) 1) (Pi.single (.inr true) 1)=0 := by
    simp [B,Matrix.toBilin'_apply,pairMatrix_bb,innerWeight]
  have he1 : B 1 (Pi.single (.inr false) 1) (Pi.single (.inr false) 1)=0 := by
    simp [B,Matrix.toBilin'_apply,pairMatrix_aa,innerWeight]
  have hcross0 (v : I → ℝ) : B 0 (old v) (Pi.single (.inr true) 1)=ell v :=
    cross_b F 1 z 0 (by omega) v
  have hcross1 (v : I → ℝ) : B 1 (old v) (Pi.single (.inr false) 1)=ell v :=
    cross_a F 1 z 1 le_rfl v
  have hpositive : 0 < F (profile (removeOne z i) 0 0) := by
    apply hpos _ (profile_inBox m (removeOne z i) 1 0 0
      (fun u => (Nat.sub_le _ _).trans (hz u)) (by omega) (by omega))
    have hh := removeOne_total z i hi
    rw [profile_total]
    omega
  have hell : ell (Pi.single i 1)≠0 := by
    have hv : ValidPair (profile z 1 0) (.inl i) (.inr false) := by
      simp [ValidPair,profile,hi]
    have he : ell (Pi.single i 1)=F (profile (removeOne z i) 0 0) := by
      dsimp only [ell]
      rw [← cross_a F 1 z 1 le_rfl,old_single]
      simp only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [pairMatrix,integerRemovalMatrix,ite_eq_left hv,profile_removeOldA]
    rw [he]
    exact hpositive.ne'
  have hker (v : I → ℝ) (hv : ell v=0) : B 0 (old v) (old v)+B 1 (old v) (old v) ≤ 0 := by
    have hs0 : ∀ x y,B 0 x y=B 0 y x :=
      fun x y => (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
    have hs1 : ∀ x y,B 1 x y=B 1 y x :=
      fun x y => (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
    have hh0 := isotropic_kernel_nonpositive (B 0) hs0 (hsigB 0 (by omega))
      (Pi.single (.inr true) 1) (old (Pi.single i 1)) he0
      (by rw [hs0,hcross0]; exact hell) (old v) (by rw [hs0,hcross0,hv])
    have hh1 := isotropic_kernel_nonpositive (B 1) hs1 (hsigB 1 le_rfl)
      (Pi.single (.inr false) 1) (old (Pi.single i 1)) he1
      (by rw [hs1,hcross1]; exact hell) (old v) (by rw [hs1,hcross1,hv])
    linarith
  apply onePositiveDirection_of_kernel _
    (fun x y => (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y) ell
  intro v hv
  have hh := hker v hv
  rw [marginal_old_block]
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    LinearMap.add_apply,LinearMap.compl₁₂_apply,B] using hh

end IntegerMarginal
end ContingencyTables

end OAI
